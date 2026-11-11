import S1Angle
import S1ChordAngle
import S2Cap
import S2Cell
import S2CellId
import S2Edge
import S2LatLng
import S2LatLngRect
import S2Loop
import Internal/S2Boundary
import S2Point
import Internal/S2Coder
import S2PointCompression

## A region bounded by loops, holes included.
##
## The loops are nested rather than oriented: a point is inside the polygon
## when an odd number of loops contain it, so a disc with a hole punched out of
## it is two counterclockwise loops, one inside the other. Each loop's depth
## records where it sits in that nesting, and its parity says what the loop
## bounds: an even depth is a shell, an odd depth a hole.
##
## `from_loops` takes loops in that nested form, each with its interior on
## its left. `from_oriented_loops` takes them the way GeoJSON and upstream's
## oriented convention write them, with the polygon's interior on the left of
## every loop, so that a hole runs clockwise.
##
##     shell = S2Loop.from_lat_lngs(outer)
##     hole = S2Loop.from_lat_lngs(inner)
##     polygon = S2Polygon.from_loops([shell, hole])
##     polygon.contains_polygon(other)
##
## A polygon is a region, so `S2RegionCoverer` covers it like any other.
##
## This port has no spatial index. Containment between two polygons costs the
## product of their vertex counts, and `is_valid` the square of the total
## vertex count. That is fine for the polygon sizes a containment test
## usually sees and slow for very large ones.
S2Polygon := { loops : List(Nested), bound : S2LatLngRect, inconsistent_orientations : Bool }.{

	## One loop, and how deeply it is nested inside the others.
	Nested : { boundary : S2Loop, depth : U64 }

	## The polygon whose interior is the points that an odd number of the
	## loops contain.
	##
	## The loops must be nested: no two of them cross or share an edge, and
	## no two of them together cover the whole sphere. Each loop is used as it
	## is, so each one's interior is on its left, and a hole runs in the same
	## direction as its shell. When the direction of the input is not known,
	## `normalized` on each loop gives loops that nest, or use
	## `from_oriented_loops`. The loops may come in any order. This is
	## upstream's `InitNested`, which also drops empty loops.
	##
	## The nesting is found with `S2Loop.contains_nested`, which assumes
	## nested input. `is_valid` checks it.
	from_loops : List(S2Loop) -> S2Polygon
	from_loops = |loops| {
		kept = loops.keep_if(|boundary| !boundary.is_empty())
		nested = nest(kept).map(
			|(index, depth)| { boundary: kept.get(index) ?? S2Loop.empty(), depth: depth },
		)
		assemble(nested, Bool.False)
	}

	## The polygon whose interior is on the left of every loop.
	##
	## This is the oriented convention of GeoJSON and of upstream's
	## `InitOriented`: a shell runs counterclockwise and a hole inside it runs
	## clockwise. The loops must not cross or share an edge, and may come in
	## any order. Each hole is inverted, so the polygon's loops all bound
	## their own interiors as `from_loops` expects. Empty loops are dropped.
	##
	## When the orientations do not agree, for example two nested loops that
	## both run counterclockwise, no polygon has its interior on the left of
	## both. The polygon is then still built, but `is_valid` is false and
	## `find_validation_error` gives `InconsistentOrientations`.
	from_oriented_loops : List(S2Loop) -> S2Polygon
	from_oriented_loops = |loops| orient(loops.keep_if(|boundary| !boundary.is_empty()))

	## The polygon bounded by a single loop, with the loop's own interior.
	##
	## The loop is not normalized, so a loop enclosing more than half the
	## sphere gives a polygon that does too. The empty loop gives the empty
	## polygon.
	from_loop : S2Loop -> S2Polygon
	from_loop = |boundary| S2Polygon.from_loops([boundary])

	## The polygon bounded by the loop through the cell's four vertices,
	## `S2Loop.from_cell`. Upstream's `S2Polygon(const S2Cell&)`.
	from_cell : S2Cell -> S2Polygon
	from_cell = |cell| S2Polygon.from_loop(S2Loop.from_cell(cell))

	## The polygon containing nothing.
	empty : () -> S2Polygon
	empty = || { loops: [], bound: S2LatLngRect.empty(), inconsistent_orientations: Bool.False }

	## The polygon containing the whole sphere.
	full : () -> S2Polygon
	full = || {
		loops: [{ boundary: S2Loop.full(), depth: 0 }],
		bound: S2LatLngRect.full(),
		inconsistent_orientations: Bool.False,
	}

	## The loops in preorder: each loop is followed by the loops nested inside
	## it, so loop 0 is always a shell at depth 0.
	loops : S2Polygon -> List(Nested)
	loops = |polygon| polygon.loops

	## The number of loops, shells and holes together.
	num_loops : S2Polygon -> U64
	num_loops = |polygon| polygon.loops.len()

	## The `i`-th loop, or the empty loop when there is none.
	loop_at : S2Polygon, U64 -> S2Loop
	loop_at = |polygon, index| match polygon.loops.get(index) {
		Ok(entry) => entry.boundary
		Err(_) => S2Loop.empty()
	}

	## The nesting depth of the `i`-th loop.
	depth_at : S2Polygon, U64 -> U64
	depth_at = |polygon, index| match polygon.loops.get(index) {
		Ok(entry) => entry.depth
		Err(_) => 0
	}

	## True when the loop bounds a hole rather than a shell.
	is_hole : Nested -> Bool
	is_hole = |entry| entry.depth % 2 == 1

	## The `i`-th vertex of the loop, in the order that keeps the polygon's
	## interior on the left: reversed for a hole. Upstream's
	## `S2Loop::oriented_vertex`, which is on the loop there because an
	## upstream loop knows its depth.
	##
	## For a hole of `n` vertices, `0, 1, 2` give vertices `n - 1, n - 2,
	## n - 3`. The index wraps, as in `S2Loop.vertex`.
	oriented_vertex : Nested, U64 -> S2Point
	oriented_vertex = |entry, index| {
		n = entry.boundary.num_vertices()
		if n == 0 {
			return S2Point.zero()
		}
		j = index % n
		entry.boundary.vertex(if (S2Polygon.is_hole(entry)) n - 1 - j else j)
	}

	## The total number of vertices of all the loops. Upstream's
	## `num_vertices`: the full polygon has one, its full loop's marker.
	num_vertices : S2Polygon -> U64
	num_vertices = |polygon| polygon.loops.fold(0, |acc, entry| acc + entry.boundary.num_vertices())

	## The index of the loop that directly contains loop `k`, or `NoParent`
	## for a loop at depth 0. Upstream's `GetParent`.
	parent : S2Polygon, U64 -> Try(U64, [NoParent])
	parent = |polygon, k| {
		depth = polygon.depth_at(k)
		if depth == 0 {
			return Err(NoParent)
		}
		var $i = k
		while $i > 0 {
			$i = $i - 1
			if polygon.depth_at($i) < depth {
				return Ok($i)
			}
		}
		Err(NoParent)
	}

	## The index of the last loop nested inside loop `k`, or `k` itself
	## when nothing is. Loops `k` through the result are loop `k` and all
	## its descendants. Upstream's `GetLastDescendant` for `k >= 0`.
	last_descendant : S2Polygon, U64 -> U64
	last_descendant = |polygon, k| last_descendant_of(polygon.loops.map(|entry| entry.depth), k)

	## The level of the cells whose centres all the vertices are, or
	## `NotSnapped` when there is no such level or no vertex. Upstream's
	## `GetSnapLevel`.
	snap_level : S2Polygon -> Try(U64, [NotSnapped])
	snap_level = |polygon| S2Boundary.snap_level(polygon.loops.join_map(|entry| entry.boundary.vertices()))

	## True when the polygon has no loop.
	is_empty : S2Polygon -> Bool
	is_empty = |polygon| polygon.loops.is_empty()

	## True when the polygon is the single full loop.
	is_full : S2Polygon -> Bool
	is_full = |polygon| polygon.loops.len() == 1 and polygon.loop_at(0).is_full()

	## True when the polygon is well formed: `find_validation_error` finds
	## nothing.
	is_valid : S2Polygon -> Bool
	is_valid = |polygon| polygon.find_validation_error().is_ok()

	## The first reason the polygon is not well formed, if there is one.
	##
	## These are the checks of upstream's `FindValidationError` at v0.11.1, in
	## its order. Upstream v0.14.0 checks the loop depths first and then
	## validates its spatial index, so for an invalid polygon it can report a
	## different first error. Loop numbers are positions in `loops`.
	##
	## - `InvalidLoop`: the loop fails `S2Loop.is_valid`.
	## - `EmptyLoop`: the loop is the empty loop.
	## - `ExcessFullLoop`: the full loop is in a polygon with other loops.
	##   Only the full polygon has a full loop.
	## - `LoopsCross`: two loops cross, at interior points of their edges or
	##   at a vertex they share.
	## - `LoopsShareEdge`: two loops have an edge in common, in either
	##   direction.
	## - `InconsistentOrientations`: `from_oriented_loops` got loops whose
	##   orientations do not agree.
	## - `InvalidLoopDepth`: a loop is more than one level deeper than the
	##   loop before it, or loop 0 is not at depth 0.
	## - `InvalidNesting`: the first loop contains the second although the
	##   depths say it does not, or the reverse.
	##
	## Comparing every pair of edges costs the square of the total vertex
	## count, since this port has no spatial index.
	find_validation_error : S2Polygon -> Try({}, [InvalidLoop(U64), EmptyLoop(U64), ExcessFullLoop(U64), LoopsCross(U64, U64), LoopsShareEdge(U64, U64), InconsistentOrientations, InvalidLoopDepth(U64), InvalidNesting(U64, U64)])
	find_validation_error = |polygon| {
		n = polygon.loops.len()
		var $i = 0
		while $i < n {
			boundary = polygon.loop_at($i)
			if !boundary.is_valid() {
				return Err(InvalidLoop($i))
			}
			if boundary.is_empty() {
				return Err(EmptyLoop($i))
			}
			if boundary.is_full() and n > 1 {
				return Err(ExcessFullLoop($i))
			}
			$i = $i + 1
		}

		# Each loop with the polygon's interior on its left, as upstream's
		# index sees it, so a hole runs backwards. With more than one loop
		# none is full, so every loop here has edges.
		oriented = polygon.loops.map(
			|entry| if S2Polygon.is_hole(entry) {
				entry.boundary.vertices().rev()
			} else {
				entry.boundary.vertices()
			},
		)
		var $a = 0
		while $a < n {
			var $b = $a + 1
			while $b < n {
				match S2Boundary.find_loop_pair_error(oriented.get($a) ?? [], oriented.get($b) ?? []) {
					Err(Cross) => return Err(LoopsCross($a, $b))
					Err(ShareEdge) => return Err(LoopsShareEdge($a, $b))
					Ok(_) => {}
				}
				$b = $b + 1
			}
			$a = $a + 1
		}

		if polygon.inconsistent_orientations {
			return Err(InconsistentOrientations)
		}

		# The depths must describe a preorder walk of a nesting tree.
		depths = polygon.loops.map(|entry| entry.depth)
		var $limit = 0
		var $k = 0
		while $k < n {
			depth = depths.get($k) ?? 0
			if depth > $limit {
				return Err(InvalidLoopDepth($k))
			}
			$limit = depth + 1
			$k = $k + 1
		}
		# And they must match what contains what.
		var $outer = 0
		while $outer < n {
			last = last_descendant_of(depths, $outer)
			var $inner = 0
			while $inner < n {
				if $inner != $outer {
					nested = $inner > $outer and $inner <= last
					contains = polygon.loop_at($outer).contains_non_crossing_boundary(polygon.loop_at($inner), Bool.False)
					if contains != nested {
						return Err(InvalidNesting($outer, $inner))
					}
				}
				$inner = $inner + 1
			}
			$outer = $outer + 1
		}
		Ok({})
	}

	## True when the point is inside the polygon.
	##
	## Inside means an odd number of loops contain it, so a point in a hole is
	## outside.
	contains_point : S2Polygon, S2Point -> Bool
	contains_point = |polygon, p| {
		if !polygon.bound.contains_point(p) {
			return Bool.False
		}
		var $inside = Bool.False
		for entry in polygon.loops {
			if entry.boundary.contains_point(p) {
				$inside = !$inside
			}
		}
		$inside
	}

	## True when the position is in the polygon. Same as `contains_point` on
	## the matching point.
	contains_lat_lng : S2Polygon, S2LatLng -> Bool
	contains_lat_lng = |polygon, position| polygon.contains_point(position.to_point())

	## The area of the polygon's interior in steradians, holes subtracted.
	area : S2Polygon -> F64
	area = |polygon| {
		var $total = 0.0
		for entry in polygon.loops {
			$total = $total + sign_of(entry) * entry.boundary.area()
		}
		$total
	}

	## The centroid of the polygon's interior, scaled by its area.
	##
	## Holes subtract, as they do from the area. The result is not a unit
	## vector; normalize it to get a direction.
	centroid : S2Polygon -> S2Point
	centroid = |polygon| {
		var $total = S2Point.zero()
		for entry in polygon.loops {
			$total = $total.plus(entry.boundary.centroid().times(sign_of(entry)))
		}
		$total
	}

	## The distance from `x` to the polygon: zero when the polygon contains
	## `x`, otherwise the distance to its boundary. The empty polygon gives
	## `S1Angle.infinity()`. Upstream's `S2Polygon::GetDistance`.
	##
	## Upstream finds the nearest edge with its closest-edge query. This port
	## scans every edge, so the cost is linear in the vertex count.
	distance_to_point : S2Polygon, S2Point -> S1Angle
	distance_to_point = |polygon, x|
		if polygon.contains_point(x) {
			S1Angle.zero()
		} else {
			polygon.distance_to_boundary(x)
		}

	## The distance from `x` to the nearest point of the polygon's edges.
	## The empty and full polygons have no boundary, so they give
	## `S1Angle.infinity()`. Upstream's `GetDistanceToBoundary`. The cost is
	## linear in the vertex count.
	distance_to_boundary : S2Polygon, S2Point -> S1Angle
	distance_to_boundary = |polygon, x|
		match closest_edge(polygon, x) {
			Ok(edge) => edge.distance.to_angle()
			Err(NoEdges) => S1Angle.infinity()
		}

	## `x` itself when the polygon contains it, otherwise the nearest point
	## of the polygon's boundary. The empty polygon gives `x`. Upstream's
	## `S2Polygon::Project`.
	project : S2Polygon, S2Point -> S2Point
	project = |polygon, x|
		if polygon.contains_point(x) {
			x
		} else {
			polygon.project_to_boundary(x)
		}

	## The nearest point of the polygon's boundary to `x`. The empty and
	## full polygons have no boundary, so they give `x`. Upstream's
	## `ProjectToBoundary`. The cost is linear in the vertex count.
	project_to_boundary : S2Polygon, S2Point -> S2Point
	project_to_boundary = |polygon, x|
		match closest_edge(polygon, x) {
			Ok(edge) => S2Edge.project(x, edge.v0, edge.v1)
			Err(NoEdges) => x
		}

	## The complement of the polygon: every point it does not contain, and
	## the same boundary. Upstream's `Invert`, which `InitToComplement` also
	## uses.
	##
	## The empty polygon becomes full and the full polygon empty. Otherwise
	## the shell at depth 0 with the largest area is inverted. Its former
	## siblings go one level deeper, and its former descendants one level
	## up. Ties between shells are broken by their vertices, so the loop
	## order of the input does not matter.
	invert : S2Polygon -> S2Polygon
	invert = |polygon| {
		if polygon.is_empty() {
			return S2Polygon.full()
		}
		var $k = 0
		var $tracked = []
		for entry in polygon.loops {
			$tracked = $tracked.append({ index: $k, boundary: entry.boundary, depth: entry.depth })
			$k = $k + 1
		}
		inverted = invert_nested($tracked)
		assemble(inverted.map(|entry| { boundary: entry.boundary, depth: entry.depth }), polygon.inconsistent_orientations)
	}

	## The complement of the polygon, the same as `invert`. Upstream's
	## `InitToComplement`.
	complement : S2Polygon -> S2Polygon
	complement = |polygon| polygon.invert()

	## True when no hole or shell shares more than one vertex with the loop
	## that directly contains it. Upstream's `IsNormalized`.
	##
	## Upstream notes that this is a weaker test than it should be: a
	## connected group of child loops should share at most one vertex with
	## their parent. Each child is compared with the vertices of its parent,
	## so the cost is the product of their vertex counts.
	is_normalized : S2Polygon -> Bool
	is_normalized = |polygon| {
		var $k = 0
		while $k < polygon.loops.len() {
			match polygon.parent($k) {
				Ok(p) => {
					parent_vertices = polygon.loop_at(p).vertices()
					count = polygon.loop_at($k).vertices().count_if(|v| parent_vertices.contains(v))
					if count > 1 {
						return Bool.False
					}
				}
				Err(NoParent) => {}
			}
			$k = $k + 1
		}
		Bool.True
	}

	## True when for each loop of this polygon the other has a loop at the
	## same depth with the same boundary, as `S2Loop.boundary_equals`
	## decides, and the two have the same number of loops. Upstream's
	## `BoundaryEquals`. The loops may be in any order.
	boundary_equals : S2Polygon, S2Polygon -> Bool
	boundary_equals = |polygon, other|
		match_loops(polygon, other, |a, b| a.boundary_equals(b))

	## Like `boundary_equals`, with each pair of loops compared by
	## `S2Loop.boundary_approx_equals`. Upstream's `BoundaryApproxEquals`.
	boundary_approx_equals : S2Polygon, S2Polygon, S1Angle -> Bool
	boundary_approx_equals = |polygon, other, max_error|
		match_loops(polygon, other, |a, b| b.boundary_approx_equals(a, max_error))

	## Like `boundary_equals`, with each pair of loops compared by
	## `S2Loop.boundary_near`. Upstream's `BoundaryNear`.
	boundary_near : S2Polygon, S2Polygon, S1Angle -> Bool
	boundary_near = |polygon, other, max_error|
		match_loops(polygon, other, |a, b| b.boundary_near(a, max_error))

	## The bounding rectangle of the polygon, which bounds its shells.
	rect_bound : S2Polygon -> S2LatLngRect
	rect_bound = |polygon| polygon.bound

	## The bounding cap of the polygon.
	cap_bound : S2Polygon -> S2Cap
	cap_bound = |polygon| polygon.bound.cap_bound()

	## A few cells that cover the polygon: those of its bounding cap.
	##
	## Upstream's `S2Polygon::GetCellUnionBound` takes the cells of its
	## spatial index instead, which this port does not have. So the
	## covering that `S2RegionCoverer` finds for a polygon can differ from
	## upstream's.
	cell_union_bound : S2Polygon -> List(S2CellId)
	cell_union_bound = |polygon| polygon.cap_bound().cell_union_bound()

	## True when the polygon contains every point of the cell.
	##
	## The one vertex of a full loop is a marker, not a boundary point, so
	## the full polygon contains every cell.
	contains_cell : S2Polygon, S2Cell -> Bool
	contains_cell = |polygon, cell| {
		if !polygon.contains_point(cell.center()) {
			return Bool.False
		}
		# A boundary wholly inside the cell leaves the cell sticking out of
		# the polygon, or covering a hole.
		!touches_cell_boundary(polygon, cell)
	}

	## True when the polygon and the cell share any point.
	may_intersect_cell : S2Polygon, S2Cell -> Bool
	may_intersect_cell = |polygon, cell|
		polygon.contains_point(cell.center()) or touches_cell_boundary(polygon, cell)

	## True when this polygon contains every point of the other.
	##
	## The polygon contains the other exactly when the other misses the
	## complement of this one, which takes two questions: the complement must
	## exclude the whole boundary of the other, and the other must exclude
	## every shell of that complement. The second question is what catches two
	## polygons that hold each other's boundary but not each other's interior.
	contains_polygon : S2Polygon, S2Polygon -> Bool
	contains_polygon = |polygon, other| {
		if other.is_empty() {
			return Bool.True
		}
		if polygon.is_empty() {
			return Bool.False
		}
		if polygon.is_full() {
			return Bool.True
		}
		if other.is_full() {
			return Bool.False
		}
		contains_boundary(polygon, other)
			and excludes_non_crossing_complement_shells(other, polygon)
	}

	## True when the two polygons share any interior point.
	##
	## They are disjoint exactly when this polygon excludes the whole boundary
	## of the other and the other excludes every shell of this one.
	intersects_polygon : S2Polygon, S2Polygon -> Bool
	intersects_polygon = |polygon, other| {
		if polygon.is_empty() or other.is_empty() {
			return Bool.False
		}
		if polygon.is_full() or other.is_full() {
			return Bool.True
		}
		!(excludes_boundary(polygon, other)
			and excludes_non_crossing_shells(other, polygon))
	}

	## True when this polygon contains every point of the loop.
	##
	## The loop keeps its own interior, as in `from_loop`, so a loop that
	## encloses more than half the sphere is not inverted first.
	contains_loop : S2Polygon, S2Loop -> Bool
	contains_loop = |polygon, boundary| polygon.contains_polygon(S2Polygon.from_loop(boundary))

	## True when this polygon and the loop share any interior point.
	##
	## As in `contains_loop`, the loop keeps its own interior.
	intersects_loop : S2Polygon, S2Loop -> Bool
	intersects_loop = |polygon, boundary| polygon.intersects_polygon(S2Polygon.from_loop(boundary))

	## True when the two polygons have the same loops in the same order, to
	## within `max_error` radians per vertex.
	approx_eq : S2Polygon, S2Polygon, F64 -> Bool
	approx_eq = |polygon, other, max_error| {
		if polygon.loops.len() != other.loops.len() {
			return Bool.False
		}
		var $ok = Bool.True
		var $i = 0
		while $i < polygon.loops.len() {
			if !polygon.loop_at($i).approx_eq(other.loop_at($i), max_error) {
				$ok = Bool.False
			}
			if polygon.depth_at($i) != other.depth_at($i) {
				$ok = Bool.False
			}
			$i = $i + 1
		}
		$ok
	}

	is_eq : S2Polygon, S2Polygon -> Bool
	is_eq = |polygon, other| polygon.approx_eq(other, 0.0)

	to_inspect : S2Polygon -> Str
	to_inspect = |polygon| "S2Polygon(${polygon.loops.len().to_str()} loops)"

	## The bytes that upstream's `S2Polygon::Encode` writes with its default
	## hint, `CodingHint::COMPACT`: the compressed format when it is smaller,
	## and `encode_uncompressed` otherwise.
	##
	## The compressed format is the version byte 4, the snap level, the
	## number of loops as a varint, and then each loop: its number of
	## vertices as a varint, the vertices in the format of
	## `S2PointCompression.encode_points_compressed`, a varint of flags (1
	## for `origin_inside`, 2 when the bound follows), the depth as a varint,
	## and, for a loop of 64 vertices or more, its bound in the format of
	## `S2LatLngRect.encode`.
	##
	## The snap level is the level whose cell centres most of the vertices
	## are, the lowest such level on a tie. The compressed format is chosen
	## when about 4 bytes for each vertex, plus 26 for each vertex that is not
	## such a centre, is less than the 24 bytes for each vertex of the
	## lossless format. A polygon with no vertex is always compressed. Both
	## formats are lossless.
	encode : S2Polygon -> List(U8)
	encode = |polygon| {
		all = polygon.loops.join_map(|entry| entry.boundary.vertices().map(S2PointCompression.xyz_face_si_ti))
		level =
			if all.is_empty() {
				30
			} else {
				match compact_snap_level(all) {
					Ok(l) => l
					Err(Lossless) => return polygon.encode_uncompressed()
				}
			}
		header = [4, level.to_u8_wrap()] |> S2Coder.put_varint32(polygon.loops.len())
		polygon.loops.fold(header, |out, entry| out.concat(encode_loop_compressed(entry, level)))
	}

	## The bytes that upstream's `S2Polygon::EncodeUncompressed` writes: the
	## version byte 1, the byte 1 that stands for the obsolete `owns_loops`
	## field, a byte that tells whether any loop is a hole, the number of loops
	## as a little-endian 32-bit integer, each loop in the format of
	## `S2Loop.encode` with its own depth, and the bounding rectangle in the
	## format of `S2LatLngRect.encode`. This is the lossless format.
	encode_uncompressed : S2Polygon -> List(U8)
	encode_uncompressed = |polygon| {
		has_holes = polygon.loops.any(|entry| entry.depth % 2 == 1)
		header =
			[1, 1, if (has_holes) 1 else 0]
				|> S2Coder.put_u32(polygon.loops.len())
		polygon.loops.fold(header, |out, entry| out.concat(encode_loop(entry)))
			|> List.concat(polygon.bound.encode())
	}

	## The polygon that `encode` or `encode_uncompressed` writes. Bytes after
	## the polygon are ignored.
	##
	## Upstream's `Decode` trusts the stored depths, flags and bounds without
	## a check, and so does this function. A loop with no vertex, and an
	## empty loop, are dropped, as upstream drops them. The two obsolete bytes
	## are ignored. In the compressed format a loop without a stored bound
	## gets the bound of its vertices, and the polygon gets the union of the
	## bounds of its loops at depth 0, as upstream computes them.
	##
	## A version byte other than 1 or 4 is `UnsupportedVersion`. More than
	## 10000000 loops is `TooManyLoops`, which is the default limit of
	## upstream's flag `s2polygon_decode_max_num_loops`. A loop can give any
	## error of `S2Loop.decode`. In the compressed format a snap level above
	## 30 and a loop with no vertex are `InvalidEncoding`, and the points can
	## give any error of `S2PointCompression.decode_points_compressed`.
	decode : List(U8) -> Try(S2Polygon, [Truncated, UnsupportedVersion(U8), TooManyLoops, TooManyVertices, InvalidRect, BadVarint, InvalidEncoding])
	decode = |bytes| {
		version = S2Coder.get_u8(bytes, 0)?
		if version == 4 {
			return decode_compressed(bytes)
		}
		if version != 1 {
			return Err(UnsupportedVersion(version))
		}
		if !S2Coder.can_read(bytes, 1, 6) {
			return Err(Truncated)
		}
		count = S2Coder.get_u32(bytes, 3)?
		if count > 10000000 {
			return Err(TooManyLoops)
		}
		var $loops = []
		var $pos = 7
		for _ in 0..<count {
			rest = bytes.drop_first($pos)
			boundary = S2Loop.decode(rest)?
			size = 43 + boundary.num_vertices() * 24
			depth = S2Coder.get_u32(rest, 6 + boundary.num_vertices() * 24)?
			if boundary.num_vertices() > 0 and !boundary.is_empty() {
				$loops = $loops.append({ boundary: boundary, depth: depth })
			}
			$pos = $pos + size
		}
		bound = S2LatLngRect.decode(bytes.drop_first($pos))?
		Ok({ loops: $loops, bound: bound, inconsistent_orientations: Bool.False })
	}
}

## The compressed format of `encode`, after the version byte.
decode_compressed : List(U8) -> Try(S2Polygon, [Truncated, UnsupportedVersion(U8), TooManyLoops, TooManyVertices, InvalidRect, BadVarint, InvalidEncoding])
decode_compressed = |bytes| {
	snap_level = S2Coder.get_u8(bytes, 1)?
	if snap_level > 30 {
		return Err(InvalidEncoding)
	}
	(count, start) = S2Coder.get_varint32(bytes, 2)?
	if count > 10000000 {
		return Err(TooManyLoops)
	}
	var $loops = []
	var $pos = start
	for _ in 0..<count {
		(num_vertices, after_count) = S2Coder.get_varint32(bytes, $pos)?
		if num_vertices == 0 {
			return Err(InvalidEncoding)
		}
		if num_vertices > 50000000 {
			return Err(TooManyVertices)
		}
		decoded = S2PointCompression.decode_points_compressed(bytes.drop_first(after_count), num_vertices, snap_level.to_u64())?
		(properties, after_properties) = S2Coder.get_varint32(bytes, after_count + decoded.size)?
		(depth, after_depth) = S2Coder.get_varint32(bytes, after_properties)?
		origin_inside = properties.bitwise_and(1) != 0
		(bound, next) =
			if properties.bitwise_and(2) != 0 {
				(S2LatLngRect.decode(bytes.drop_first(after_depth))?, after_depth + 33)
			} else {
				(S2Boundary.compute_bound(decoded.points, origin_inside), after_depth)
			}
		$pos = next
		boundary : S2Loop
		boundary = { vertices: decoded.points, origin_inside: origin_inside, bound: bound }
		if !boundary.is_empty() {
			$loops = $loops.append({ boundary: boundary, depth: depth })
		}
	}
	Ok(assemble($loops, Bool.False))
}

## The encoding of a loop in the compressed format of `encode`, at the given
## snap level.
encode_loop_compressed : S2Polygon.Nested, U64 -> List(U8)
encode_loop_compressed = |entry, level| {
	boundary = entry.boundary
	n = boundary.num_vertices()
	# Loops of 64 vertices or more carry their bound, which is costly to
	# compute again.
	with_bound = n >= 64
	properties = (if (boundary.origin_inside) 1 else 0) + (if (with_bound) 2 else 0)
	out =
		[]
			|> S2Coder.put_varint32(n)
			|> List.concat(S2PointCompression.encode_points_compressed(boundary.vertices().map(S2PointCompression.xyz_face_si_ti), level))
			|> S2Coder.put_varint32(properties)
			|> S2Coder.put_varint32(entry.depth)
	if with_bound {
		out.concat(boundary.rect_bound().encode())
	} else {
		out
	}
}

## Upstream's choice of format in `Encode`: the level whose cell centres most
## of the points are, the lowest on a tie, when the compressed format is
## estimated to be smaller, and `Err(Lossless)` otherwise.
compact_snap_level : List(S2PointCompression.S2XYZFaceSiTi) -> Try(U64, [Lossless])
compact_snap_level = |all| {
	histogram = all.fold(
		List.repeat(0.U64, 31),
		|counts, v| match v.cell_level {
			Ok(level) => counts.update(level, |c| c + 1) ?? counts
			Err(_) => counts
		},
	)
	(level, snapped) = histogram.fold_with_index((0, 0), |(best, best_count), count, i| if (count > best_count) (i, count) else (best, best_count))
	n = all.len()
	if 4 * n + 26 * (n - snapped) < 24 * n {
		Ok(level)
	} else {
		Err(Lossless)
	}
}

## The encoding of the loop, with its depth in the field for it. The format is
## that of `S2Loop.encode`.
encode_loop : S2Polygon.Nested -> List(U8)
encode_loop = |entry| {
	boundary = entry.boundary
	boundary.vertices()
		.fold(
			[1] |> S2Coder.put_u32(boundary.num_vertices()),
			|out, p| out.concat(p.encode()),
		)
		|> S2Coder.put_u8(if (boundary.origin_inside) 1 else 0)
		|> S2Coder.put_u32(entry.depth)
		|> List.concat(boundary.rect_bound().encode())
}

## The edge nearest to `x`, with each loop oriented as `oriented_vertex`
## orients it, as upstream's spatial index holds the edges. The full loop has
## no edges.
closest_edge : S2Polygon, S2Point -> Try({ distance : S1ChordAngle, v0 : S2Point, v1 : S2Point }, [NoEdges])
closest_edge = |polygon, x| {
	chains =
		polygon.loops
			.keep_if(|entry| !entry.boundary.is_empty_or_full())
			.map(
				|entry| if S2Polygon.is_hole(entry) {
					entry.boundary.vertices().rev()
				} else {
					entry.boundary.vertices()
				},
			)
	S2Boundary.closest_edge(chains, x)
}

## True when the polygons have the same number of loops and each loop of the
## first has a partner in the second at the same depth for which `same`
## holds. As upstream assumes, there is at most one candidate partner.
match_loops : S2Polygon, S2Polygon, (S2Loop, S2Loop -> Bool) -> Bool
match_loops = |polygon, other, same| {
	if polygon.loops.len() != other.loops.len() {
		return Bool.False
	}
	polygon.loops.all(
		|a| other.loops.any(|b| b.depth == a.depth and same(a.boundary, b.boundary)),
	)
}

## The polygon with the given loops, already in preorder, and its bound:
## the union of the bounds of its shells at depth 0.
assemble : List(S2Polygon.Nested), Bool -> S2Polygon
assemble = |nested, inconsistent_orientations| {
	var $bound = S2LatLngRect.empty()
	for entry in nested {
		if entry.depth == 0 {
			$bound = $bound.union(entry.boundary.rect_bound())
		}
	}
	{ loops: nested, bound: $bound, inconsistent_orientations: inconsistent_orientations }
}

## The nesting tree of the loops, as `(index, depth)` pairs in preorder.
##
## Ports upstream's `InsertLoop` and `InitLoops`. Each loop goes below the
## deepest loop already placed that contains it, and takes over the children
## of that loop that it contains itself. Siblings keep their input order.
nest : List(S2Loop) -> List((U64, U64))
nest = |loops| {
	n = loops.len()
	at = |k| loops.get(k) ?? S2Loop.empty()
	# The children of each loop, and at index `n` those of the root.
	var $children = List.repeat([], n + 1)
	var $k = 0
	while $k < n {
		new_loop = at($k)
		var $parent = n
		var $descending = Bool.True
		while $descending {
			found = ($children.get($parent) ?? []).find_first(|child| at(child).contains_nested(new_loop))
			match found {
				Ok(child) => {
					$parent = child
				}
				Err(_) => {
					$descending = Bool.False
				}
			}
		}
		siblings = $children.get($parent) ?? []
		moved = siblings.keep_if(|child| new_loop.contains_nested(at(child)))
		staying = siblings.drop_if(|child| new_loop.contains_nested(at(child)))
		$children = $children.set($parent, staying.append($k)) ?? $children
		$children = $children.set($k, moved) ?? $children
		$k = $k + 1
	}
	preorder($children, n, 0, [])
}

## Appends the subtree below `node` to `acc` in preorder, its children at
## depth `depth`.
preorder : List(List(U64)), U64, U64, List((U64, U64)) -> List((U64, U64))
preorder = |children, node, depth, acc| {
	var $acc = acc
	for child in children.get(node) ?? [] {
		$acc = preorder(children, child, depth + 1, $acc.append((child, depth)))
	}
	$acc
}

## The index of the last loop nested inside loop `k`, given the depths of
## loops in preorder. That is `k` itself when nothing is nested inside it.
last_descendant_of : List(U64), U64 -> U64
last_descendant_of = |depths, k| {
	depth = depths.get(k) ?? 0
	var $last = k
	while $last + 1 < depths.len() and (depths.get($last + 1) ?? 0) > depth {
		$last = $last + 1
	}
	$last
}

## The polygon whose interior is on the left of every loop, none of them
## empty. Ports upstream's `InitOriented`.
##
## Each loop is first normalized, or for a loop too close to a great circle
## to tell, inverted when it contains the reference point. That gives loops
## that nest, and so either the polygon or its complement. Of the loops next
## to the reference point, the deepest that contains it says which, and the
## polygon is inverted if it came out as the complement.
orient : List(S2Loop) -> S2Polygon
orient = |loops| {
	origin = S2Point.origin()
	contained = loops.map(|boundary| S2Boundary.compute_origin_inside(boundary.vertices()))
	prepared = loops.map(
		|boundary| {
			angle = boundary.turning_angle()
			flip =
				if angle.abs() > S2Boundary.curvature_max_error(boundary.vertices()) {
					angle < 0.0
				} else {
					S2Boundary.compute_origin_inside(boundary.vertices())
				}
			if (flip) boundary.invert() else boundary
		},
	)
	var $tracked = nest(prepared).map(
		|(index, depth)| { index: index, boundary: prepared.get(index) ?? S2Loop.empty(), depth: depth },
	)
	if !$tracked.is_empty() {
		var $inside = Bool.False
		var $origin_index = ($tracked.first() ?? { index: 0, boundary: S2Loop.empty(), depth: 0 }).index
		for entry in $tracked {
			if entry.boundary.contains_point(origin) {
				$inside = !$inside
				$origin_index = entry.index
			}
		}
		if (contained.get($origin_index) ?? Bool.False) != $inside {
			$tracked = invert_nested($tracked)
		}
	}
	# A loop must have been inverted exactly when it is now a hole.
	var $inconsistent = Bool.False
	for entry in $tracked {
		was_inverted =
			(contained.get(entry.index) ?? Bool.False)
				!= S2Boundary.compute_origin_inside(entry.boundary.vertices())
		if was_inverted != (entry.depth % 2 == 1) {
			$inconsistent = Bool.True
		}
	}
	assemble($tracked.map(|entry| { boundary: entry.boundary, depth: entry.depth }), $inconsistent)
}

## The complement of a non-empty polygon given as loops in preorder, each
## with the index it had in the input. Ports upstream's `S2Polygon::Invert`.
##
## The full polygon becomes empty. Otherwise the top-level shell with the
## largest area, that is the least turning angle, is inverted. Its former
## siblings go one level deeper and its former children one level up.
invert_nested : List({ index : U64, boundary : S2Loop, depth : U64 }) -> List({ index : U64, boundary : S2Loop, depth : U64 })
invert_nested = |loops| {
	n = loops.len()
	none = { index: 0, boundary: S2Loop.empty(), depth: 0 }
	at = |k| loops.get(k) ?? none
	if n == 0 or (n == 1 and at(0).boundary.is_full()) {
		return []
	}
	var $best = 0
	var $best_angle = 0.0
	var $have_angle = Bool.False
	var $i = 1
	while $i < n {
		if at($i).depth == 0 {
			if !$have_angle {
				$best_angle = at($best).boundary.turning_angle()
				$have_angle = Bool.True
			}
			angle = at($i).boundary.turning_angle()
			# Ties are broken by the vertices, so the result does not depend
			# on the input order.
			if angle < $best_angle
				or (angle == $best_angle
					and S2Boundary.compare_loops(at($i).boundary.vertices(), at($best).boundary.vertices()) < 0) {
				$best = $i
				$best_angle = angle
			}
		}
		$i = $i + 1
	}
	best = $best
	last = last_descendant_of(loops.map(|entry| entry.depth), best)
	chosen = at(best)
	var $result = [{ index: chosen.index, boundary: chosen.boundary.invert(), depth: chosen.depth }]
	var $k = 0
	while $k < n {
		entry = at($k)
		if $k < best or $k > last {
			$result = $result.append({ index: entry.index, boundary: entry.boundary, depth: entry.depth + 1 })
		}
		$k = $k + 1
	}
	$k = best + 1
	while $k <= last {
		entry = at($k)
		$result = $result.append({ index: entry.index, boundary: entry.boundary, depth: entry.depth - 1 })
		$k = $k + 1
	}
	$result
}

## True when a loop edge meets the cell's boundary, or a loop vertex is in
## the cell. The empty and full loops have no edges and no real vertices,
## so they never touch a cell.
touches_cell_boundary : S2Polygon, S2Cell -> Bool
touches_cell_boundary = |polygon, cell|
	polygon.loops.any(
		|entry| {
			points = entry.boundary.vertices()
			!entry.boundary.is_empty_or_full()
				and (S2Boundary.crosses_cell_boundary(points, cell)
					or S2Boundary.cell_contains_any(cell, points))
		},
	)

## How this polygon stands to the boundary of one loop: `1` when it
## contains that boundary, `-1` when it excludes it, `0` when the
## boundaries cross.
##
## Each loop of the polygon that contains the boundary flips the answer,
## which is the same odd-count rule that decides a point.
compare_boundary : S2Polygon, S2Loop, Bool -> I8
compare_boundary = |polygon, other, other_is_hole| {
	var $result = -1
	for entry in polygon.loops {
		if $result != 0 {
			side = entry.boundary.compare_boundary(other, other_is_hole)
			if side == 0 {
				$result = 0
			} else if side > 0 {
				$result = 0 - $result
			}
		}
	}
	$result
}

## True when this polygon contains every loop boundary of the other.
contains_boundary : S2Polygon, S2Polygon -> Bool
contains_boundary = |polygon, other| {
	var $ok = Bool.True
	for entry in other.loops {
		if compare_boundary(polygon, entry.boundary, S2Polygon.is_hole(entry)) <= 0 {
			$ok = Bool.False
		}
	}
	$ok
}

## True when this polygon excludes every loop boundary of the other.
excludes_boundary : S2Polygon, S2Polygon -> Bool
excludes_boundary = |polygon, other| {
	var $ok = Bool.True
	for entry in other.loops {
		if compare_boundary(polygon, entry.boundary, S2Polygon.is_hole(entry)) >= 0 {
			$ok = Bool.False
		}
	}
	$ok
}

## True when this polygon contains the loop's boundary, given that the
## boundaries are known not to cross.
contains_non_crossing_boundary : S2Polygon, S2Loop, Bool -> Bool
contains_non_crossing_boundary = |polygon, other, reverse_other| {
	var $inside = Bool.False
	for entry in polygon.loops {
		if entry.boundary.contains_non_crossing_boundary(other, reverse_other) {
			$inside = !$inside
		}
	}
	$inside
}

## True when this polygon excludes every shell boundary of the other,
## whose loops are known not to cross this polygon's boundary.
excludes_non_crossing_shells : S2Polygon, S2Polygon -> Bool
excludes_non_crossing_shells = |polygon, other| {
	var $ok = Bool.True
	for entry in other.loops {
		if !S2Polygon.is_hole(entry)
			and contains_non_crossing_boundary(polygon, entry.boundary, Bool.False) {
			$ok = Bool.False
		}
	}
	$ok
}

## True when this polygon excludes every shell boundary of the other's
## complement, whose loops are known not to cross this polygon's boundary.
##
## The complement of a polygon is its first loop inverted, with every
## other loop swapping shell for hole. So the complement's shells are that
## first loop, reversed, together with the polygon's own holes.
excludes_non_crossing_complement_shells : S2Polygon, S2Polygon -> Bool
excludes_non_crossing_complement_shells = |polygon, other| {
	if other.is_empty() {
		return !polygon.is_full()
	}
	if other.is_full() {
		return Bool.True
	}
	var $ok = Bool.True
	var $index = 0
	for entry in other.loops {
		is_first = $index == 0
		if is_first or S2Polygon.is_hole(entry) {
			if contains_non_crossing_boundary(polygon, entry.boundary, is_first) {
				$ok = Bool.False
			}
		}
		$index = $index + 1
	}
	$ok
}

expect {
	# The full loop's one vertex, the south pole, is on face 5. It is not a
	# boundary point, so the full polygon still contains face 5.
	faces = [0, 1, 2, 3, 4, 5].map(S2Cell.from_face)
	faces.all(|cell| S2Polygon.full().contains_cell(cell) and S2Polygon.full().may_intersect_cell(cell))
		and faces.all(|cell| !S2Polygon.empty().may_intersect_cell(cell))
}
expect {
	# A loop enclosing more than half the sphere keeps its own interior.
	square = |lat, lng| S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(lat - 1.0, lng - 1.0),
		S2LatLng.from_degrees(lat - 1.0, lng + 1.0),
		S2LatLng.from_degrees(lat + 1.0, lng + 1.0),
		S2LatLng.from_degrees(lat + 1.0, lng - 1.0),
	])
	polygon = S2Polygon.from_loop(square(0.0, 0.0))
	# Everything except a square far away contains the polygon, and
	# everything except the polygon's own square is not contained by it.
	far = square(40.0, 40.0).invert()
	not_here = square(0.0, 0.0).invert()
	polygon.intersects_loop(far)
		and !polygon.contains_loop(far)
		and !polygon.intersects_loop(not_here)
		and !polygon.contains_loop(not_here)
		and polygon.contains_loop(square(0.0, 0.0))
}

## A loop through the given `(lat, lng)` positions in degrees.
loop_of_degrees : List((F64, F64)) -> S2Loop
loop_of_degrees = |points| S2Loop.from_lat_lngs(points.map(|(lat, lng)| S2LatLng.from_degrees(lat, lng)))

## A counterclockwise square around `(lat, lng)` with sides of twice `half`
## degrees.
square_of : F64, F64, F64 -> S2Loop
square_of = |lat, lng, half| loop_of_degrees([
	(lat - half, lng - half),
	(lat - half, lng + half),
	(lat + half, lng + half),
	(lat + half, lng - half),
])

expect {
	# Upstream's IsValidTest.FullLoop: the full loop is allowed only alone.
	# Such a polygon is not full either, as upstream's `is_full` also says.
	polygon = S2Polygon.from_loops([square_of(0.0, 0.0, 1.0), S2Loop.full()])
	polygon.find_validation_error() == Err(ExcessFullLoop(0))
		and !polygon.is_valid()
		and !polygon.is_full()
		and S2Polygon.from_loops([S2Loop.full()]).is_valid()
}
expect {
	# Upstream's IsValidTest.DuplicateEdge: a square cut along a diagonal
	# gives two loops that share that edge in opposite directions.
	a = loop_of_degrees([(0.0, 0.0), (0.0, 2.0), (2.0, 2.0)])
	b = loop_of_degrees([(0.0, 0.0), (2.0, 2.0), (2.0, 0.0)])
	S2Polygon.from_loops([a, b]).find_validation_error() == Err(LoopsShareEdge(0, 1))
}
expect {
	# Two loops that meet only at two shared vertices, with no edges
	# crossing, but whose wedges at those vertices interleave: they cross
	# there, as upstream's FindSelfIntersection reports.
	a = loop_of_degrees([(0.0, 0.0), (-1.0, 2.0), (0.7, 4.0), (1.0, 2.0)])
	b = loop_of_degrees([(0.0, 0.0), (0.7, 4.0), (4.0, 0.0)])
	S2Polygon.from_loops([a, b]).find_validation_error() == Err(LoopsCross(0, 1))
}
expect {
	# Upstream's IsValidTest.LoopNestingInvalid: invert one loop of a valid
	# nesting and keep the depths. The inverted hole now contains the
	# shell, which the depths say it must not.
	polygon = S2Polygon.from_loops([square_of(0.0, 0.0, 2.0), square_of(0.0, 0.0, 1.0)])
	broken : S2Polygon
	broken = {
		loops: polygon.loops.map(
			|entry| if entry.depth == 1 {
				{ boundary: entry.boundary.invert(), depth: entry.depth }
			} else {
				entry
			},
		),
		bound: polygon.bound,
		inconsistent_orientations: Bool.False,
	}
	polygon.is_valid() and broken.find_validation_error() == Err(InvalidNesting(1, 0))
}
expect {
	# Upstream's IsValidTest.LoopDepthNegative: a loop two levels deeper than
	# the loop before it.
	polygon = S2Polygon.from_loops([square_of(0.0, 0.0, 2.0), square_of(0.0, 0.0, 1.0)])
	broken : S2Polygon
	broken = {
		loops: polygon.loops.map(|entry| { boundary: entry.boundary, depth: entry.depth * 2 }),
		bound: polygon.bound,
		inconsistent_orientations: Bool.False,
	}
	broken.find_validation_error() == Err(InvalidLoopDepth(1))
}
expect {
	# Upstream's IsValidTest.EmptyLoop. `from_loops` drops empty loops, so
	# the polygon is put together directly.
	shell = square_of(0.0, 0.0, 1.0)
	polygon : S2Polygon
	polygon = {
		loops: [{ boundary: shell, depth: 0 }, { boundary: S2Loop.empty(), depth: 0 }],
		bound: shell.rect_bound(),
		inconsistent_orientations: Bool.False,
	}
	polygon.find_validation_error() == Err(EmptyLoop(1))
}
expect {
	# Like upstream's InitNested, `from_loops` keeps each loop as it is: a
	# clockwise square bounds everything outside it.
	polygon = S2Polygon.from_loops([square_of(0.0, 0.0, 1.0).invert()])
	polygon.is_valid()
		and polygon.contains_point(S2LatLng.from_degrees(40.0, 40.0).to_point())
		and !polygon.contains_point(S2LatLng.from_degrees(0.0, 0.0).to_point())
}
expect {
	# The loops come out in preorder, each followed by the loops inside it,
	# as upstream's InitNested orders them: a shell, a hole holding an
	# island, and a second hole.
	shell = square_of(0.0, 0.0, 10.0)
	hole = square_of(-4.0, 0.0, 3.0)
	island = square_of(-4.0, 0.0, 1.0)
	other_hole = square_of(5.0, 0.0, 2.0)
	polygon = S2Polygon.from_loops([shell, hole, other_hole, island])
	polygon.is_valid()
		and polygon.loops.map(|entry| entry.depth) == [0, 1, 2, 1]
		and polygon.loop_at(0) == shell
		and polygon.loop_at(1) == hole
		and polygon.loop_at(2) == island
		and polygon.loop_at(3) == other_hole
}
expect {
	# The oriented convention: a counterclockwise shell and a clockwise hole,
	# in either order. The hole is inverted, so the result is the same as
	# from the nested loops.
	shell = square_of(0.0, 0.0, 2.0)
	hole = square_of(0.0, 0.0, 1.0)
	expected = S2Polygon.from_loops([shell, hole])
	a = S2Polygon.from_oriented_loops([shell, hole.invert()])
	b = S2Polygon.from_oriented_loops([hole.invert(), shell])
	a.is_valid() and a == expected and b == expected
}
expect {
	# With its interior on its left, one clockwise square alone is the
	# whole sphere outside it.
	polygon = S2Polygon.from_oriented_loops([square_of(0.0, 0.0, 1.0).invert()])
	polygon.is_valid()
		and polygon.contains_point(S2LatLng.from_degrees(40.0, 40.0).to_point())
		and !polygon.contains_point(S2LatLng.from_degrees(0.0, 0.0).to_point())
		and (polygon.area() - (4.0 * F64.pi - square_of(0.0, 0.0, 1.0).area())).abs() < 1e-12
}
expect {
	# Upstream's IsValidTest.InconsistentOrientations: two counterclockwise
	# loops, one inside the other, cannot both have the interior on their
	# left.
	polygon = S2Polygon.from_oriented_loops([square_of(0.0, 0.0, 2.0), square_of(0.0, 0.0, 1.0)])
	polygon.find_validation_error() == Err(InconsistentOrientations)
}
expect S2Polygon.from_oriented_loops([S2Loop.full()]).is_full()
expect S2Polygon.from_oriented_loops([]).is_empty()

## `1` for a shell, `-1` for a hole: what the loop's area contributes.
sign_of : Nested -> F64
sign_of = |entry| if S2Polygon.is_hole(entry) {
	-1.0
} else {
	1.0
}

# Upstream's S2PolygonTestBase.GetDistance: two nested rectangles around (0, 0),
# so the inner one is a hole. Points outside that project to an edge and to
# a vertex, inside that project to an outer edge and an inner vertex, in the
# hole, and on the boundary; then the empty and full polygons. Distances in
# radians, then Project and ProjectToBoundary, all from upstream.
expect {
	nested = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(3.0, 1.0), S2LatLng.from_degrees(3.0, -1.0), S2LatLng.from_degrees(-3.0, -1.0), S2LatLng.from_degrees(-3.0, 1.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 2.0), S2LatLng.from_degrees(4.0, -2.0), S2LatLng.from_degrees(-4.0, -2.0), S2LatLng.from_degrees(-4.0, 2.0)])])
	check = |polygon, x, expected| {
		(distance, boundary, projected, on_boundary) = expected
		polygon.distance_to_point(x).radians() == distance
			and polygon.distance_to_boundary(x).radians() == boundary
			and polygon.project(x) == projected
			and polygon.project_to_boundary(x) == on_boundary
	}
	y = S2Point.new(0.0, 1.0, 0.0)
	inf = S1Angle.infinity().radians()
	check(nested, S2LatLng.from_degrees(0.0, -4.7).to_point(), (0.047123889803846908, 0.047123889803846908, S2Point.new(0.99939082701909576, -0.034899496702500969, 0.0), S2Point.new(0.99939082701909576, -0.034899496702500969, 0.0)))
		and check(nested, S2LatLng.from_degrees(6.0, -3.0).to_point(), (0.038996688676648301, 0.038996688676648301, S2Point.new(0.99695636119368447, -0.034814483282576247, 0.069756473744125302), S2Point.new(0.99695636119368447, -0.034814483282576247, 0.069756473744125302)))
		and check(nested, S2LatLng.from_degrees(0.0, 1.7).to_point(), (0.0, 0.0052359877559829803, S2Point.new(0.99955986011938402, 0.029666244085110757, 0.0), S2Point.new(0.99939082701909576, 0.034899496702500969, -0.0)))
		and check(nested, S2LatLng.from_degrees(-3.3, -1.3).to_point(), (0.0, 0.0073992087714004409, S2Point.new(0.99808485273767145, -0.022649713813178974, -0.057564026959567277), S2Point.new(0.99847743863945992, -0.017428488520812163, -0.052335956242943835)))
		and check(nested, S2LatLng.from_degrees(0.0, 0.1).to_point(), (0.015707963267948963, 0.015707963267948963, S2Point.new(0.99984769515639127, 0.017452406437283512, 0.0), S2Point.new(0.99984769515639127, 0.017452406437283512, 0.0)))
		and check(nested, S2LatLng.from_degrees(3.0, 1.0).to_point(), (0.0, 0.0, S2Point.new(0.99847743863945992, 0.017428488520812163, 0.052335956242943835), S2Point.new(0.99847743863945992, 0.017428488520812163, 0.052335956242943835)))
		and check(nested, S2LatLng.from_degrees(0.0, 2.0).to_point(), (0.0, 1.1102230246251565e-16, S2Point.new(0.99939082701909576, 0.034899496702500969, 0.0), S2Point.new(0.99939082701909576, 0.034899496702500969, -0.0)))
		and check(S2Polygon.empty(), y, (inf, inf, S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0)))
		and check(S2Polygon.full(), y, (0.0, inf, S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0)))
}
# Upstream's num_vertices, GetSnapLevel, IsNormalized, GetParent and
# GetLastDescendant for a shell holding a hole holding a shell, beside a
# second shell; and for a hole that touches its shell at two vertices.
# From upstream, with -1 for no parent and for no snap level.
expect {
	polygon = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(4.0, 6.0), S2LatLng.from_degrees(6.0, 6.0), S2LatLng.from_degrees(6.0, 4.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 21.0), S2LatLng.from_degrees(21.0, 21.0), S2LatLng.from_degrees(21.0, 20.0)])])
	indices = [0, 1, 2, 3]
	polygon.num_vertices() == 16
		and polygon.snap_level() == Err(NotSnapped)
		and polygon.is_normalized() == Bool.True
		and indices.map(|k| polygon.depth_at(k)) == [0, 1, 2, 0]
		and indices.map(|k| polygon.parent(k)) == [Err(NoParent), Ok(0), Ok(1), Err(NoParent)]
		and indices.map(|k| polygon.last_descendant(k)) == [2, 2, 2, 3]
}
expect {
	polygon = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(4.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.0, 3.0), S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(3.0, 1.0)])])
	indices = [0, 1]
	polygon.num_vertices() == 8
		and polygon.snap_level() == Err(NotSnapped)
		and polygon.is_normalized() == Bool.False
		and indices.map(|k| polygon.depth_at(k)) == [0, 1]
		and indices.map(|k| polygon.parent(k)) == [Err(NoParent), Ok(0)]
		and indices.map(|k| polygon.last_descendant(k)) == [1, 1]
}
# Upstream's Invert: the depth and vertex count of each loop, and then all
# the vertices in order, from upstream.
expect {
	inverted = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(4.0, 6.0), S2LatLng.from_degrees(6.0, 6.0), S2LatLng.from_degrees(6.0, 4.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 21.0), S2LatLng.from_degrees(21.0, 21.0), S2LatLng.from_degrees(21.0, 20.0)])]).invert()
	inverted.loops().map(|entry| (entry.depth, entry.boundary.num_vertices())) == [(0, 4), (1, 4), (0, 4), (1, 4)]
		and inverted.loops().join_map(|entry| entry.boundary.vertices()) == [
			S2Point.new(0.98480775301220802, 0.0, 0.17364817766693033),
			S2Point.new(0.9698463103929541, 0.17101007166283433, 0.17364817766693033),
			S2Point.new(0.98480775301220802, 0.17364817766693033, 0.0),
			S2Point.new(1.0, 0.0, 0.0),
			S2Point.new(0.88302222155948906, 0.32139380484326968, 0.34202014332566871),
			S2Point.new(0.8772786376895817, 0.3367557177138954, 0.34202014332566871),
			S2Point.new(0.87157241273869712, 0.33456530317942912, 0.35836794954530027),
			S2Point.new(0.8772786376895817, 0.31930331127661188, 0.35836794954530027),
			S2Point.new(0.99878202512991221, 0.034878236872062651, 0.034899496702500969),
			S2Point.new(0.98966482419024082, 0.13908832046729191, 0.034899496702500969),
			S2Point.new(0.98063084796915956, 0.13781867790849958, 0.13917310096006544),
			S2Point.new(0.98966482419024082, 0.034559857199638437, 0.13917310096006544),
			S2Point.new(0.99513403437078507, 0.069586550480032719, 0.069756473744125302),
			S2Point.new(0.99209929001565178, 0.10427383718471565, 0.069756473744125302),
			S2Point.new(0.98907380036690273, 0.10395584540887966, 0.10452846326765347),
			S2Point.new(0.99209929001565178, 0.069374340482214691, 0.10452846326765347),
		]
		and S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(4.0, 6.0), S2LatLng.from_degrees(6.0, 6.0), S2LatLng.from_degrees(6.0, 4.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 21.0), S2LatLng.from_degrees(21.0, 21.0), S2LatLng.from_degrees(21.0, 20.0)])]).complement() == inverted
}
expect {
	inverted = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(3.0, 1.0), S2LatLng.from_degrees(3.0, -1.0), S2LatLng.from_degrees(-3.0, -1.0), S2LatLng.from_degrees(-3.0, 1.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 2.0), S2LatLng.from_degrees(4.0, -2.0), S2LatLng.from_degrees(-4.0, -2.0), S2LatLng.from_degrees(-4.0, 2.0)])]).invert()
	inverted.loops().map(|entry| (entry.depth, entry.boundary.num_vertices())) == [(0, 4), (0, 4)]
		and inverted.loops().join_map(|entry| entry.boundary.vertices()) == [
			S2Point.new(0.99695636119368447, 0.034814483282576247, -0.069756473744125302),
			S2Point.new(0.99695636119368447, -0.034814483282576247, -0.069756473744125302),
			S2Point.new(0.99695636119368447, -0.034814483282576247, 0.069756473744125302),
			S2Point.new(0.99695636119368447, 0.034814483282576247, 0.069756473744125302),
			S2Point.new(0.99847743863945992, 0.017428488520812163, 0.052335956242943835),
			S2Point.new(0.99847743863945992, -0.017428488520812163, 0.052335956242943835),
			S2Point.new(0.99847743863945992, -0.017428488520812163, -0.052335956242943835),
			S2Point.new(0.99847743863945992, 0.017428488520812163, -0.052335956242943835),
		]
		and S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(3.0, 1.0), S2LatLng.from_degrees(3.0, -1.0), S2LatLng.from_degrees(-3.0, -1.0), S2LatLng.from_degrees(-3.0, 1.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 2.0), S2LatLng.from_degrees(4.0, -2.0), S2LatLng.from_degrees(-4.0, -2.0), S2LatLng.from_degrees(-4.0, 2.0)])]).complement() == inverted
}
# Upstream inverts the empty polygon to the full one, whose one loop is at
# depth 0 with one vertex, (0, 0, -1): '0 1 0 0 -1'. The full polygon inverts to
# the empty one, with no loops.
expect S2Polygon.empty().invert().is_full() and S2Polygon.full().invert().is_empty()
# Upstream's BoundaryEquals, BoundaryApproxEquals and BoundaryNear: the same
# loops in another order and from other starting vertices, a moved vertex,
# an added vertex on an edge, and a missing hole. From upstream.
expect {
	compare = |a, b, degrees| (a.boundary_equals(b), a.boundary_approx_equals(b, S1Angle.from_degrees(degrees)), a.boundary_near(b, S1Angle.from_degrees(degrees)))
	compare(S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0), S2LatLng.from_degrees(2.0, 2.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0), S2LatLng.from_degrees(0.0, 0.0)])]), 0.1) == (Bool.True, Bool.True, Bool.True)
		and compare(S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.1), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), 0.2) == (Bool.False, Bool.True, Bool.True)
		and compare(S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.1), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), 0.05) == (Bool.False, Bool.False, Bool.False)
		and compare(S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 5.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), 0.1) == (Bool.False, Bool.False, Bool.True)
		and compare(S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])]), S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)])]), 0.1) == (Bool.False, Bool.False, Bool.False)
}
# Upstream's S2Polygon.TestS2CellConstructorAndContains, without the union.
expect {
	cell = S2Cell.from_lat_lng(S2LatLng.from_degrees(40.565459, -74.645276))
	polygon = S2Polygon.from_cell(cell)
	copy = S2Polygon.from_loop(S2Loop.from_points(polygon.loop_at(0).vertices()))
	polygon.num_loops() == 1 and polygon.loop_at(0) == S2Loop.from_cell(cell)
		and copy.contains_polygon(polygon) and polygon.contains_polygon(copy)
}
# Upstream bounds a polygon by the cells of its index; this port uses the
# cap bound, as for a loop.
expect {
	polygon = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(3.0, 1.0), S2LatLng.from_degrees(3.0, -1.0), S2LatLng.from_degrees(-3.0, -1.0), S2LatLng.from_degrees(-3.0, 1.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 2.0), S2LatLng.from_degrees(4.0, -2.0), S2LatLng.from_degrees(-4.0, -2.0), S2LatLng.from_degrees(-4.0, 2.0)])])
	polygon.cell_union_bound() == polygon.cap_bound().cell_union_bound()
		and polygon.cell_union_bound() == polygon.loop_at(0).cell_union_bound()
}
# oriented_vertex walks a hole backwards.
expect {
	polygon = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(3.0, 1.0), S2LatLng.from_degrees(3.0, -1.0), S2LatLng.from_degrees(-3.0, -1.0), S2LatLng.from_degrees(-3.0, 1.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(4.0, 2.0), S2LatLng.from_degrees(4.0, -2.0), S2LatLng.from_degrees(-4.0, -2.0), S2LatLng.from_degrees(-4.0, 2.0)])])
	shell = polygon.loops().get(0) ?? { boundary: S2Loop.empty(), depth: 0 }
	hole = polygon.loops().get(1) ?? { boundary: S2Loop.empty(), depth: 0 }
	S2Polygon.oriented_vertex(shell, 1) == shell.boundary.vertex(1)
		and S2Polygon.oriented_vertex(hole, 0) == hole.boundary.vertex(3)
		and S2Polygon.oriented_vertex(hole, 1) == hole.boundary.vertex(2)
		and S2Polygon.oriented_vertex(hole, 5) == hole.boundary.vertex(2)
}

# Two holes in one shell, from upstream's GetParent and GetLastDescendant:
# depths 0, 1, 1, parents none, 0, 0, last descendants 2, 1, 2.
expect {
	square = |lo, hi| S2Loop.from_lat_lngs([S2LatLng.from_degrees(lo, lo), S2LatLng.from_degrees(lo, hi), S2LatLng.from_degrees(hi, hi), S2LatLng.from_degrees(hi, lo)])
	polygon = S2Polygon.from_loops([square(0.0, 10.0), square(2.0, 4.0), square(6.0, 8.0)])
	[0, 1, 2].map(|k| polygon.depth_at(k)) == [0, 1, 1]
		and [0, 1, 2].map(|k| polygon.parent(k)) == [Err(NoParent), Ok(0), Ok(0)]
		and [0, 1, 2].map(|k| polygon.last_descendant(k)) == [2, 1, 2]
		and polygon.num_vertices() == 12
		and polygon.is_normalized()
}

# S2Polygon encoding against upstream's `EncodeUncompressed`, and decoding it
# back.
expect S2Coder.to_hex(S2Polygon.empty().encode_uncompressed()) == "0101000000000001000000000000f03f0000000000000000182d4454fb210940182d4454fb2109c0"
expect S2Polygon.decode(S2Coder.from_hex("0101000000000001000000000000f03f0000000000000000182d4454fb210940182d4454fb2109c0")) == Ok(S2Polygon.empty())
expect S2Coder.to_hex(S2Polygon.full().encode_uncompressed()) == "01010001000000010100000000000000000000000000000000000000000000000000f0bf010000000001182d4454fb21f9bf182d4454fb21f93f182d4454fb2109c0182d4454fb21094001182d4454fb21f9bf182d4454fb21f93f182d4454fb2109c0182d4454fb210940"
expect S2Polygon.decode(S2Coder.from_hex("01010001000000010100000000000000000000000000000000000000000000000000f0bf010000000001182d4454fb21f9bf182d4454fb21f93f182d4454fb2109c0182d4454fb21094001182d4454fb21f9bf182d4454fb21f93f182d4454fb2109c0182d4454fb210940")) == Ok(S2Polygon.full())
expect S2Coder.to_hex(S2Polygon.from_loop(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])).encode_uncompressed()) == "010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940"
expect S2Polygon.decode(S2Coder.from_hex("010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940")) == Ok(S2Polygon.from_loop(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])))

# Upstream's `Encode` with its default hint. The empty polygon is always
# compressed, and the vertices of the full polygon and of the triangle are
# centres of cells at level 0.
expect S2Coder.to_hex(S2Polygon.empty().encode()) == "041e00"
expect S2Polygon.decode(S2Coder.from_hex("041e00")) == Ok(S2Polygon.empty())
expect S2Coder.to_hex(S2Polygon.full().encode()) == "040001010b000100"
expect S2Polygon.decode(S2Coder.from_hex("040001010b000100")) == Ok(S2Polygon.full())
expect S2Coder.to_hex(S2Polygon.from_loop(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])).encode()) == "040001030607080000000000"
expect S2Polygon.decode(S2Coder.from_hex("040001030607080000000000")) == Ok(S2Polygon.from_loop(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])))
expect
	S2Polygon.decode(S2Coder.from_hex("040001030607080000000000")).map_ok(|p| S2Coder.to_hex(p.encode_uncompressed()))
		== Ok("010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000080000000000000f03f000000000000000000000000000000800000000000000080000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940")
# A compressed loop of four cell centres at level 10, decoded as upstream
# decodes it.
expect
	S2Polygon.decode(S2Coder.from_hex("04000104180000000301171c818c8b83ef3f89730b7e1a3ac63f0000000000000000028d162921fb08ef3ff40b8a74a8e3c53f89730b7e1a3ac63f03171c818c8b83ef3f000000000000000089730b7e1a3ac63f0000")).map_ok(|p| S2Coder.to_hex(p.encode_uncompressed()))
		== Ok("010100010000000104000000000000000000f03f00000000000000000000000000000000171c818c8b83ef3f89730b7e1a3ac63f00000000000000008d162921fb08ef3ff40b8a74a8e3c53f89730b7e1a3ac63f171c818c8b83ef3f000000000000000089730b7e1a3ac63f000000000001193c52217c17cabca2cb5f5b7f6cc63f00000000000000008744e74a1857c63f01193c52217c17cabca2cb5f5b7f6cc63f00000000000000008744e74a1857c63f")
expect S2Polygon.decode(S2Coder.from_hex("04")) == Err(Truncated)
# Any other version is not known.
expect S2Polygon.decode(S2Coder.from_hex("020100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940")) == Err(UnsupportedVersion(2))
expect S2Polygon.decode(S2Coder.from_hex("000100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940")) == Err(UnsupportedVersion(0))
expect S2Polygon.decode([]) == Err(Truncated)
expect S2Polygon.decode(S2Coder.from_hex("01")) == Err(Truncated)
expect S2Polygon.decode(S2Coder.from_hex("010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb2109")) == Err(Truncated)
expect S2Polygon.decode(S2Coder.from_hex("010100ffffffff")) == Err(TooManyLoops)
expect S2Polygon.decode(S2Coder.from_hex("010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940ff")) == S2Polygon.decode(S2Coder.from_hex("010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940"))
# The nesting depth is kept, whatever it is.
expect S2Polygon.decode(S2Coder.from_hex("010100010000000103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f00ffffff7f01000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb21094001000000000000d4bc182d4454fb21f93f182d4454fb2109c0182d4454fb210940")) |> Try.map_ok(|p| p.depth_at(0)) == Ok(2147483647)

import S1Angle
import S1ChordAngle
import S2Cap
import S2Cell
import S2CellId
import S2Edge
import S2LatLng
import S2LatLngRect
import Internal/S2Boundary
import S2Point

## A simple closed polygon on the sphere: a sequence of vertices joined by
## geodesic edges, with the last vertex joined back to the first.
##
## The interior is the region to the left of the edges, so vertex order decides
## which side is inside. A loop that runs counterclockwise as seen from outside
## the sphere encloses less than half of it; `invert` swaps interior for
## exterior.
##
## A loop with one vertex is special: it is the full loop, containing
## everything, when that vertex is in the southern hemisphere (`z < 0`), and
## the empty loop, containing nothing, otherwise. `empty` and `full` give the
## north and south poles. They exist so that the empty and full regions have a
## representation.
##
## This port has no spatial index, so the cell tests are linear in the vertex
## count and `is_valid` is quadratic. That is fine for the loop sizes a
## coverer or a containment test usually sees, and slow for very large ones.
S2Loop := { vertices : List(S2Point), origin_inside : Bool, bound : S2LatLngRect }.{

	## The loop through the given vertices, in order.
	from_points : List(S2Point) -> S2Loop
	from_points = |vertices| {
		origin_inside = S2Boundary.compute_origin_inside(vertices)
		{
			vertices: vertices,
			origin_inside: origin_inside,
			bound: S2Boundary.compute_bound(vertices, origin_inside),
		}
	}

	## The loop through the given positions, in order.
	from_lat_lngs : List(S2LatLng) -> S2Loop
	from_lat_lngs = |points| S2Loop.from_points(points.map(S2LatLng.to_point))

	## The loop through the four vertices of the cell, in the cell's
	## counterclockwise order, as upstream's `S2Loop(const S2Cell&)` builds
	## it.
	##
	## The loop and the cell do not contain exactly the same points. A cell
	## contains its whole boundary, so a vertex shared by four cells is in all
	## four, but it is in only one of the four loops made from them. The
	## loop's bound comes from its edges, as for any loop, and so can be
	## tighter than `S2LatLngRect.from_cell`.
	from_cell : S2Cell -> S2Loop
	from_cell = |cell| S2Loop.from_points([cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3)])

	## A regular polygon of `num_vertices` vertices, each at the distance
	## `radius` from `center`. Upstream's `S2Loop::MakeRegularLoop`.
	##
	## The vertices run counterclockwise around `center`. The first one is in
	## the direction of the first axis of `S2Point.frame(center)`.
	make_regular_loop : S2Point, S1Angle, U64 -> S2Loop
	make_regular_loop = |center, radius, num_vertices|
		S2Loop.make_regular_loop_in_frame(center.frame(), radius, num_vertices)

	## Like `make_regular_loop`, but centred on the third axis of the frame,
	## with the first vertex in the direction of its first axis. The frame is
	## the triple of column vectors that `S2Point.frame` returns. This lets a
	## caller rotate the loop.
	make_regular_loop_in_frame : (S2Point, S2Point, S2Point), S1Angle, U64 -> S2Loop
	make_regular_loop_in_frame = |frame, radius, num_vertices| {
		r_and_z = radius.sin_cos()
		step = 2.0 * F64.pi / num_vertices.to_f64()
		var $vertices = []
		var $i = 0
		while $i < num_vertices {
			a = S1Angle.from_radians($i.to_f64() * step).sin_cos()
			p = S2Point.new(r_and_z.sin * a.cos, r_and_z.sin * a.sin, r_and_z.cos)
			$vertices = $vertices.append(S2Point.from_frame(frame, p).normalize())
			$i = $i + 1
		}
		S2Loop.from_points($vertices)
	}

	## The loop containing nothing.
	empty : () -> S2Loop
	empty = || S2Loop.from_points([S2Boundary.empty_vertex()])

	## The loop containing the whole sphere.
	full : () -> S2Loop
	full = || S2Loop.from_points([S2Boundary.full_vertex()])

	## The vertices of the loop, in order. The edge from the last vertex back
	## to the first is implied.
	vertices : S2Loop -> List(S2Point)
	vertices = |loop| loop.vertices

	## The number of vertices. The empty loop and the full loop each have one.
	num_vertices : S2Loop -> U64
	num_vertices = |loop| loop.vertices.len()

	## The `i`-th vertex, wrapping so that `vertex(n)` is `vertex(0)`.
	vertex : S2Loop, U64 -> S2Point
	vertex = |loop, index| {
		if loop.vertices.is_empty() {
			return S2Point.zero()
		}
		loop.vertices.get(index % loop.vertices.len()) ?? S2Point.zero()
	}

	## The bounding rectangle of the loop, valid for its edges as well as its
	## vertices.
	rect_bound : S2Loop -> S2LatLngRect
	rect_bound = |loop| loop.bound

	## The bounding cap of the loop.
	cap_bound : S2Loop -> S2Cap
	cap_bound = |loop| loop.bound.cap_bound()

	## True for a one-vertex loop whose vertex has `z >= 0`.
	is_empty : S2Loop -> Bool
	is_empty = |loop| loop.is_empty_or_full() and !loop.origin_inside

	## True for a one-vertex loop whose vertex has `z < 0`.
	is_full : S2Loop -> Bool
	is_full = |loop| loop.is_empty_or_full() and loop.origin_inside

	## True for any one-vertex loop, which is the empty or the full loop.
	is_empty_or_full : S2Loop -> Bool
	is_empty_or_full = |loop| loop.vertices.len() == 1

	## True when the loop is a well-formed simple polygon: when
	## `find_validation_error` finds nothing.
	is_valid : S2Loop -> Bool
	is_valid = |loop| loop.find_validation_error().is_ok()

	## The first reason the loop is not well formed, if there is one.
	##
	## These are the checks of upstream's `S2Loop::FindValidationError`, in
	## its order:
	##
	## - `NotUnitLength(i)`: vertex `i` is not unit length.
	## - `NotEnoughVertices`: the loop has fewer than three vertices and is
	##   not the empty or the full loop.
	## - `DegenerateEdge(i)`: edge `i` joins a vertex to itself.
	## - `AntipodalVertices(i, j)`: adjacent vertices `i` and `j` are
	##   antipodal.
	## - `DuplicateVertex(i, j)`: edges `i` and `j` end at the same vertex.
	## - `SelfIntersection(i, j)`: edges `i` and `j` cross.
	##
	## Edge `i` runs from vertex `i` to vertex `i + 1`. Upstream finds the
	## last two kinds through its spatial index. This port compares every
	## pair of edges in order, which costs O(n^2), so for a loop with several
	## such faults it can name a different pair than upstream does.
	find_validation_error : S2Loop -> Try({}, [NotUnitLength(U64), NotEnoughVertices, DegenerateEdge(U64), AntipodalVertices(U64, U64), DuplicateVertex(U64, U64), SelfIntersection(U64, U64)])
	find_validation_error = |loop| {
		n = loop.vertices.len()
		var $k = 0
		while $k < n {
			if !loop.vertex($k).is_unit_length() {
				return Err(NotUnitLength($k))
			}
			$k = $k + 1
		}
		if n < 3 {
			return if (loop.is_empty_or_full()) Ok({}) else Err(NotEnoughVertices)
		}
		var $i = 0
		while $i < n {
			a = loop.vertex($i)
			b = loop.vertex($i + 1)
			if a == b {
				return Err(DegenerateEdge($i))
			}
			if a == -b {
				return Err(AntipodalVertices($i, ($i + 1) % n))
			}
			$i = $i + 1
		}
		# Two edges that share a vertex have a crossing sign of 0. Only the
		# pair that ends at the shared vertex reports it, as upstream does.
		var $a = 0
		while $a < n {
			var $b = $a + 1
			while $b < n {
				sign = S2Edge.crossing_sign(loop.vertex($a), loop.vertex($a + 1), loop.vertex($b), loop.vertex($b + 1))
				if sign > 0 {
					return Err(SelfIntersection($a, $b))
				}
				if sign == 0 and loop.vertex($a + 1) == loop.vertex($b + 1) {
					return Err(DuplicateVertex($a, $b))
				}
				$b = $b + 1
			}
			$a = $a + 1
		}
		Ok({})
	}

	## True when the point is inside the loop.
	##
	## Counts how many times the edge from S2's fixed reference point to `p`
	## crosses the loop's boundary; an odd count means inside. The crossing
	## test is exact, so the answer is consistent even for points on an edge.
	contains_point : S2Loop, S2Point -> Bool
	contains_point = |loop, p| {
		if loop.is_empty() {
			return Bool.False
		}
		if loop.is_full() {
			return Bool.True
		}
		if !loop.bound.contains_point(p) {
			return Bool.False
		}
		S2Boundary.crossing_parity(loop.vertices, p, loop.origin_inside)
	}

	## The area of the loop's interior in steradians, in `[0, 4pi]`.
	##
	## Follows upstream's `S2Loop::GetArea`. When the area is so close to
	## zero that rounding could flip its sign, the turning angle decides: a
	## nearly degenerate loop that runs counterclockwise, and so contains
	## almost nothing, has an area near 0, and one that runs clockwise, and so
	## contains almost everything, has an area near `4pi`.
	area : S2Loop -> F64
	area = |loop| {
		if loop.is_empty_or_full() {
			return if (loop.is_full()) 4.0 * F64.pi else 0.0
		}
		signed = S2Boundary.signed_area(loop.vertices)
		if signed < 0.0 {
			signed + 4.0 * F64.pi
		} else {
			signed
		}
	}

	## The centroid of the loop's interior, scaled by its area so that the
	## centroids of several loops can be summed.
	##
	## Follows upstream's `S2Loop::GetCentroid`. The result is not a unit
	## vector. The empty and full loops give the zero vector.
	centroid : S2Loop -> S2Point
	centroid = |loop| S2Boundary.surface_centroid(loop.vertices)

	## The total angle turned while walking the loop once, in radians: its
	## geodesic curvature, equal to `2pi` less its area.
	##
	## Positive for a counterclockwise loop and negative for a clockwise one,
	## so its sign says which side of the edges the interior is on. This is
	## the robust way to ask, since it does not go through the area.
	##
	## Follows upstream's `S2Loop::GetCurvature`. The empty loop gives `2pi`
	## and the full loop `-2pi`. Repeated vertices and spikes are pruned
	## first, and a loop that is nothing else gives exactly `2pi`. Any other
	## loop gives a value in `(-2pi, 2pi)`. The turn angles are summed in an
	## order fixed by the vertices themselves, so rotating the loop does not
	## change the result and reversing it negates the result exactly.
	turning_angle : S2Loop -> F64
	turning_angle = |loop| {
		if loop.is_empty_or_full() {
			return if (loop.is_full()) -2.0 * F64.pi else 2.0 * F64.pi
		}
		S2Boundary.curvature(loop.vertices)
	}

	## The largest error `turning_angle` can make for this loop, upstream's
	## `GetCurvatureMaxError`: 11.25 machine epsilons per vertex.
	curvature_max_error : S2Loop -> F64
	curvature_max_error = |loop| S2Boundary.curvature_max_error(loop.vertices)

	## The area of the loop's interior from its turning angle: `2pi` less
	## `turning_angle`. Upstream's `S2::GetApproxArea`.
	##
	## Cheaper than `area`, and less accurate for small loops: its absolute
	## error is about `curvature_max_error`. The empty loop gives 0 and the
	## full loop `4pi`.
	approx_area : S2Loop -> F64
	approx_area = |loop| 2.0 * F64.pi - loop.turning_angle()

	## The total length of the loop's edges, the closing edge included.
	## Upstream's `S2::GetPerimeter`. The empty and full loops give zero.
	perimeter : S2Loop -> S1Angle
	perimeter = |loop| {
		n = loop.vertices.len()
		if n <= 1 {
			return S1Angle.zero()
		}
		var $total = S1Angle.zero()
		var $i = 0
		while $i < n {
			$total = $total + loop.vertex($i).angle_to(loop.vertex($i + 1))
			$i = $i + 1
		}
		$total
	}

	## The distance from `x` to the loop's interior: zero when the loop
	## contains `x`, otherwise the distance to the boundary. The empty loop
	## gives `S1Angle.infinity()`. Upstream's `S2Loop::GetDistance`.
	##
	## Upstream finds the nearest edge with its closest-edge query. This port
	## scans every edge, so the cost is linear in the vertex count.
	distance_to_point : S2Loop, S2Point -> S1Angle
	distance_to_point = |loop, x|
		if loop.contains_point(x) {
			S1Angle.zero()
		} else {
			loop.distance_to_boundary(x)
		}

	## The distance from `x` to the nearest point of the loop's edges.
	## Upstream's `GetDistanceToBoundary`. The empty and full loops have no
	## boundary, so they give `S1Angle.infinity()`. The cost is linear in the
	## vertex count.
	distance_to_boundary : S2Loop, S2Point -> S1Angle
	distance_to_boundary = |loop, x|
		match closest_edge(loop, x) {
			Ok(edge) => edge.distance.to_angle()
			Err(NoEdges) => S1Angle.infinity()
		}

	## `x` itself when the loop contains it, otherwise the nearest point of
	## the loop's boundary. The empty loop gives `x`. Upstream's
	## `S2Loop::Project`. The result may or may not be inside the loop.
	project : S2Loop, S2Point -> S2Point
	project = |loop, x|
		if loop.contains_point(x) {
			x
		} else {
			loop.project_to_boundary(x)
		}

	## The nearest point of the loop's boundary to `x`. The empty and full
	## loops have no boundary, so they give `x`. Upstream's
	## `ProjectToBoundary`. The cost is linear in the vertex count.
	project_to_boundary : S2Loop, S2Point -> S2Point
	project_to_boundary = |loop, x|
		match closest_edge(loop, x) {
			Ok(edge) => S2Edge.project(x, edge.v0, edge.v1)
			Err(NoEdges) => x
		}

	## True when the loop encloses at most half the sphere, which is the
	## orientation S2 treats as canonical.
	##
	## A loop whose longitude span is less than pi is normalized. Otherwise
	## the turning angle must be at least the negated error bound of the
	## turning angle, which grows with the vertex count, so that a hemisphere
	## always counts as normalized. This is upstream's `IsNormalized`.
	is_normalized : S2Loop -> Bool
	is_normalized = |loop| {
		if loop.bound.lng().length() < F64.pi {
			return Bool.True
		}
		loop.turning_angle() >= -S2Boundary.curvature_max_error(loop.vertices)
	}

	## The loop with the same boundary but the opposite interior.
	##
	## Reverses the whole vertex list, so `ABCD` becomes `DCBA`, as upstream's
	## `Invert` does. The empty and full loops swap.
	invert : S2Loop -> S2Loop
	invert = |loop| {
		if loop.is_empty_or_full() {
			return if (loop.is_full()) S2Loop.empty() else S2Loop.full()
		}
		S2Loop.from_points(loop.vertices.rev())
	}

	## The loop in canonical orientation, inverted if it was enclosing more
	## than half the sphere.
	normalized : S2Loop -> S2Loop
	normalized = |loop| if loop.is_normalized() {
		loop
	} else {
		loop.invert()
	}

	## True when the two loops have the same boundary: the same vertices in
	## the same order, no matter which one each starts from.
	boundary_equals : S2Loop, S2Loop -> Bool
	boundary_equals = |loop, other| {
		n = loop.num_vertices()
		if n != other.num_vertices() {
			return Bool.False
		}
		# Equal vertex counts mean that if one loop is a sentinel, so is the
		# other.
		if loop.is_empty_or_full() {
			return loop.is_empty() == other.is_empty()
		}
		var $found = Bool.False
		var $offset = 0
		while $offset < n {
			if loop.vertex($offset) == other.vertex(0) {
				var $same = Bool.True
				var $i = 0
				while $i < n {
					if loop.vertex($i + $offset) != other.vertex($i) {
						$same = Bool.False
					}
					$i = $i + 1
				}
				if $same {
					$found = Bool.True
				}
			}
			$offset = $offset + 1
		}
		$found
	}

	## True when the two loops have the same boundary to within `max_error`:
	## the same number of vertices, in the same cyclic order, each within
	## `max_error` of its partner. Upstream's `BoundaryApproxEquals`.
	##
	## The empty and full loops are not near each other. Since vertices match
	## only approximately, every starting offset is tried, so the cost is
	## O(n^2) at worst.
	boundary_approx_equals : S2Loop, S2Loop, S1Angle -> Bool
	boundary_approx_equals = |loop, other, max_error| {
		n = loop.num_vertices()
		if n != other.num_vertices() {
			return Bool.False
		}
		if loop.is_empty_or_full() {
			return loop.is_empty() == other.is_empty()
		}
		near = |a, b| a.angle_to(b) <= max_error
		var $offset = 0
		while $offset < n {
			if near(loop.vertex($offset), other.vertex(0)) {
				var $same = Bool.True
				var $i = 0
				while $same and $i < n {
					if !near(loop.vertex($i + $offset), other.vertex($i)) {
						$same = Bool.False
					}
					$i = $i + 1
				}
				if $same {
					return Bool.True
				}
			}
			$offset = $offset + 1
		}
		Bool.False
	}

	## True when the two boundaries stay within `max_error` of each other
	## along their whole length. Upstream's `BoundaryNear`.
	##
	## The loops may have different vertex counts. Picture two cars driving
	## once around the two loops, never backwards: the answer is true when
	## they can always stay within `max_error` of each other. The empty loop
	## is near only the empty loop, and the full loop only the full loop.
	##
	## Each starting vertex of this loop is tried with a search over pairs of
	## positions, so the cost is O(n^2 m) at worst for loops of `n` and `m`
	## vertices.
	boundary_near : S2Loop, S2Loop, S1Angle -> Bool
	boundary_near = |loop, other, max_error| {
		if loop.is_empty_or_full() or other.is_empty_or_full() {
			return (loop.is_empty() and other.is_empty()) or (loop.is_full() and other.is_full())
		}
		var $offset = 0
		while $offset < loop.num_vertices() {
			if match_boundaries(loop, other, $offset, max_error) {
				return Bool.True
			}
			$offset = $offset + 1
		}
		Bool.False
	}

	## True when this loop contains every point of the other one.
	##
	## Exact where the boundaries touch: at a shared vertex the local order of
	## the four edges around it decides, so a loop does contain another that
	## runs along part of its boundary in the same direction.
	##
	## Costs the product of the two vertex counts, since this port has no
	## spatial index.
	contains : S2Loop, S2Loop -> Bool
	contains = |loop, other| {
		if loop.is_empty_or_full() or other.is_empty_or_full() {
			return loop.is_full() or other.is_empty()
		}
		# The bound holds every point of a loop, so bounds that miss each
		# other rule containment out.
		if !loop.bound.intersects_rect(other.bound) {
			return Bool.False
		}
		rel = S2Boundary.relate(loop.vertices, other.vertices, Bool.False)
		if rel.crossing or !rel.wedges_contained {
			return Bool.False
		}
		if rel.shared {
			return Bool.True
		}
		# With no crossings and no shared vertices the loops are disjoint, one
		# holds the other, or between them they cover the sphere. The second
		# test is what tells that last case from real containment.
		loop.contains_point(other.vertex(0)) and !other.contains_point(loop.vertex(0))
	}

	## True when the two loops share any interior point.
	##
	## Touching along a boundary is not sharing: two loops that meet at a
	## vertex or run along a common edge without overlapping do not intersect.
	intersects : S2Loop, S2Loop -> Bool
	intersects = |loop, other| {
		if loop.is_empty_or_full() or other.is_empty_or_full() {
			return !loop.is_empty() and !other.is_empty()
		}
		if !loop.bound.intersects_rect(other.bound) {
			return Bool.False
		}
		rel = S2Boundary.relate(loop.vertices, other.vertices, Bool.False)
		if rel.crossing or rel.wedges_overlap {
			return Bool.True
		}
		if rel.shared {
			return Bool.False
		}
		loop.contains_point(other.vertex(0)) or other.contains_point(loop.vertex(0))
	}

	## True when this loop contains the other, given that the two are known to
	## be nested: disjoint, or one inside the other, and sharing no edge.
	##
	## Cheaper than `contains`, which has to look for crossings. This is the
	## test `S2Polygon.from_loops` uses to work out the nesting depths.
	contains_nested : S2Loop, S2Loop -> Bool
	contains_nested = |loop, other| {
		if loop.is_empty_or_full() or other.num_vertices() < 2 {
			return loop.is_full() or other.is_empty()
		}
		if !loop.bound.intersects_rect(other.bound) {
			return Bool.False
		}
		match S2Boundary.find_vertex(loop.vertices, other.vertex(1)) {
			Err(NotFound) => loop.contains_point(other.vertex(1))
			Ok(m) => S2Boundary.wedge_contains(
				loop.vertex(m + loop.num_vertices() - 1),
				loop.vertex(m),
				loop.vertex(m + 1),
				other.vertex(0),
				other.vertex(2),
			)
		}
	}

	## How this loop stands to the boundary of the other: `1` when it contains
	## that boundary, `-1` when it excludes it, `0` when the two boundaries
	## cross.
	##
	## `other_is_hole` names which side of the other loop its polygon calls
	## inside. It matters only where the two loops share an edge: a shared
	## edge running the same way belongs to a shell, and one running the
	## opposite way belongs to a hole.
	##
	## Neither loop may be empty. `S2Polygon` is the caller this exists for.
	compare_boundary : S2Loop, S2Loop, Bool -> I8
	compare_boundary = |loop, other, other_is_hole| {
		if loop.is_empty() or other.is_empty() {
			return -1
		}
		if !loop.bound.intersects_rect(other.bound) {
			return -1
		}
		# A full loop is treated as though it surrounded the sphere.
		if loop.is_full() {
			return 1
		}
		if other.is_full() {
			return -1
		}
		rel = S2Boundary.relate(loop.vertices, other.vertices, other_is_hole)
		if rel.crossing or (rel.semi_contained and rel.semi_excluded) {
			return 0
		}
		if rel.shared {
			if rel.semi_contained {
				1
			} else {
				-1
			}
		} else if loop.contains_point(other.vertex(0)) {
			1
		} else {
			-1
		}
	}

	## True when this loop contains the other's boundary, given that the two
	## boundaries are known not to cross.
	##
	## Cheaper than `compare_boundary`, which has to look for crossings.
	## `reverse_other` flips which side of the other loop counts as inside,
	## and matters only along shared edges.
	contains_non_crossing_boundary : S2Loop, S2Loop, Bool -> Bool
	contains_non_crossing_boundary = |loop, other, reverse_other| {
		if loop.is_empty() or other.is_empty() {
			return Bool.False
		}
		if !loop.bound.intersects_rect(other.bound) {
			return Bool.False
		}
		if loop.is_full() {
			return Bool.True
		}
		if other.is_full() {
			return Bool.False
		}
		match S2Boundary.find_vertex(loop.vertices, other.vertex(0)) {
			Err(NotFound) => loop.contains_point(other.vertex(0))
			Ok(m) => S2Boundary.wedge_contains_semiwedge(
				loop.vertex(m + loop.num_vertices() - 1),
				loop.vertex(m),
				loop.vertex(m + 1),
				other.vertex(1),
				reverse_other,
			)
		}
	}

	## True when the loop contains every point of the cell.
	##
	## The cell is inside when its centre is inside, no loop edge crosses its
	## boundary, and no loop vertex falls within it. The full loop contains
	## every cell. Its one vertex is a marker, not a point of a boundary.
	contains_cell : S2Loop, S2Cell -> Bool
	contains_cell = |loop, cell| {
		if loop.is_empty_or_full() {
			return loop.is_full()
		}
		if !loop.contains_point(cell.center()) {
			return Bool.False
		}
		if S2Boundary.crosses_cell_boundary(loop.vertices, cell) {
			return Bool.False
		}
		# No crossing means the loop lies wholly inside or wholly outside the
		# cell. A vertex inside puts it wholly inside, so the cell sticks out.
		!S2Boundary.cell_contains_any(cell, loop.vertices)
	}

	## True when the loop and the cell share any point.
	##
	## The empty loop meets no cell and the full loop meets every cell.
	may_intersect_cell : S2Loop, S2Cell -> Bool
	may_intersect_cell = |loop, cell| {
		if loop.is_empty_or_full() {
			return loop.is_full()
		}
		if loop.contains_point(cell.center()) {
			return Bool.True
		}
		if S2Boundary.cell_contains_any(cell, loop.vertices) {
			return Bool.True
		}
		S2Boundary.crosses_cell_boundary(loop.vertices, cell)
	}

	## A few cells that cover the loop: those of its bounding cap, as
	## upstream's `S2Loop::GetCellUnionBound` gives them.
	cell_union_bound : S2Loop -> List(S2CellId)
	cell_union_bound = |loop| loop.cap_bound().cell_union_bound()

	## True when the two loops have the same vertices to within `max_error`
	## radians.
	approx_eq : S2Loop, S2Loop, F64 -> Bool
	approx_eq = |loop, other, max_error| {
		if loop.vertices.len() != other.vertices.len() {
			return Bool.False
		}
		var $ok = Bool.True
		var $i = 0
		while $i < loop.vertices.len() {
			if !loop.vertex($i).approx_eq(other.vertex($i), max_error) {
				$ok = Bool.False
			}
			$i = $i + 1
		}
		$ok
	}

	is_eq : S2Loop, S2Loop -> Bool
	is_eq = |a, b| a.vertices == b.vertices

	to_inspect : S2Loop -> Str
	to_inspect = |loop| "S2Loop(${loop.vertices.len().to_str()} vertices)"
}

## The edge of the loop nearest to `x`, by a scan of every edge.
closest_edge : S2Loop, S2Point -> Try({ distance : S1ChordAngle, v0 : S2Point, v1 : S2Point }, [NoEdges])
closest_edge = |loop, x|
	if loop.is_empty_or_full() {
		Err(NoEdges)
	} else {
		S2Boundary.closest_edge([loop.vertices], x)
	}

## Upstream's `MatchBoundaries`: true when the two boundaries can be walked
## together, starting at vertex `a_offset` of `a` and vertex 0 of `b`, with
## each step keeping the next vertex of one loop within `max_error` of the
## current edge of the other.
##
## A state `(i, j)` counts the vertices passed on each loop. Where both loops
## can advance, only one choice may succeed, so the states wait on a stack,
## and a set keeps any state from being explored twice.
match_boundaries : S2Loop, S2Loop, U64, S1Angle -> Bool
match_boundaries = |a, b, a_offset, max_error| {
	na = a.num_vertices()
	nb = b.num_vertices()
	key = |i, j| i * (nb + 1) + j
	var $pending = [(0, 0)]
	var $done = Set.empty()
	while !$pending.is_empty() {
		(i, j) = $pending.last() ?? (0, 0)
		$pending = $pending.drop_last(1)
		if i == na and j == nb {
			return Bool.True
		}
		$done = $done.insert(key(i, j))
		io = if (i + a_offset >= na) i + a_offset - na else i + a_offset
		if i < na
			and !$done.contains(key(i + 1, j))
			and S2Edge.distance_to_edge(a.vertex(io + 1), b.vertex(j), b.vertex(j + 1)).to_angle() <= max_error {
			$pending = $pending.append((i + 1, j))
		}
		if j < nb
			and !$done.contains(key(i, j + 1))
			and S2Edge.distance_to_edge(b.vertex(j + 1), a.vertex(io), a.vertex(io + 1)).to_angle() <= max_error {
			$pending = $pending.append((i, j + 1))
		}
	}
	Bool.False
}

expect S2Loop.empty().is_empty()
expect S2Loop.full().is_full()
expect S2Loop.empty().is_empty_or_full()
expect S2Loop.empty().is_valid()
expect S2Loop.full().is_valid()
expect S2Loop.empty().area() == 0.0
expect S2Loop.full().area() == 4.0 * F64.pi
expect !S2Loop.empty().contains_point(S2Point.new(1.0, 0.0, 0.0))
expect S2Loop.full().contains_point(S2Point.new(1.0, 0.0, 0.0))
expect S2Loop.empty().invert() == S2Loop.full()
expect S2Loop.full().invert() == S2Loop.empty()
expect {
	# A counterclockwise triangle over one octant.
	loop = S2Loop.from_points(
		[S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)],
	)
	loop.is_valid() and (loop.area() - 0.5 * F64.pi).abs() < 1e-13
}
expect {
	# Reversing the triangle gives the rest of the sphere.
	loop = S2Loop.from_points(
		[S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, 1.0, 0.0)],
	)
	(loop.area() - 3.5 * F64.pi).abs() < 1e-13
}
expect {
	loop = S2Loop.from_points(
		[S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)],
	)
	loop.contains_point(S2Point.new(1.0, 1.0, 1.0).normalize())
		and !loop.contains_point(S2Point.new(-1.0, -1.0, -1.0).normalize())
}
expect {
	# A square around the origin of the lat-lng grid.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-10.0, -10.0),
		S2LatLng.from_degrees(-10.0, 10.0),
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(10.0, -10.0),
	])
	loop.is_valid()
		and loop.contains_point(S2LatLng.from_degrees(0.0, 0.0).to_point())
		and !loop.contains_point(S2LatLng.from_degrees(0.0, 20.0).to_point())
		and !loop.contains_point(S2LatLng.from_degrees(20.0, 0.0).to_point())
}
expect {
	# Its bound covers the loop, including the poleward bulge of the top edge.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-10.0, -10.0),
		S2LatLng.from_degrees(-10.0, 10.0),
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(10.0, -10.0),
	])
	bound = loop.rect_bound()
	bound.lat_hi().degrees() > 10.0 and bound.lat_lo().degrees() < -10.0
}
expect {
	# Area of a small square matches the flat approximation.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, 0.0),
	])
	expected = S1Angle.from_degrees(1.0).radians() * S1Angle.from_degrees(1.0).radians()
	(loop.area() - expected).abs() / expected < 1e-3
}
expect {
	# Gauss-Bonnet: the turning angle plus the enclosed area is 2 pi.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, 0.0),
	])
	(loop.turning_angle() + loop.area() - 2.0 * F64.pi).abs() < 1e-13 and loop.is_normalized()
}
expect {
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(1.0, 0.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(0.0, 1.0),
	])
	!loop.is_normalized() and loop.normalized().is_normalized()
}
expect {
	# Inverting swaps interior for exterior.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-10.0, -10.0),
		S2LatLng.from_degrees(-10.0, 10.0),
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(10.0, -10.0),
	])
	inverted = loop.invert()
	p = S2LatLng.from_degrees(0.0, 0.0).to_point()
	loop.contains_point(p) and !inverted.contains_point(p)
		and (loop.area() + inverted.area() - 4.0 * F64.pi).abs() < 1e-12
}
expect {
	# A bowtie crosses itself.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(0.0, 10.0),
		S2LatLng.from_degrees(10.0, 0.0),
	])
	!loop.is_valid()
}
expect {
	# Fewer than three vertices is not a loop, unless it is a sentinel.
	!S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)]).is_valid()
}
expect {
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-10.0, -10.0),
		S2LatLng.from_degrees(-10.0, 10.0),
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(10.0, -10.0),
	])
	c = loop.centroid()
	c.normalize().approx_eq(S2LatLng.from_degrees(0.0, 0.0).to_point(), 1e-12)
}
expect {
	# The equator as four edges of 90 degrees each, so the fan from vertex 0
	# needs an edge of 180 degrees unless the origin moves. The interior is the
	# northern hemisphere. The integral of position over a hemisphere is
	# (0, 0, pi), since the integral of cos(t) sin(t) dt over [0, pi/2] is 1/2
	# and the longitude range is 2pi.
	loop = S2Loop.from_points([
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(0.0, 1.0, 0.0),
		S2Point.new(-1.0, 0.0, 0.0),
		S2Point.new(0.0, -1.0, 0.0),
	])
	loop.centroid().approx_eq(S2Point.new(0.0, 0.0, F64.pi), 1e-12)
}
expect {
	# A loop around the north pole contains it, and its bound says so.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(80.0, 0.0),
		S2LatLng.from_degrees(80.0, 120.0),
		S2LatLng.from_degrees(80.0, -120.0),
	])
	loop.contains_point(S2Point.new(0.0, 0.0, 1.0))
		and loop.rect_bound().lat_hi().degrees() == 90.0
		and loop.rect_bound().lng().is_full()
}
expect {
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-10.0, -10.0),
		S2LatLng.from_degrees(-10.0, 10.0),
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(10.0, -10.0),
	])
	cell = S2Cell.from_lat_lng(S2LatLng.from_degrees(0.0, 0.0))
	loop.contains_cell(cell) and loop.may_intersect_cell(cell)
}
expect {
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-1.0, -1.0),
		S2LatLng.from_degrees(-1.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, -1.0),
	])
	# A whole face is far too big to be contained, but it does meet the loop.
	!loop.contains_cell(S2Cell.from_face(0)) and loop.may_intersect_cell(S2Cell.from_face(0))
}
expect {
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-1.0, -1.0),
		S2LatLng.from_degrees(-1.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, -1.0),
	])
	!loop.may_intersect_cell(S2Cell.from_face(3))
}
expect {
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-1.0, -1.0),
		S2LatLng.from_degrees(-1.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, -1.0),
	])
	loop.cap_bound().contains_point(S2LatLng.from_degrees(0.0, 0.0).to_point())
		and loop.approx_eq(loop, 1e-15)
}

expect {
	# The sentinels' one vertex is not a boundary point. The full loop's
	# vertex is the south pole, on face 5, and the empty loop's is the north
	# pole, on face 2.
	faces = [0, 1, 2, 3, 4, 5].map(S2Cell.from_face)
	faces.all(|cell| S2Loop.full().contains_cell(cell) and S2Loop.full().may_intersect_cell(cell))
		and faces.all(|cell| !S2Loop.empty().contains_cell(cell) and !S2Loop.empty().may_intersect_cell(cell))
}

expect {
	# A square, and a smaller one strictly inside it.
	outer = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-2.0, -2.0),
		S2LatLng.from_degrees(-2.0, 2.0),
		S2LatLng.from_degrees(2.0, 2.0),
		S2LatLng.from_degrees(2.0, -2.0),
	])
	inner = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(-1.0, -1.0),
		S2LatLng.from_degrees(-1.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, -1.0),
	])
	outer.contains(inner)
		and outer.contains_nested(inner)
		and !inner.contains(outer)
		and outer.intersects(inner)
		and inner.intersects(outer)
		and outer.compare_boundary(inner, Bool.False) == 1
		and inner.compare_boundary(outer, Bool.False) == -1
}
expect {
	# Two squares that overlap in one corner.
	a = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 2.0),
		S2LatLng.from_degrees(2.0, 2.0),
		S2LatLng.from_degrees(2.0, 0.0),
	])
	b = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, 3.0),
		S2LatLng.from_degrees(3.0, 3.0),
		S2LatLng.from_degrees(3.0, 1.0),
	])
	!a.contains(b) and !b.contains(a) and a.intersects(b) and b.intersects(a)
}
expect {
	# Two squares that share nothing.
	a = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(1.0, 0.0),
	])
	b = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(10.0, 10.0),
		S2LatLng.from_degrees(10.0, 11.0),
		S2LatLng.from_degrees(11.0, 11.0),
		S2LatLng.from_degrees(11.0, 10.0),
	])
	!a.contains(b)
		and !a.intersects(b)
		and a.compare_boundary(b, Bool.False) == -1
		and !a.boundary_equals(b)
}
expect {
	# A loop contains itself, and neither contains its own complement.
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
	])
	loop.contains(loop)
		and loop.boundary_equals(loop)
		and !loop.contains(loop.invert())
		and !loop.invert().contains(loop)
		and !loop.intersects(loop.invert())
}
expect {
	# Where a loop starts makes no difference to its boundary.
	a = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
	])
	b = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 1.0),
		S2LatLng.from_degrees(1.0, 1.0),
		S2LatLng.from_degrees(0.0, 0.0),
	])
	a.boundary_equals(b) and a.contains(b) and b.contains(a) and !a.is_eq(b)
}

expect {
	# Upstream's GetAreaConsistentWithSign: points on the equator within 90
	# degrees of longitude make a degenerate loop. Which way it runs decides
	# whether it contains almost nothing or almost everything, and the area
	# must agree: near 0 when normalized, near 4pi when not, with the north
	# pole inside only in the second case.
	agrees = |loop| {
		ccw = loop.is_normalized()
		expected = if (ccw) 0.0 else 4.0 * F64.pi
		(loop.area() - expected).abs() <= 1e-15
			and loop.contains_point(S2Point.new(0.0, 0.0, 1.0)) == !ccw
	}
	loop = S2Loop.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 10.0),
		S2LatLng.from_degrees(0.0, 20.0),
		S2LatLng.from_degrees(0.0, 30.0),
	])
	loop.is_valid() and agrees(loop) and agrees(loop.invert())
}
expect {
	# Upstream's CheckCurvatureInvariants: rotating the vertices leaves the
	# turning angle exactly the same, and reversing them negates it exactly.
	points = [
		S2LatLng.from_degrees(0.3, 0.1),
		S2LatLng.from_degrees(-1.7, 2.9),
		S2LatLng.from_degrees(0.9, 5.3),
		S2LatLng.from_degrees(3.1, 4.7),
		S2LatLng.from_degrees(2.2, 2.3),
		S2LatLng.from_degrees(4.9, 0.7),
		S2LatLng.from_degrees(1.3, -1.1),
	].map(S2LatLng.to_point)
	expected = S2Loop.from_points(points).turning_angle()
	n = points.len()
	var $ok = Bool.True
	var $i = 0
	while $i < n {
		rotated = S2Loop.from_points(points.drop_first($i).concat(points.take_first($i)))
		if rotated.turning_angle() != expected or rotated.invert().turning_angle() != -expected {
			$ok = Bool.False
		}
		$i = $i + 1
	}
	$ok
}
expect {
	# A loop made only of degeneracies has a turning angle of exactly 2pi:
	# upstream's PruneDegeneracies reduces "abcb" to nothing.
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(1.0, 0.0).to_point()
	c = S2LatLng.from_degrees(1.0, 1.0).to_point()
	S2Loop.from_points([a, b, c, b]).turning_angle() == 2.0 * F64.pi
}
expect {
	# Upstream's IsNormalized allows an error that grows with the vertex
	# count, about 2.5e-12 for 1000 vertices. Moving one vertex of a
	# 1000-vertex equator loop 1e-11 radians south adds about
	# 0.5 * (2 * 0.36 degrees) * 1e-11 = 6.3e-14 to the area of the northern
	# hemisphere, so the turning angle is about -6.3e-14: outside a fixed
	# bound of 1e-14, inside upstream's.
	var $points = [S2LatLng.from_radians(-1e-11, -F64.pi).to_point()]
	var $i = 1
	while $i < 1000 {
		$points = $points.append(S2LatLng.from_degrees(0.0, -180.0 + 0.36 * $i.to_f64()).to_point())
		$i = $i + 1
	}
	loop = S2Loop.from_points($points)
	angle = loop.turning_angle()
	angle < -5e-14 and angle > -8e-14 and loop.is_normalized() and loop.invert().is_normalized()
}
expect {
	# Upstream treats any one-vertex loop as empty or full: full when the
	# vertex is in the southern hemisphere, empty otherwise.
	south = S2Loop.from_points([S2LatLng.from_degrees(-30.0, 40.0).to_point()])
	north = S2Loop.from_points([S2LatLng.from_degrees(30.0, 40.0).to_point()])
	p = S2LatLng.from_degrees(10.0, 10.0).to_point()
	south.is_full()
		and south.is_valid()
		and south.contains_point(p)
		and south.area() == 4.0 * F64.pi
		and south.turning_angle() == -2.0 * F64.pi
		and north.is_empty()
		and !north.contains_point(p)
		and north.area() == 0.0
		and south.invert().is_empty()
		and north.invert().is_full()
}
expect {
	# Upstream's Invert reverses the whole vertex list: ABC becomes CBA.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	S2Loop.from_points([a, b, c]).invert().vertices() == [c, b, a]
}
expect {
	# A loop with vertex 2 exactly antipodal to vertex 0, over (0, h, h) and
	# then through (0, -1, 0) and (0, 0, -1), with h = sqrt(1/2). Use polar
	# angle t from the x axis and azimuth f, so a point is
	# (cos t, sin t cos f, sin t sin f) and its area element is sin t dt df.
	# The interior is t in [0, pi/2] and f in [pi/4, 3pi/2], plus t in
	# [pi/2, pi] and f in [pi/4, pi]. The integral of position is then
	# (pi/4) * (1, -(1 + 2h), 1 + 2h).
	h = 0.7071067811865476
	loop = S2Loop.from_points([
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(0.0, h, h),
		S2Point.new(-1.0, 0.0, 0.0),
		S2Point.new(0.0, -1.0, 0.0),
		S2Point.new(0.0, 0.0, -1.0),
	])
	k = F64.pi / 4.0 * (1.0 + 2.0 * h)
	loop.centroid().approx_eq(S2Point.new(F64.pi / 4.0, -k, k), 1e-12)
}

## True when `a` is within a few units in the last place of `b`.
close : F64, F64 -> Bool
close = |a, b| (a - b).abs() <= 1e-15 * b.abs()

# Upstream's S2LoopTestBase.MakeRegularLoop: four vertices 20 degrees from
# (80, 135). The vertices are from upstream through tools/s2_oracle.cc.
expect {
	loop = S2Loop.make_regular_loop(S2LatLng.from_degrees(80.0, 135.0).to_point(), S1Angle.from_degrees(20.0), 4)
	expected = [
		S2Point.new(-0.10592043631161428, 0.4547880263631654, 0.88427863948432794),
		S2Point.new(-0.45468293541276456, 0.11965015866898869, 0.88257989313994556),
		S2Point.new(-0.12484515031268675, -0.22402243973886438, 0.96655451731231878),
		S2Point.new(0.22391734878846359, 0.11111542795531232, 0.96825326365670139),
	]
	loop.num_vertices() == 4 and List.map2(loop.vertices(), expected, |a, b| a.approx_eq(b, 1e-15)).all(|ok| ok)
}
# S2Loop(S2Cell) has the cell's vertices, and its own bound from its edges,
# upstream's S2Loop.S2CellConstructorAndContains. The values are from upstream.
# The bound and the areas below go through the trigonometry, which can differ
# from the C library in the last place, so they are compared to within that.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9926595690882924544))
	loop = S2Loop.from_cell(cell)
	copy = S2Loop.from_points(loop.vertices())
	expected = [
		S2Point.new(0.20882807852131757, -0.72858243420304736, 0.65234842698657325),
		S2Point.new(0.20889010772616387, -0.72879884853477228, 0.65208677433953655),
		S2Point.new(0.20919955365520837, -0.72874955125747487, 0.65204266600621352),
		S2Point.new(0.20913744096138975, -0.72853318082571805, 0.65230432715419162),
	]
	bound = loop.rect_bound()
	loop.vertices() == expected
		and close(bound.lat().lo(), 0.71027548816598163) and close(bound.lat().hi(), 0.71067883976107338)
		and close(bound.lng().lo(), -1.2916572505888528) and close(bound.lng().hi(), -1.2912469917194127)
		and copy.contains(loop) and loop.contains(copy)
		and !bound.contains_rect(S2LatLngRect.from_cell(cell))
}
# Upstream's S2Loop.IsValidDetectsInvalidLoops. The upstream messages, through
# tools/s2_oracle.cc, name the same edges:
# Non-empty, non-full loops must have at least 3 vertices.
# Non-empty, non-full loops must have at least 3 vertices.
# Edge 0 is degenerate (duplicate vertex).
# Edge 2 is degenerate (duplicate vertex).
# Edge 2 has duplicate vertex with edge 4.
# Edge 0 crosses edge 3.
# Vertices 0 and 1 are antipodal. Vertex 0 is not unit length.
expect S2Loop.from_lat_lngs([]).find_validation_error() == Err(NotEnoughVertices)
expect S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(21.0, 21.0)]).find_validation_error() == Err(NotEnoughVertices)
expect S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 21.0)]).find_validation_error() == Err(DegenerateEdge(0))
expect S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 21.0), S2LatLng.from_degrees(20.0, 20.0)]).find_validation_error() == Err(DegenerateEdge(2))
expect S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(21.0, 21.0), S2LatLng.from_degrees(21.0, 20.0), S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(20.0, 21.0)]).find_validation_error() == Err(DuplicateVertex(2, 4))
expect S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(21.0, 21.0), S2LatLng.from_degrees(21.0, 20.5), S2LatLng.from_degrees(21.0, 20.0), S2LatLng.from_degrees(20.0, 21.0)]).find_validation_error() == Err(SelfIntersection(0, 3))
expect S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]).find_validation_error() == Err(AntipodalVertices(0, 1))
expect S2Loop.from_points([S2Point.new(2.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]).find_validation_error() == Err(NotUnitLength(0))
expect S2Loop.from_points([S2Point.new(2.0, 0.0, 0.0)]).find_validation_error() == Err(NotUnitLength(0))
# Area, approximate area, perimeter and curvature error from upstream's
# GetArea, S2::GetApproxArea, S2::GetPerimeter and GetCurvatureMaxError.
expect {
	loop = S2Loop.from_lat_lngs([S2LatLng.from_degrees(-1.0, -1.0), S2LatLng.from_degrees(-1.0, 1.0), S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(1.0, -1.0)])
	close(loop.area(), 0.0012185315123719783)
		and loop.approx_area() == 0.0012185315123716123
		and loop.perimeter().radians() == 0.13961570619605679
		and loop.curvature_max_error() == 9.9920072216264089e-15
}
expect {
	loop = S2Loop.from_lat_lngs([S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(21.0, 21.0), S2LatLng.from_degrees(21.0, 20.5), S2LatLng.from_degrees(21.0, 20.0), S2LatLng.from_degrees(20.0, 21.0)])
	close(loop.area(), 12.566369579527354)
		and loop.approx_area() == 6.2831842723477678
		and loop.perimeter().radians() == 0.080522129010809462
		and loop.curvature_max_error() == 1.2490009027033011e-14
}
expect {
	loop = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(0.0, 20.0), S2LatLng.from_degrees(0.0, 30.0)])
	close(loop.area(), 2.2250738585072014e-308)
		and loop.approx_area() == 8.8817841970012523e-16
		and loop.perimeter().radians() == 0.69813170079773168
		and loop.curvature_max_error() == 7.4940054162198066e-15
}
# The empty and full loops have no perimeter. Upstream's S2::GetApproxArea of
# the bare one-vertex list gives 0 for both; the loop's own convention gives
# 0 and 4pi, as `area` does.
expect S2Loop.empty().perimeter().radians() == 0.0 and S2Loop.full().perimeter().radians() == 0.0
expect S2Loop.empty().curvature_max_error() == 2.4980018054066022e-15 and S2Loop.full().curvature_max_error() == 2.4980018054066022e-15
expect S2Loop.empty().approx_area() == 0.0 and S2Loop.full().approx_area() == 4.0 * F64.pi
# Upstream's S2LoopTestBase.DistanceMethods: the empty and full loops, then a
# vertex, a point on an edge, a point inside, and points outside that project
# to an edge and to a vertex of a square. Distances in radians, then Project
# and ProjectToBoundary, all from upstream.
expect {
	square = S2Loop.from_lat_lngs([S2LatLng.from_degrees(-1.0, -1.0), S2LatLng.from_degrees(-1.0, 1.0), S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(1.0, -1.0)])
	check = |loop, x, expected| {
		(distance, boundary, projected, on_boundary) = expected
		loop.distance_to_point(x).radians() == distance
			and loop.distance_to_boundary(x).radians() == boundary
			and loop.project(x) == projected
			and loop.project_to_boundary(x) == on_boundary
	}
	y = S2Point.new(0.0, 1.0, 0.0)
	inf = S1Angle.infinity().radians()
	check(S2Loop.empty(), y, (inf, inf, S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0)))
		and check(S2Loop.full(), y, (0.0, inf, S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0)))
		and check(square, S2LatLng.from_degrees(1.0, -1.0).to_point(), (0.0, 0.0, S2Point.new(0.99969541350954794, -0.017449748351250485, 0.017452406437283512), S2Point.new(0.99969541350954794, -0.017449748351250485, 0.017452406437283512)))
		and check(square, S2LatLng.from_degrees(0.5, 1.0).to_point(), (1.1102230246251565e-16, 1.1102230246251565e-16, S2Point.new(0.9998096240198644, 0.017451741903123544, 0.0087265354983739364), S2Point.new(0.9998096240198644, 0.017451741903123544, 0.0087265354983739364)))
		and check(square, S2LatLng.from_degrees(0.0, 0.5).to_point(), (0.0, 0.008726646259971646, S2Point.new(0.99996192306417131, 0.0087265354983739347, 0.0), S2Point.new(0.99984769515639116, 0.017452406437283512, -0.0)))
		and check(square, S2LatLng.from_degrees(0.0, -2.0).to_point(), (0.017453292519943292, 0.017453292519943292, S2Point.new(0.99984769515639138, -0.017452406437283512, 0.0), S2Point.new(0.99984769515639138, -0.017452406437283512, 0.0)))
		and check(square, S2LatLng.from_degrees(3.0, 4.0).to_point(), (0.062899979934787242, 0.062899979934787242, S2Point.new(0.99969541350954794, 0.017449748351250485, 0.017452406437283512), S2Point.new(0.99969541350954794, 0.017449748351250485, 0.017452406437283512)))
}
# Upstream's S2Loop.BoundaryNear, with BoundaryApproxEquals for the same
# pairs. Each pair is (approx_equals, near), from upstream.
expect {
	a = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(5.0, 5.0)])
	b = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.1), S2LatLng.from_degrees(-0.1, 9.9), S2LatLng.from_degrees(5.0, 5.2)])
	(a.boundary_approx_equals(b, S1Angle.from_degrees(0.5)), a.boundary_near(b, S1Angle.from_degrees(0.5))) == (Bool.True, Bool.True)
}
expect {
	a = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 7.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(3.0, 7.0), S2LatLng.from_degrees(5.0, 5.0)])
	b = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(5.0, 5.0), S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(3.0, 3.0), S2LatLng.from_degrees(1.0, 1.0)])
	(a.boundary_approx_equals(b, S1Angle.from_radians(1e-3)), a.boundary_near(b, S1Angle.from_radians(1e-3))) == (Bool.False, Bool.True)
}
expect {
	a = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 0.0)])
	b = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.9999, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 0.0)])
	(a.boundary_approx_equals(b, S1Angle.from_degrees(0.5)), a.boundary_near(b, S1Angle.from_degrees(0.5))) == (Bool.False, Bool.False)
}
expect {
	a = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.1, 0.0), S2LatLng.from_degrees(0.1, 1.0), S2LatLng.from_degrees(0.1, 2.0), S2LatLng.from_degrees(0.1, 3.0), S2LatLng.from_degrees(0.1, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.0), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(2.0, 4.1), S2LatLng.from_degrees(1.0, 4.1), S2LatLng.from_degrees(2.0, 4.2), S2LatLng.from_degrees(3.0, 4.2), S2LatLng.from_degrees(4.0, 4.2), S2LatLng.from_degrees(5.0, 4.2)])
	b = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.1, 2.0), S2LatLng.from_degrees(0.1, 1.0), S2LatLng.from_degrees(0.2, 2.0), S2LatLng.from_degrees(0.2, 3.0), S2LatLng.from_degrees(0.2, 4.0), S2LatLng.from_degrees(1.0, 4.1), S2LatLng.from_degrees(2.0, 4.0), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(5.0, 4.0)])
	(a.boundary_approx_equals(b, S1Angle.from_degrees(1.5)), a.boundary_near(b, S1Angle.from_degrees(1.5))) == (Bool.False, Bool.True)
}
expect {
	a = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.1, 0.0), S2LatLng.from_degrees(0.1, 1.0), S2LatLng.from_degrees(0.1, 2.0), S2LatLng.from_degrees(0.1, 3.0), S2LatLng.from_degrees(0.1, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.0), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(2.0, 4.1), S2LatLng.from_degrees(1.0, 4.1), S2LatLng.from_degrees(2.0, 4.2), S2LatLng.from_degrees(3.0, 4.2), S2LatLng.from_degrees(4.0, 4.2), S2LatLng.from_degrees(5.0, 4.2)])
	b = S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.1, 2.0), S2LatLng.from_degrees(0.1, 1.0), S2LatLng.from_degrees(0.2, 2.0), S2LatLng.from_degrees(0.2, 3.0), S2LatLng.from_degrees(0.2, 4.0), S2LatLng.from_degrees(1.0, 4.1), S2LatLng.from_degrees(2.0, 4.0), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(4.0, 4.0), S2LatLng.from_degrees(5.0, 4.0)])
	(a.boundary_approx_equals(b, S1Angle.from_degrees(0.5)), a.boundary_near(b, S1Angle.from_degrees(0.5))) == (Bool.False, Bool.False)
}
expect S2Loop.empty().boundary_near(S2Loop.empty(), S1Angle.from_radians(1e-15)) and !S2Loop.empty().boundary_near(S2Loop.full(), S1Angle.from_radians(1e-15))
expect S2Loop.full().boundary_approx_equals(S2Loop.full(), S1Angle.from_radians(1e-15)) and !S2Loop.full().boundary_approx_equals(S2Loop.empty(), S1Angle.from_radians(1e-15))
# GetCellUnionBound of the square, from upstream.
expect S2Loop.from_lat_lngs([S2LatLng.from_degrees(-1.0, -1.0), S2LatLng.from_degrees(-1.0, 1.0), S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(1.0, -1.0)]).cell_union_bound() == [1157425104234217472, 1148417904979476480, 1923037040887201792, 382805968326492160].map(S2CellId.from_id)

# The full loop is near only itself.
expect S2Loop.full().boundary_near(S2Loop.full(), S1Angle.from_radians(1e-15)) and !S2Loop.full().boundary_near(S2Loop.empty(), S1Angle.from_radians(1e-15))

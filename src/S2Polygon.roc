import S2Cap
import S2Cell
import S2LatLng
import S2LatLngRect
import S2Loop
import Internal/S2Boundary
import S2Point

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
	## upstream's `InitNested`, except that empty loops are dropped here.
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
	## These are the checks of upstream's `FindValidationError`, in its order.
	## Loop numbers are positions in `loops`.
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
			last = last_descendant(depths, $outer)
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

	## The bounding rectangle of the polygon, which bounds its shells.
	rect_bound : S2Polygon -> S2LatLngRect
	rect_bound = |polygon| polygon.bound

	## The bounding cap of the polygon.
	cap_bound : S2Polygon -> S2Cap
	cap_bound = |polygon| polygon.bound.cap_bound()

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
last_descendant : List(U64), U64 -> U64
last_descendant = |depths, k| {
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
	last = last_descendant(loops.map(|entry| entry.depth), best)
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

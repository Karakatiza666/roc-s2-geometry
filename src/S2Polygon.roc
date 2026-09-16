import S1Angle
import S2Cap
import S2Cell
import S2LatLng
import S2LatLngRect
import S2Loop
import S2Point

## A region bounded by loops, holes included.
##
## The loops are nested rather than oriented: a point is inside the polygon
## when an odd number of loops contain it, so a disc with a hole punched out of
## it is two counterclockwise loops, one inside the other. Each loop's depth
## records where it sits in that nesting, and its parity says what the loop
## bounds: an even depth is a shell, an odd depth a hole.
##
## `from_loops` puts any properly nested set of loops into that form, in either
## direction, so a hole may be given clockwise as upstream's oriented
## convention writes it.
##
##     shell = S2Loop.from_lat_lngs(outer)
##     hole = S2Loop.from_lat_lngs(inner)
##     polygon = S2Polygon.from_loops([shell, hole])
##     polygon.contains_polygon(other)
##
## A polygon is a region, so `S2RegionCoverer` covers it like any other.
##
## This port has no spatial index. Containment between two polygons costs the
## product of their vertex counts, which is fine for the polygon sizes a
## containment test usually sees and slow for very large ones.
S2Polygon := { loops : List(Nested), bound : S2LatLngRect }.{

	## One loop, and how deeply it is nested inside the others.
	Nested : { boundary : S2Loop, depth : U64 }

	## The polygon bounded by the given loops.
	##
	## The loops must be properly nested: any two of them are either disjoint
	## or one contains the other, and no two share an edge. Each is normalized
	## first, so direction does not matter.
	##
	## Empty loops are dropped. A loop enclosing more than half the sphere is
	## inverted by normalization, so pass such a region as the complement it
	## represents.
	from_loops : List(S2Loop) -> S2Polygon
	from_loops = |loops| {
		kept = loops.keep_if(|boundary| !boundary.is_empty()).map(
			|boundary| if boundary.is_full() {
				boundary
			} else {
				boundary.normalized()
			},
		)
		if kept.is_empty() {
			return S2Polygon.empty()
		}
		# The depth of a loop is the number of the others that contain it.
		var $nested = []
		for boundary in kept {
			var $depth = 0
			for outer in kept {
				if !(outer.is_eq(boundary)) and outer.contains_nested(boundary) {
					$depth = $depth + 1
				}
			}
			$nested = $nested.append({ boundary: boundary, depth: $depth })
		}
		S2Polygon.assemble($nested)
	}

	## The polygon bounded by a single loop.
	from_loop : S2Loop -> S2Polygon
	from_loop = |boundary| S2Polygon.from_loops([boundary])

	## The polygon containing nothing.
	empty : () -> S2Polygon
	empty = || { loops: [], bound: S2LatLngRect.empty() }

	## The polygon containing the whole sphere.
	full : () -> S2Polygon
	full = || {
		loops: [{ boundary: S2Loop.full(), depth: 0 }],
		bound: S2LatLngRect.full(),
	}

	## Order the loops shallowest first and compute the bound.
	##
	## Shallowest first is what makes loop 0 a top-level shell, which the
	## complement in `contains_polygon` is built by inverting.
	assemble : List(Nested) -> S2Polygon
	assemble = |nested| {
		var $ordered = []
		var $depth = 0
		while $ordered.len() < nested.len() {
			for entry in nested {
				if entry.depth == $depth {
					$ordered = $ordered.append(entry)
				}
			}
			$depth = $depth + 1
		}
		var $bound = S2LatLngRect.empty()
		for entry in $ordered {
			if entry.depth == 0 {
				$bound = $bound.union(entry.boundary.rect_bound())
			}
		}
		{ loops: $ordered, bound: $bound }
	}

	## The loops, shallowest first.
	loops : S2Polygon -> List(Nested)
	loops = |polygon| polygon.loops

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

	## `1` for a shell, `-1` for a hole: what the loop's area contributes.
	sign_of : Nested -> F64
	sign_of = |entry| if S2Polygon.is_hole(entry) {
		-1.0
	} else {
		1.0
	}

	is_empty : S2Polygon -> Bool
	is_empty = |polygon| polygon.loops.is_empty()

	is_full : S2Polygon -> Bool
	is_full = |polygon| polygon.loops.len() == 1 and polygon.loop_at(0).is_full()

	## True when every loop is valid and no two of them cross.
	##
	## Costs the square of the total vertex count.
	is_valid : S2Polygon -> Bool
	is_valid = |polygon| {
		var $ok = Bool.True
		for entry in polygon.loops {
			if !entry.boundary.is_valid() {
				$ok = Bool.False
			}
		}
		if !$ok {
			return Bool.False
		}
		# Nested loops never cross, so a crossing means the polygon is not
		# the nesting its depths claim.
		var $i = 0
		while $i < polygon.loops.len() {
			var $j = $i + 1
			while $j < polygon.loops.len() {
				a = polygon.loop_at($i)
				b = polygon.loop_at($j)
				if S2Loop.relate(a, b, Bool.False).crossing {
					$ok = Bool.False
				}
				$j = $j + 1
			}
			$i = $i + 1
		}
		$ok
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

	contains_lat_lng : S2Polygon, S2LatLng -> Bool
	contains_lat_lng = |polygon, position| polygon.contains_point(position.to_point())

	## The area of the polygon's interior in steradians, holes subtracted.
	area : S2Polygon -> F64
	area = |polygon| {
		var $total = 0.0
		for entry in polygon.loops {
			$total = $total + S2Polygon.sign_of(entry) * entry.boundary.area()
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
			$total = $total.plus(entry.boundary.centroid().times(S2Polygon.sign_of(entry)))
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
	contains_cell : S2Polygon, S2Cell -> Bool
	contains_cell = |polygon, cell| {
		if !polygon.contains_point(cell.center()) {
			return Bool.False
		}
		var $ok = Bool.True
		for entry in polygon.loops {
			if S2Loop.crosses_cell_boundary(entry.boundary, cell) {
				$ok = Bool.False
			}
			# A boundary wholly inside the cell leaves the cell sticking out
			# of the polygon, or covering a hole.
			for v in entry.boundary.vertices() {
				if cell.contains_point(v) {
					$ok = Bool.False
				}
			}
		}
		$ok
	}

	## True when the polygon and the cell share any point.
	may_intersect_cell : S2Polygon, S2Cell -> Bool
	may_intersect_cell = |polygon, cell| {
		if polygon.contains_point(cell.center()) {
			return Bool.True
		}
		var $hit = Bool.False
		for entry in polygon.loops {
			if S2Loop.crosses_cell_boundary(entry.boundary, cell) {
				$hit = Bool.True
			}
			for v in entry.boundary.vertices() {
				if cell.contains_point(v) {
					$hit = Bool.True
				}
			}
		}
		$hit
	}

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
		polygon.contains_boundary(other)
			and other.excludes_non_crossing_complement_shells(polygon)
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
		!(polygon.excludes_boundary(other)
			and other.excludes_non_crossing_shells(polygon))
	}

	## True when this polygon contains every point of the loop.
	contains_loop : S2Polygon, S2Loop -> Bool
	contains_loop = |polygon, boundary| polygon.contains_polygon(S2Polygon.from_loop(boundary))

	## True when this polygon and the loop share any interior point.
	intersects_loop : S2Polygon, S2Loop -> Bool
	intersects_loop = |polygon, boundary| polygon.intersects_polygon(S2Polygon.from_loop(boundary))

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
			if polygon.compare_boundary(entry.boundary, S2Polygon.is_hole(entry)) <= 0 {
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
			if polygon.compare_boundary(entry.boundary, S2Polygon.is_hole(entry)) >= 0 {
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
				and polygon.contains_non_crossing_boundary(entry.boundary, Bool.False) {
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
				if polygon.contains_non_crossing_boundary(entry.boundary, is_first) {
					$ok = Bool.False
				}
			}
			$index = $index + 1
		}
		$ok
	}

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

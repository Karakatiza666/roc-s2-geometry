import R1Interval
import S1Angle
import S1Interval
import S2Cap
import S2Cell
import S2Edge
import S2LatLng
import S2LatLngRect
import Internal/S2Math
import S2Point
import S2Predicates

## A simple closed polygon on the sphere: a sequence of vertices joined by
## geodesic edges, with the last vertex joined back to the first.
##
## The interior is the region to the left of the edges, so vertex order decides
## which side is inside. A loop that runs counterclockwise as seen from outside
## the sphere encloses less than half of it; `invert` swaps interior for
## exterior.
##
## Two one-vertex loops are special: `empty` contains nothing and `full`
## contains everything. They exist so that the empty and full regions have a
## representation.
##
## This port has no spatial index, so the cell tests are linear in the vertex
## count and `is_valid` is quadratic. That is fine for the loop sizes a
## coverer or a containment test usually sees, and slow for very large ones.
S2Loop := { vertices : List(S2Point), origin_inside : Bool, bound : S2LatLngRect }.{

	## The single vertex that marks the empty loop: the north pole.
	empty_vertex : () -> S2Point
	empty_vertex = || S2Point.new(0.0, 0.0, 1.0)

	## The single vertex that marks the full loop: the south pole.
	full_vertex : () -> S2Point
	full_vertex = || S2Point.new(0.0, 0.0, -1.0)

	## The loop through the given vertices, in order.
	from_points : List(S2Point) -> S2Loop
	from_points = |vertices| {
		origin_inside = S2Loop.compute_origin_inside(vertices)
		{
			vertices: vertices,
			origin_inside: origin_inside,
			bound: S2Loop.compute_bound(vertices, origin_inside),
		}
	}

	## The loop through the given positions, in order.
	from_lat_lngs : List(S2LatLng) -> S2Loop
	from_lat_lngs = |points| S2Loop.from_points(points.map(S2LatLng.to_point))

	## The loop containing nothing.
	empty : () -> S2Loop
	empty = || S2Loop.from_points([S2Loop.empty_vertex()])

	## The loop containing the whole sphere.
	full : () -> S2Loop
	full = || S2Loop.from_points([S2Loop.full_vertex()])

	vertices : S2Loop -> List(S2Point)
	vertices = |loop| loop.vertices

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

	is_empty : S2Loop -> Bool
	is_empty = |loop| loop.vertices == [S2Loop.empty_vertex()]

	is_full : S2Loop -> Bool
	is_full = |loop| loop.vertices == [S2Loop.full_vertex()]

	## True for the one-vertex `empty` and `full` sentinels.
	is_empty_or_full : S2Loop -> Bool
	is_empty_or_full = |loop| loop.is_empty() or loop.is_full()

	## True when the loop is a well-formed simple polygon.
	##
	## Checks vertex count, unit length, adjacent duplicates and antipodes,
	## and that no two edges cross. The crossing check compares every pair of
	## edges, so it costs O(n^2).
	is_valid : S2Loop -> Bool
	is_valid = |loop| {
		if loop.is_empty_or_full() {
			return Bool.True
		}
		n = loop.vertices.len()
		if n < 3 {
			return Bool.False
		}
		var $ok = Bool.True
		for v in loop.vertices {
			if !v.is_unit_length() {
				$ok = Bool.False
			}
		}
		var $i = 0
		while $i < n {
			a = loop.vertex($i)
			b = loop.vertex($i + 1)
			if a == b or a == -b {
				$ok = Bool.False
			}
			$i = $i + 1
		}
		if !$ok {
			return Bool.False
		}

		# No two edges may cross, and only adjacent edges may share a vertex.
		var $j = 0
		while $j < n {
			var $k = $j + 2
			while $k < n {
				if !($j == 0 and $k == n - 1) {
					crossing = S2Edge.crossing_sign(
						loop.vertex($j),
						loop.vertex($j + 1),
						loop.vertex($k),
						loop.vertex($k + 1),
					)
					if crossing >= 0 {
						$ok = Bool.False
					}
				}
				$k = $k + 1
			}
			$j = $j + 1
		}
		$ok
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
		S2Loop.crossing_parity(loop.vertices, p, loop.origin_inside)
	}

	## The area of the loop's interior in steradians, in `[0, 4pi]`.
	area : S2Loop -> F64
	area = |loop| {
		if loop.is_empty() {
			return 0.0
		}
		if loop.is_full() {
			return 4.0 * F64.pi
		}
		if loop.vertices.len() < 3 {
			return 0.0
		}
		signed = S2Loop.signed_area(loop.vertices)
		adjusted = if signed < 0.0 {
			signed + 4.0 * F64.pi
		} else {
			signed
		}
		adjusted.max(0.0).min(4.0 * F64.pi)
	}

	## The centroid of the loop's interior, scaled by its area so that the
	## centroids of several loops can be summed.
	centroid : S2Loop -> S2Point
	centroid = |loop| {
		if loop.vertices.len() < 3 {
			return S2Point.zero()
		}
		origin = loop.vertex(0)
		var $sum = S2Point.zero()
		var $i = 1
		while $i + 1 < loop.vertices.len() {
			$sum = $sum + S2Point.true_centroid(origin, loop.vertex($i), loop.vertex($i + 1))
			$i = $i + 1
		}
		$sum
	}

	## The total angle turned while walking the loop once, in radians.
	##
	## `2pi` for a small counterclockwise loop, `-2pi` for a small clockwise
	## one, so its sign says which side of the edges the interior is on. This
	## is the robust way to ask, since it does not go through the area.
	turning_angle : S2Loop -> F64
	turning_angle = |loop| {
		if loop.is_empty() {
			return 2.0 * F64.pi
		}
		if loop.is_full() {
			return -2.0 * F64.pi
		}
		if loop.vertices.len() < 3 {
			return 0.0
		}
		n = loop.vertices.len()
		var $sum = 0.0
		var $i = 0
		while $i < n {
			$sum = $sum
				+ S2Loop.turn_angle(loop.vertex($i), loop.vertex($i + 1), loop.vertex($i + 2))
			$i = $i + 1
		}
		$sum
	}

	## The angle turned at vertex `b` when walking from `a` to `c`, positive
	## for a left turn.
	turn_angle : S2Point, S2Point, S2Point -> F64
	turn_angle = |a, b, c| {
		outgoing = b.robust_cross(c)
		incoming = a.robust_cross(b)
		angle = outgoing.angle_to(incoming).radians()
		if S2Predicates.sign(a, b, c) > 0 {
			angle
		} else {
			-angle
		}
	}

	## True when the loop encloses at most half the sphere, which is the
	## orientation S2 treats as canonical.
	is_normalized : S2Loop -> Bool
	is_normalized = |loop| loop.turning_angle() >= -1e-14

	## The loop with the same boundary but the opposite interior.
	##
	## Reverses the vertex order, keeping the first vertex first, which is
	## what upstream's `Invert` does.
	invert : S2Loop -> S2Loop
	invert = |loop| {
		if loop.is_empty() {
			return S2Loop.full()
		}
		if loop.is_full() {
			return S2Loop.empty()
		}
		if loop.vertices.is_empty() {
			return loop
		}
		first = loop.vertex(0)
		S2Loop.from_points([first].concat(loop.vertices.drop_first(1).rev()))
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
		rel = S2Loop.relate(loop, other, Bool.False)
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
		rel = S2Loop.relate(loop, other, Bool.False)
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
		match S2Loop.find_vertex(loop, other.vertex(1)) {
			Err(NotFound) => loop.contains_point(other.vertex(1))
			Ok(m) => S2Loop.wedge_contains(
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
		rel = S2Loop.relate(loop, other, other_is_hole)
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
		match S2Loop.find_vertex(loop, other.vertex(0)) {
			Err(NotFound) => loop.contains_point(other.vertex(0))
			Ok(m) => S2Loop.wedge_contains_semiwedge(
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
	## boundary, and no loop vertex falls within it.
	contains_cell : S2Loop, S2Cell -> Bool
	contains_cell = |loop, cell| {
		if !loop.contains_point(cell.center()) {
			return Bool.False
		}
		if S2Loop.crosses_cell_boundary(loop, cell) {
			return Bool.False
		}
		# No crossing means the loop lies wholly inside or wholly outside the
		# cell. A vertex inside puts it wholly inside, so the cell sticks out.
		var $vertex_inside = Bool.False
		for v in loop.vertices {
			if cell.contains_point(v) {
				$vertex_inside = Bool.True
			}
		}
		!$vertex_inside
	}

	## True when the loop and the cell share any point.
	may_intersect_cell : S2Loop, S2Cell -> Bool
	may_intersect_cell = |loop, cell| {
		if loop.contains_point(cell.center()) {
			return Bool.True
		}
		var $hit = Bool.False
		for v in loop.vertices {
			if cell.contains_point(v) {
				$hit = Bool.True
			}
		}
		if $hit {
			return Bool.True
		}
		S2Loop.crosses_cell_boundary(loop, cell)
	}

	## True when any loop edge meets any of the cell's four edges.
	crosses_cell_boundary : S2Loop, S2Cell -> Bool
	crosses_cell_boundary = |loop, cell| {
		n = loop.vertices.len()
		if n < 2 {
			return Bool.False
		}
		var $hit = Bool.False
		var $i = 0
		while $i < n {
			a = loop.vertex($i)
			b = loop.vertex($i + 1)
			var $k = 0
			while $k < 4 {
				if S2Edge.crossing_sign(a, b, cell.vertex($k), cell.vertex(($k + 1) % 4)) >= 0 {
					$hit = Bool.True
				}
				$k = $k + 1
			}
			$i = $i + 1
		}
		$hit
	}

	## What one pass over every pair of edges found.
	##
	## The five answers cost one scan between them, so `contains`,
	## `intersects` and `compare_boundary` each ask for all five and read the
	## ones they need.
	Relation : {
		crossing : Bool,
		shared : Bool,
		wedges_contained : Bool,
		wedges_overlap : Bool,
		semi_contained : Bool,
		semi_excluded : Bool,
	}

	## Compare every edge of one loop against every edge of the other.
	##
	## A proper crossing is decisive on its own. Where the loops merely touch,
	## what matters is the order of the four edges around the shared vertex,
	## which is what the three wedge tests read.
	relate : S2Loop, S2Loop, Bool -> Relation
	relate = |loop, other, reverse_other| {
		n = loop.num_vertices()
		m = other.num_vertices()
		var $crossing = Bool.False
		var $shared = Bool.False
		var $wedges_contained = Bool.True
		var $wedges_overlap = Bool.False
		var $semi_contained = Bool.False
		var $semi_excluded = Bool.False
		var $i = 0
		while $i < n {
			a0 = loop.vertex($i)
			a1 = loop.vertex($i + 1)
			var $j = 0
			while $j < m {
				b0 = other.vertex($j)
				b1 = other.vertex($j + 1)
				sign = S2Edge.crossing_sign(a0, a1, b0, b1)
				if sign > 0 {
					$crossing = Bool.True
				} else if sign == 0 and a0 == b0 {
					# Every shared vertex is reached once this way: at the one
					# pair of edges that both start there.
					$shared = Bool.True
					a_prev = loop.vertex($i + n - 1)
					b_prev = other.vertex($j + m - 1)
					if !S2Loop.wedge_contains(a_prev, a0, a1, b_prev, b1) {
						$wedges_contained = Bool.False
					}
					if S2Loop.wedge_intersects(a_prev, a0, a1, b_prev, b1) {
						$wedges_overlap = Bool.True
					}
					if S2Loop.wedge_contains_semiwedge(a_prev, a0, a1, b1, reverse_other) {
						$semi_contained = Bool.True
					} else {
						$semi_excluded = Bool.True
					}
				}
				$j = $j + 1
			}
			$i = $i + 1
		}
		{
			crossing: $crossing,
			shared: $shared,
			wedges_contained: $wedges_contained,
			wedges_overlap: $wedges_overlap,
			semi_contained: $semi_contained,
			semi_excluded: $semi_excluded,
		}
	}

	## True when the wedge `a0 -> ab1 -> a2` contains the wedge
	## `b0 -> ab1 -> b2`, each wedge's inside being on its left.
	##
	## Containment means the edges run `a2 b2 b0 a0` counterclockwise around
	## the shared vertex, split here into two three-point tests.
	wedge_contains : S2Point, S2Point, S2Point, S2Point, S2Point -> Bool
	wedge_contains = |a0, ab1, a2, b0, b2|
		S2Predicates.ordered_ccw(a2, b2, b0, ab1)
			and S2Predicates.ordered_ccw(b0, a0, a2, ab1)

	## True when the two wedges at `ab1` share interior rays.
	##
	## Written as the negation of "disjoint" on purpose: the positive form is
	## the one that gets the degenerate cases wrong.
	wedge_intersects : S2Point, S2Point, S2Point, S2Point, S2Point -> Bool
	wedge_intersects = |a0, ab1, a2, b0, b2|
		!(S2Predicates.ordered_ccw(a0, b2, b0, ab1)
			and S2Predicates.ordered_ccw(b0, a2, a0, ab1))

	## True when the wedge `a0 -> ab1 -> a2` contains the rays just
	## counterclockwise of the edge `ab1 -> b2`, or just clockwise of it when
	## `reverse_b` is set.
	##
	## This is the test for containing a boundary rather than a region, so a
	## shared edge counts as contained exactly when the two loops disagree
	## about which side is inside.
	wedge_contains_semiwedge : S2Point, S2Point, S2Point, S2Point, Bool -> Bool
	wedge_contains_semiwedge = |a0, ab1, a2, b2, reverse_b|
		if b2 == a0 or b2 == a2 {
			(b2 == a0) == reverse_b
		} else {
			S2Predicates.ordered_ccw(a0, a2, b2, ab1)
		}

	## The index of the loop's first vertex equal to `p`, if it has one.
	find_vertex : S2Loop, S2Point -> Try(U64, [NotFound])
	find_vertex = |loop, p| {
		var $found = Bool.False
		var $index = 0
		var $i = 0
		while $i < loop.num_vertices() {
			if !$found and loop.vertex($i) == p {
				$found = Bool.True
				$index = $i
			}
			$i = $i + 1
		}
		if $found {
			Ok($index)
		} else {
			Err(NotFound)
		}
	}

	## Whether the reference point lies inside the loop, which anchors every
	## later containment test.
	##
	## Found by answering "is vertex 1 inside?" twice: once from the wedge of
	## the two edges meeting there, which is always right, and once by
	## counting crossings while assuming the reference point is outside.
	## Disagreement means the assumption was wrong.
	compute_origin_inside : List(S2Point) -> Bool
	compute_origin_inside = |points| {
		n = points.len()
		if n < 3 {
			# Only the empty and full sentinels are meaningful here, and only
			# the full loop can contain the reference point.
			if n == 1 and (points.get(0) ?? S2Point.zero()) == S2Loop.full_vertex() {
				Bool.True
			} else {
				Bool.False
			}
		} else {
			v0 = points.get(0) ?? S2Point.zero()
			v1 = points.get(1) ?? S2Point.zero()
			v2 = points.get(2) ?? S2Point.zero()
			v1_inside =
				v0 != v1 and v2 != v1 and S2Predicates.angle_contains_vertex(v0, v1, v2)
			v1_inside != S2Loop.crossing_parity(points, v1, Bool.False)
		}
	}

	## Counts boundary crossings between the reference point and `p`.
	crossing_parity : List(S2Point), S2Point, Bool -> Bool
	crossing_parity = |points, p, origin_inside| {
		n = points.len()
		origin = S2Point.origin()
		var $inside = origin_inside
		var $i = 0
		while $i < n {
			a = points.get($i) ?? S2Point.zero()
			b = points.get(($i + 1) % n) ?? S2Point.zero()
			if S2Edge.edge_or_vertex_crossing(origin, p, a, b) {
				$inside = !$inside
			}
			$i = $i + 1
		}
		$inside
	}

	## The signed area swept by triangles from the first vertex, which is the
	## loop's area modulo `4pi`.
	signed_area : List(S2Point) -> F64
	signed_area = |points| {
		origin = points.get(0) ?? S2Point.zero()
		var $sum = 0.0
		var $i = 1
		while $i + 1 < points.len() {
			a = points.get($i) ?? S2Point.zero()
			b = points.get($i + 1) ?? S2Point.zero()
			$sum = $sum
				+ S2Point.triangle_area(origin, a, b) * S2Predicates.sign(origin, a, b).to_f64()
			$i = $i + 1
		}
		$sum
	}

	## The bounding rectangle of the loop's edges, not just its vertices.
	##
	## A geodesic edge bulges polewards of its endpoints, so each edge's own
	## maximum latitude is included when it falls inside that edge. A loop
	## containing a pole gets the full range of longitudes.
	compute_bound : List(S2Point), Bool -> S2LatLngRect
	compute_bound = |points, origin_inside| {
		n = points.len()
		if n == 0 {
			return S2LatLngRect.empty()
		}
		if n == 1 {
			return if (points.get(0) ?? S2Point.zero()) == S2Loop.full_vertex() {
				S2LatLngRect.full()
			} else {
				S2LatLngRect.empty()
			}
		}

		var $bound = S2LatLngRect.empty()
		var $i = 0
		while $i < n {
			a = points.get($i) ?? S2Point.zero()
			b = points.get(($i + 1) % n) ?? S2Point.zero()
			$bound = $bound.union(S2Loop.edge_bound(a, b))
			$i = $i + 1
		}

		# Rounding in the trigonometry above can shave the true bound.
		padded = $bound.expanded(S1Angle.from_radians(2.0e-15) |> S2Loop.uniform_margin)
		north = S2Loop.contains_pole(points, origin_inside, Bool.True)
		south = S2Loop.contains_pole(points, origin_inside, Bool.False)
		# A loop that reaches a pole covers every longitude there, and one
		# that reaches both covers every latitude between them as well.
		if north and south {
			S2LatLngRect.full()
		} else if north {
			S2LatLngRect.new(
				R1Interval.new(padded.lat().lo(), 0.5 * F64.pi),
				S1Interval.full(),
			)
		} else if south {
			S2LatLngRect.new(
				R1Interval.new(-0.5 * F64.pi, padded.lat().hi()),
				S1Interval.full(),
			)
		} else {
			padded
		}
	}

	## The same margin in latitude and longitude.
	uniform_margin : S1Angle -> S2LatLng
	uniform_margin = |angle| S2LatLng.from_radians(angle.radians(), angle.radians())

	## True when the loop contains the north or the south pole.
	contains_pole : List(S2Point), Bool, Bool -> Bool
	contains_pole = |points, origin_inside, north|
		S2Loop.crossing_parity(
			points,
			if north {
				S2Point.new(0.0, 0.0, 1.0)
			} else {
				S2Point.new(0.0, 0.0, -1.0)
			},
			origin_inside,
		)

	## The bounding rectangle of a single geodesic edge.
	edge_bound : S2Point, S2Point -> S2LatLngRect
	edge_bound = |a, b| {
		a_ll = S2LatLng.from_point(a)
		b_ll = S2LatLng.from_point(b)
		var $lat = R1Interval.from_point_pair(a_ll.lat_radians(), b_ll.lat_radians())
		lng = S1Interval.from_point_pair(a_ll.lng_radians(), b_ll.lng_radians())

		# The extreme latitudes of the edge's great circle are where the
		# +z direction projects into the circle's plane.
		n = a.robust_cross(b).normalize()
		horizontal = S2Point.new(-n.z() * n.x(), -n.z() * n.y(), 1.0 - n.z() * n.z())
		if horizontal.norm2() > 0.0 {
			peak = horizontal.normalize()
			for candidate in [peak, -peak] {
				if S2Loop.on_edge(a, b, candidate) {
					$lat = $lat.add_point(S2LatLng.latitude(candidate).radians())
				}
			}
		}
		S2LatLngRect.new($lat, lng)
	}

	## True when `c`, already on the edge's great circle, lies within the arc
	## from `a` to `b`.
	on_edge : S2Point, S2Point, S2Point -> Bool
	on_edge = |a, b, c| {
		n = a.cross(b)
		a.cross(c).dot(n) >= 0.0 and c.cross(b).dot(n) >= 0.0
	}

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

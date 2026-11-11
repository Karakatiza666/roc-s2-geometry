import /R1Interval
import /S1Angle
import /S1Interval
import /S2Cell
import /S2Edge
import /S2LatLng
import /S2LatLngRect
import /S2Point
import /S2Predicates
import /Internal/S2Math

## The machinery behind `S2Loop`, `S2Polygon` and `S2Polyline`: edge bounds,
## crossing parity, the wedge tests at a shared vertex, and the one pass over
## every pair of edges that the loop predicates read.
##
## Each function takes the vertices as a list, so that this module does not
## import `S2Loop` and the shape modules can all import it. A list of
## vertices is a closed loop here: the last vertex joins back to the first.
##
## Internal to this package.
S2Boundary := [].{

	## The single vertex that marks the empty loop: the north pole.
	empty_vertex : () -> S2Point
	empty_vertex = || S2Point.new(0.0, 0.0, 1.0)

	## The single vertex that marks the full loop: the south pole.
	full_vertex : () -> S2Point
	full_vertex = || S2Point.new(0.0, 0.0, -1.0)

	## The `i`-th vertex of the loop, wrapping so that vertex `n` is vertex 0.
	vertex_at : List(S2Point), U64 -> S2Point
	vertex_at = |points, index| {
		if points.is_empty() {
			return S2Point.zero()
		}
		points.get(index % points.len()) ?? S2Point.zero()
	}

	## True when any loop edge meets any of the cell's four edges.
	##
	## A loop with fewer than two vertices has no edges, so the empty and
	## full sentinels never cross.
	crosses_cell_boundary : List(S2Point), S2Cell -> Bool
	crosses_cell_boundary = |points, cell| {
		n = points.len()
		if n < 2 {
			return Bool.False
		}
		var $hit = Bool.False
		var $i = 0
		while $i < n {
			a = S2Boundary.vertex_at(points, $i)
			b = S2Boundary.vertex_at(points, $i + 1)
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

	## True when the cell contains any of the vertices.
	cell_contains_any : S2Cell, List(S2Point) -> Bool
	cell_contains_any = |cell, points| points.any(|v| cell.contains_point(v))

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
	relate : List(S2Point), List(S2Point), Bool -> Relation
	relate = |loop, other, reverse_other| {
		n = loop.len()
		m = other.len()
		var $crossing = Bool.False
		var $shared = Bool.False
		var $wedges_contained = Bool.True
		var $wedges_overlap = Bool.False
		var $semi_contained = Bool.False
		var $semi_excluded = Bool.False
		var $i = 0
		while $i < n {
			a0 = S2Boundary.vertex_at(loop, $i)
			a1 = S2Boundary.vertex_at(loop, $i + 1)
			var $j = 0
			while $j < m {
				b0 = S2Boundary.vertex_at(other, $j)
				b1 = S2Boundary.vertex_at(other, $j + 1)
				sign = S2Edge.crossing_sign(a0, a1, b0, b1)
				if sign > 0 {
					$crossing = Bool.True
				} else if sign == 0 and a0 == b0 {
					# Every shared vertex is reached once this way: at the one
					# pair of edges that both start there.
					$shared = Bool.True
					a_prev = S2Boundary.vertex_at(loop, $i + n - 1)
					b_prev = S2Boundary.vertex_at(other, $j + m - 1)
					if !S2Boundary.wedge_contains(a_prev, a0, a1, b_prev, b1) {
						$wedges_contained = Bool.False
					}
					if S2Boundary.wedge_intersects(a_prev, a0, a1, b_prev, b1) {
						$wedges_overlap = Bool.True
					}
					if S2Boundary.wedge_contains_semiwedge(a_prev, a0, a1, b1, reverse_other) {
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
	find_vertex : List(S2Point), S2Point -> Try(U64, [NotFound])
	find_vertex = |points, p| {
		var $found = Bool.False
		var $index = 0
		var $i = 0
		while $i < points.len() {
			if !$found and S2Boundary.vertex_at(points, $i) == p {
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
			# Only a one-vertex loop is meaningful here: it is the full loop
			# when its vertex is in the southern hemisphere, and the empty loop
			# otherwise, as upstream decides. Only the full loop contains the
			# reference point.
			n == 1 and (points.get(0) ?? S2Point.zero()).z() < 0.0
		} else {
			v0 = points.get(0) ?? S2Point.zero()
			v1 = points.get(1) ?? S2Point.zero()
			v2 = points.get(2) ?? S2Point.zero()
			v1_inside =
				v0 != v1 and v2 != v1 and S2Predicates.angle_contains_vertex(v0, v1, v2)
			v1_inside != S2Boundary.crossing_parity(points, v1, Bool.False)
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

	## The signed area of the loop: the area to its left when that is at most
	## `2pi`, and otherwise the negated area to its right. In `[-2pi, 2pi]`.
	##
	## Ports upstream's `S2::GetSignedArea`. The triangle sum is accurate for
	## small loops but can get the sign wrong when the area is near zero, so
	## in that case the turning angle, which follows `S2Predicates.sign`,
	## decides the sign. A counterclockwise loop gets a positive area and a
	## clockwise loop a negative one, and a loop made only of degeneracies
	## gets exactly zero.
	signed_area : List(S2Point) -> F64
	signed_area = |points| {
		max_error = S2Boundary.curvature_max_error(points)
		reduced = S2Math.remainder(S2Boundary.surface_area(points), 4.0 * F64.pi)
		area = if (reduced == -2.0 * F64.pi) 2.0 * F64.pi else reduced
		if area.abs() <= max_error {
			curvature = S2Boundary.curvature(points)
			if curvature == 2.0 * F64.pi {
				return 0.0
			}
			if area <= 0.0 and curvature > 0.0 {
				return S2Boundary.min_positive()
			}
			if area >= 0.0 and curvature < 0.0 {
				return -S2Boundary.min_positive()
			}
		}
		area
	}

	## The smallest positive normal `F64`, upstream's
	## `std::numeric_limits<double>::min()`.
	min_positive : () -> F64
	min_positive = || 2.2250738585072014e-308

	## The machine epsilon of `F64`, upstream's `DBL_EPSILON`.
	epsilon : () -> F64
	epsilon = || 2.220446049250313e-16

	## The oriented area of the loop, summed over a fan of triangles. It is
	## the area to the left of the loop, plus or minus a multiple of `4pi`.
	##
	## Ports upstream's `S2::GetSurfaceIntegralKahan` with `S2::SignedArea`,
	## using Kahan summation over the triangles of `surface_triangles`.
	surface_area : List(S2Point) -> F64
	surface_area = |points| {
		var $sum = (0.0, 0.0)
		for t in S2Boundary.surface_triangles(points) {
			$sum = S2Boundary.kahan_add($sum, S2Boundary.oriented_triangle_area(t.0, t.1, t.2))
		}
		$sum.0
	}

	## The centroid of the loop's interior, scaled by its area. It is the sum
	## of `S2Point.true_centroid` over the triangles of `surface_triangles`,
	## added plainly, as upstream does.
	##
	## Ports upstream's `S2::GetCentroid`. Either the interior or the negated
	## exterior is integrated, and the two are equal because the integral of
	## position over the whole sphere is zero. A list of fewer than three
	## points gives the zero vector.
	surface_centroid : List(S2Point) -> S2Point
	surface_centroid = |points| {
		var $sum = S2Point.zero()
		for t in S2Boundary.surface_triangles(points) {
			$sum = $sum.plus(S2Point.true_centroid(t.0, t.1, t.2))
		}
		$sum
	}

	## The oriented triangles that cover the loop, in the order that upstream's
	## `S2::GetSurfaceIntegral` visits them. Each point of the interior is
	## covered one more time than each point of the exterior, counting
	## clockwise triangles as negative.
	##
	## The triangles are a fan from vertex 0. When a fan edge would be nearly
	## 180 degrees long, and so unstable, the fan moves its origin to a point
	## well away from the edge, and adds the triangles that keep the sum
	## correct. A list of fewer than three points gives no triangles.
	surface_triangles : List(S2Point) -> List((S2Point, S2Point, S2Point))
	surface_triangles = |points| {
		n = points.len()
		if n < 3 {
			return []
		}
		max_length = F64.pi - 1e-5
		v0 = S2Boundary.vertex_at(points, 0)
		var $origin = v0
		var $triangles = []
		var $i = 1
		while $i + 1 < n {
			vi = S2Boundary.vertex_at(points, $i)
			next = S2Boundary.vertex_at(points, $i + 1)
			if next.angle_to($origin).radians() > max_length {
				old_origin = $origin
				if $origin == v0 {
					$origin = v0.robust_cross(vi).normalize()
				} else if vi.angle_to(v0).radians() < max_length {
					$origin = v0
				} else {
					$origin = v0.cross(old_origin)
					$triangles = $triangles.append((v0, old_origin, $origin))
				}
				$triangles = $triangles.append((old_origin, vi, $origin))
			}
			$triangles = $triangles.append(($origin, vi, next))
			$i = $i + 1
		}
		if $origin != v0 {
			last = S2Boundary.vertex_at(points, n - 1)
			$triangles = $triangles.append(($origin, last, v0))
		}
		$triangles
	}

	## The area of the triangle, negated when `S2Predicates.sign` says it is
	## clockwise. Upstream's `S2::SignedArea`.
	oriented_triangle_area : S2Point, S2Point, S2Point -> F64
	oriented_triangle_area = |a, b, c|
		S2Predicates.sign(a, b, c).to_f64() * S2Point.triangle_area(a, b, c)

	## One step of Kahan's compensated sum, on a `(sum, error)` pair.
	kahan_add : (F64, F64), F64 -> (F64, F64)
	kahan_add = |(sum, error), value| {
		adjusted = value - error
		total = sum + adjusted
		(total, (total - sum) - adjusted)
	}

	## The loop without the degeneracies that a comparison of neighbours can
	## find: a repeated vertex `AA` and a spike `ABA` both become `A`, until
	## none is left. A loop that is all degeneracies becomes the empty list.
	##
	## Ports upstream's `S2::PruneDegeneracies`.
	prune_degeneracies : List(S2Point) -> List(S2Point)
	prune_degeneracies = |points| {
		var $kept = []
		for v in points {
			n = $kept.len()
			if n > 0 and S2Boundary.vertex_at($kept, n - 1) == v {
				# A repeated vertex: AA becomes A.
				{}
			} else if n >= 2 and S2Boundary.vertex_at($kept, n - 2) == v {
				# A spike: ABA becomes A.
				$kept = $kept.drop_last(1)
			} else {
				$kept = $kept.append(v)
			}
		}
		if $kept.len() >= 2 and S2Boundary.vertex_at($kept, 0) == S2Boundary.vertex_at($kept, $kept.len() - 1) {
			$kept = $kept.drop_last(1)
		}
		m = $kept.len()
		if m < 3 {
			return []
		}
		# A spike can still wrap from the end to the start. Removing it never
		# leaves the loop degenerate.
		var $k = 0
		while S2Boundary.vertex_at($kept, $k + 1) == S2Boundary.vertex_at($kept, m - 1 - $k)
			or S2Boundary.vertex_at($kept, $k) == S2Boundary.vertex_at($kept, m - 2 - $k) {
			$k = $k + 1
		}
		$kept.sublist({ start: $k, len: m - 2 * $k })
	}

	## A start vertex and a direction for walking the loop that do not change
	## when the loop is rotated or reversed: the walk that gives the
	## lexicographically smallest vertex sequence.
	##
	## Ports upstream's `S2::GetCanonicalLoopOrder`.
	LoopOrder : { first : U64, reversed : Bool }

	canonical_loop_order : List(S2Point) -> LoopOrder
	canonical_loop_order = |points| {
		n = points.len()
		if n == 0 {
			return { first: 0, reversed: Bool.False }
		}
		var $min_indices = [0]
		var $i = 1
		while $i < n {
			v = S2Boundary.vertex_at(points, $i)
			smallest = S2Boundary.vertex_at(points, $min_indices.first() ?? 0)
			if v <= smallest {
				if v < smallest {
					$min_indices = []
				}
				$min_indices = $min_indices.append($i)
			}
			$i = $i + 1
		}
		var $best = { first: $min_indices.first() ?? 0, reversed: Bool.False }
		for m in $min_indices {
			forward = { first: m, reversed: Bool.False }
			backward = { first: m, reversed: Bool.True }
			if S2Boundary.order_less(points, forward, $best) {
				$best = forward
			}
			if S2Boundary.order_less(points, backward, $best) {
				$best = backward
			}
		}
		$best
	}

	## The `k`-th vertex of the loop when walked in the given order.
	ordered_vertex : List(S2Point), LoopOrder, U64 -> S2Point
	ordered_vertex = |points, order, k| {
		n = points.len()
		if n == 0 {
			return S2Point.zero()
		}
		if order.reversed {
			S2Boundary.vertex_at(points, order.first + n - (k % n))
		} else {
			S2Boundary.vertex_at(points, order.first + k)
		}
	}

	## True when the walk `a` gives a smaller vertex sequence than the walk
	## `b`. Both walks start at the same vertex.
	order_less : List(S2Point), LoopOrder, LoopOrder -> Bool
	order_less = |points, a, b| {
		if a == b {
			return Bool.False
		}
		var $k = 1
		while $k < points.len() {
			va = S2Boundary.ordered_vertex(points, a, $k)
			vb = S2Boundary.ordered_vertex(points, b, $k)
			if va < vb {
				return Bool.True
			}
			if va > vb {
				return Bool.False
			}
			$k = $k + 1
		}
		Bool.False
	}

	## Orders two loops by vertex count, then by canonical walk direction,
	## then by their vertices in canonical order: negative, zero or positive.
	##
	## Ports upstream's `S2Polygon::CompareLoops`.
	compare_loops : List(S2Point), List(S2Point) -> I8
	compare_loops = |a, b| {
		if a.len() != b.len() {
			return if (a.len() < b.len()) -1 else 1
		}
		ao = S2Boundary.canonical_loop_order(a)
		bo = S2Boundary.canonical_loop_order(b)
		if ao.reversed != bo.reversed {
			# Upstream's direction is -1 for a reversed walk and +1 otherwise.
			return if (ao.reversed) -1 else 1
		}
		var $k = 0
		while $k < a.len() {
			va = S2Boundary.ordered_vertex(a, ao, $k)
			vb = S2Boundary.ordered_vertex(b, bo, $k)
			if va < vb {
				return -1
			}
			if va > vb {
				return 1
			}
			$k = $k + 1
		}
		0
	}

	## The geodesic curvature of the loop: the sum of its turn angles. In
	## `(-2pi, 2pi)` for an ordinary loop, positive when it runs
	## counterclockwise.
	##
	## Ports upstream's `S2::GetCurvature`. An empty list is the full loop,
	## with `-2pi`, and a loop that is all degeneracies gets exactly `2pi`.
	## The angles are summed in canonical order with Kahan summation, so
	## rotating the loop gives the same result and reversing it gives exactly
	## the negated result.
	curvature : List(S2Point) -> F64
	curvature = |points| {
		if points.is_empty() {
			return -2.0 * F64.pi
		}
		pruned = S2Boundary.prune_degeneracies(points)
		if pruned.is_empty() {
			return 2.0 * F64.pi
		}
		n = pruned.len()
		order = S2Boundary.canonical_loop_order(pruned)
		at = |k| S2Boundary.ordered_vertex(pruned, order, k)
		var $sum = S2Edge.turn_angle(at(n - 1), at(0), at(1))
		var $compensation = 0.0
		var $k = 1
		while $k < n {
			angle = S2Edge.turn_angle(at($k - 1), at($k), at($k + 1)) + $compensation
			old_sum = $sum
			$sum = $sum + angle
			$compensation = (old_sum - $sum) + angle
			$k = $k + 1
		}
		max_curvature = 2.0 * F64.pi - 4.0 * S2Boundary.epsilon()
		direction = if (order.reversed) -1.0 else 1.0
		(direction * ($sum + $compensation)).max(-max_curvature).min(max_curvature)
	}

	## The largest error `curvature` can make for this loop: 11.25 machine
	## epsilons per vertex. It also bounds the error of `signed_area`.
	curvature_max_error : List(S2Point) -> F64
	curvature_max_error = |points| 11.25 * S2Boundary.epsilon() * points.len().to_f64()

	## How the wedge `a0 -> ab1 -> a2` stands to the wedge `b0 -> ab1 -> b2`,
	## each wedge's inside being on its left.
	##
	## Ports upstream's `S2::GetWedgeRelation`. Where edges overlap, the most
	## specific relation wins.
	wedge_relation : S2Point, S2Point, S2Point, S2Point, S2Point -> [Equals, ProperlyContains, IsProperlyContained, ProperlyOverlaps, IsDisjoint]
	wedge_relation = |a0, ab1, a2, b0, b2| {
		if a0 == b0 and a2 == b2 {
			return Equals
		}
		if S2Predicates.ordered_ccw(a0, a2, b2, ab1) {
			if S2Predicates.ordered_ccw(b2, b0, a0, ab1) {
				return ProperlyContains
			}
			return if (a2 == b2) IsProperlyContained else ProperlyOverlaps
		}
		if S2Predicates.ordered_ccw(a0, b0, b2, ab1) {
			return IsProperlyContained
		}
		if (S2Predicates.ordered_ccw(a0, b0, a2, ab1)) IsDisjoint else ProperlyOverlaps
	}

	## Whether two loops of one polygon cross or share an edge.
	##
	## Each list must be oriented with the polygon's interior on its left, so
	## a hole is given reversed. Two edges that cross at interior points are
	## a crossing. At a vertex the two loops share, an edge that both loops
	## have, in either direction, is a shared edge, and wedges that each
	## overlap the other's inside and outside are a crossing. This is the
	## cross-loop part of upstream's `FindSelfIntersection`, and it compares
	## every pair of edges.
	find_loop_pair_error : List(S2Point), List(S2Point) -> Try({}, [Cross, ShareEdge])
	find_loop_pair_error = |a, b| {
		n = a.len()
		m = b.len()
		var $i = 0
		while $i < n {
			a0 = S2Boundary.vertex_at(a, $i)
			a1 = S2Boundary.vertex_at(a, $i + 1)
			var $j = 0
			while $j < m {
				b0 = S2Boundary.vertex_at(b, $j)
				b1 = S2Boundary.vertex_at(b, $j + 1)
				if a1 == b1 {
					a2 = S2Boundary.vertex_at(a, $i + 2)
					b2 = S2Boundary.vertex_at(b, $j + 2)
					if a0 == b0 or a0 == b2 {
						return Err(ShareEdge)
					}
					if S2Boundary.wedge_relation(a0, a1, a2, b0, b2) == ProperlyOverlaps
						and S2Boundary.wedge_relation(a0, a1, a2, b2, b0) == ProperlyOverlaps {
						return Err(Cross)
					}
				} else if S2Edge.crossing_sign(a0, a1, b0, b1) > 0 {
					return Err(Cross)
				}
				$j = $j + 1
			}
			$i = $i + 1
		}
		Ok({})
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
			return if (points.get(0) ?? S2Point.zero()).z() < 0.0 {
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
			$bound = $bound.union(S2Boundary.edge_bound(a, b))
			$i = $i + 1
		}

		# Rounding in the trigonometry above can shave the true bound.
		padded = $bound.expanded(S2Boundary.bound_margin())
		north = S2Boundary.contains_pole(points, origin_inside, Bool.True)
		south = S2Boundary.contains_pole(points, origin_inside, Bool.False)
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

	## The bounding rectangle of an open chain of edges: every vertex, and
	## the poleward bulge of every edge between them.
	##
	## Like upstream's `S2LatLngRectBounder`, the result is padded against
	## rounding and closed at the poles.
	chain_bound : List(S2Point) -> S2LatLngRect
	chain_bound = |points| {
		var $bound = S2LatLngRect.empty()
		for v in points {
			$bound = $bound.add_point(v)
		}
		var $i = 1
		while $i < points.len() {
			a = points.get($i - 1) ?? S2Point.zero()
			b = points.get($i) ?? S2Point.zero()
			$bound = $bound.union(S2Boundary.edge_bound(a, b))
			$i = $i + 1
		}
		$bound.expanded(S2Boundary.bound_margin()).polar_closure()
	}

	## The padding every edge bound gets, since rounding in the trigonometry
	## can shave the true bound.
	bound_margin : () -> S2LatLng
	bound_margin = || {
		margin = S1Angle.from_radians(2.0e-15).radians()
		S2LatLng.from_radians(margin, margin)
	}

	## True when the loop contains the north or the south pole.
	contains_pole : List(S2Point), Bool, Bool -> Bool
	contains_pole = |points, origin_inside, north|
		S2Boundary.crossing_parity(
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
				if S2Boundary.on_edge(a, b, candidate) {
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
}

expect {
	# An edge along the 10th parallel bulges north of it between its ends.
	a = S2LatLng.from_degrees(10.0, -20.0).to_point()
	b = S2LatLng.from_degrees(10.0, 20.0).to_point()
	S2Boundary.edge_bound(a, b).lat_hi().degrees() > 10.5
		and S2Boundary.chain_bound([a, b]).contains_point(S2Edge.interpolate(a, b, 0.5))
}
expect S2Boundary.chain_bound([]).is_empty()
expect S2Boundary.find_vertex([S2Point.new(1.0, 0.0, 0.0)], S2Point.new(0.0, 1.0, 0.0)) == Err(NotFound)

import S1Angle
import S1ChordAngle
import S2LatLng
import Internal/S2Crossing
import Internal/S2Exact
import S2Point
import S2Predicates

## Operations on geodesic edges: whether two cross, where they cross, and how
## far a point or another edge is from one.
##
## An edge is the shorter great-circle arc between two unit-length points. The
## crossing tests are exact, because they are built on `S2Predicates.sign`
## rather than on comparisons of rounded determinants.
##
## Upstream's `Update...` functions change a running minimum or maximum in
## place and return whether they changed it. The `update_*` functions here
## take the current value and return `Ok(new_value)` when the distance
## improves on it, or `Err(Unchanged)` when it does not, so that
## `S2Edge.update_min_distance(x, a, b, best) ?? best` keeps a running
## minimum.
S2Edge := [].{

	## An upper bound on the angle between the direction that
	## `S2Point.robust_cross` returns and the exact cross product, `6 * 2^-53`
	## radians.
	robust_cross_prod_error : S1Angle
	robust_cross_prod_error = S1Angle.from_radians(6.0 * dbl_err)

	## An upper bound on the distance from the point that `intersection`
	## returns to the true intersection, `8 * 2^-53` radians.
	intersection_error : S1Angle
	intersection_error = S1Angle.from_radians(8.0 * dbl_err)

	## The distance within which vertices that `intersection` has displaced
	## should be merged back together: twice `intersection_error`.
	intersection_merge_radius : S1Angle
	intersection_merge_radius = S1Angle.from_radians(16.0 * dbl_err)

	## An upper bound on the distance from the point that `project` returns to
	## the edge. It bounds only the error perpendicular to the edge.
	project_perpendicular_error : S1Angle
	project_perpendicular_error = S1Angle.from_radians((2.0 + 2.0 / sqrt3) * dbl_err + 6.0 * dbl_err)

	## An upper bound on the distance from the point that `point_on_line`
	## returns to the true result.
	point_on_line_error : S1Angle
	point_on_line_error = S1Angle.from_radians((4.0 + 2.0 / sqrt3) * dbl_err + 6.0 * dbl_err)

	## An upper bound on the distance from the point that `point_on_ray`
	## returns to the ray. It bounds only the error perpendicular to the ray.
	point_on_ray_perpendicular_error : S1Angle
	point_on_ray_perpendicular_error = S1Angle.from_radians(3.0 * dbl_err)

	## The angle turned at `b` when walking from `a` through `b` to `c`, in
	## radians in `(-pi, pi]`. It is positive for a left turn, which is a
	## counterclockwise one, and negative for a right turn.
	##
	## The magnitude comes from the robust cross products of the edges, so it
	## stays accurate when two points are very close together. The sign comes
	## from `S2Predicates.sign`, so it is right for turns close to 180 degrees.
	## An `a` equal to `c` is allowed and gives a turn of `-pi`.
	turn_angle : S2Point, S2Point, S2Point -> F64
	turn_angle = |a, b, c| {
		angle = a.robust_cross(b).angle_to(b.robust_cross(c)).radians()
		if S2Predicates.sign(a, b, c) > 0 {
			angle
		} else {
			-angle
		}
	}

	## How the edges `ab` and `cd` meet.
	##
	## - `1` when they cross at a point interior to both
	## - `0` when they share exactly one endpoint
	## - `-1` when they do not cross
	##
	## Degenerate edges, where `a == b` or `c == d`, never cross. To test one
	## edge against a chain of others, `S2EdgeCrosser` reuses work between
	## the tests.
	crossing_sign : S2Point, S2Point, S2Point, S2Point -> I8
	crossing_sign = |a, b, c, d| {
		a_cross_b = a.cross(b)
		acb = -S2Predicates.triage_sign(c, a_cross_b)
		bda = S2Predicates.triage_sign(d, a_cross_b)
		S2Crossing.crossing_sign(a, b, c, d, acb, bda).0
	}

	## Whether two edges that share an endpoint should be counted as crossing.
	##
	## The rule makes a shared vertex belong to exactly one of the two edges,
	## so that a point-in-polygon test that counts crossings gets a consistent
	## answer along a boundary. Edges with four distinct endpoints give
	## `Bool.False`.
	vertex_crossing : S2Point, S2Point, S2Point, S2Point -> Bool
	vertex_crossing = |a, b, c, d| {
		if a == b or c == d {
			return Bool.False
		}
		if a == c {
			b == d or S2Predicates.ordered_ccw(a.ref_dir(), d, b, a)
		} else if b == d {
			S2Predicates.ordered_ccw(b.ref_dir(), c, a, b)
		} else if a == d {
			b == c or S2Predicates.ordered_ccw(a.ref_dir(), c, b, a)
		} else if b == c {
			S2Predicates.ordered_ccw(b.ref_dir(), d, a, b)
		} else {
			Bool.False
		}
	}

	## Like `vertex_crossing`, but with a sign: `1` when `cd` crosses `ab`
	## from left to right through the shared vertex, `-1` when it crosses from
	## right to left, and `0` when it does not cross.
	##
	## Summing the signs along a chain gives a winding number, where
	## `vertex_crossing` only gives a parity. Edges with four distinct
	## endpoints give `0`.
	signed_vertex_crossing : S2Point, S2Point, S2Point, S2Point -> I8
	signed_vertex_crossing = |a, b, c, d| {
		if a == b or c == d {
			return 0
		}
		if a == c {
			if (b == d or S2Predicates.ordered_ccw(a.ref_dir(), d, b, a)) 1 else 0
		} else if b == d {
			if (S2Predicates.ordered_ccw(b.ref_dir(), c, a, b)) 1 else 0
		} else if a == d {
			if (b == c or S2Predicates.ordered_ccw(a.ref_dir(), c, b, a)) -1 else 0
		} else if b == c {
			if (S2Predicates.ordered_ccw(b.ref_dir(), d, a, b)) -1 else 0
		} else {
			0
		}
	}

	## `crossing_sign` and `vertex_crossing` combined into the single boolean
	## a boundary-crossing count needs.
	edge_or_vertex_crossing : S2Point, S2Point, S2Point, S2Point -> Bool
	edge_or_vertex_crossing = |a, b, c, d| {
		crossing = S2Edge.crossing_sign(a, b, c, d)
		if crossing < 0 {
			Bool.False
		} else if crossing > 0 {
			Bool.True
		} else {
			S2Edge.vertex_crossing(a, b, c, d)
		}
	}

	## The point where two crossing edges meet.
	##
	## Requires that `crossing_sign` reports a crossing. The result is within
	## `intersection_error` of the true intersection, and it is consistent
	## with the exact predicates: it lies on the correct side of each edge.
	## Rounded arithmetic decides almost every case; when its error bound is
	## too large, the intersection is computed in exact arithmetic.
	intersection : S2Point, S2Point, S2Point, S2Point -> S2Point
	intersection = |a0, a1, b0, b1|
		match intersection_stable(a0, a1, b0, b1) {
			Ok(x) => x
			Err(Uncertain) => intersection_exact(a0, a1, b0, b1)
		}

	## The point a fraction `t` of the way from `a` to `b` along their great
	## circle.
	##
	## `t` outside `[0, 1]` extrapolates beyond the endpoints.
	interpolate : S2Point, S2Point, F64 -> S2Point
	interpolate = |a, b, t| {
		if t == 0.0 {
			a
		} else if t == 1.0 {
			b
		} else {
			S2Edge.point_on_line(a, b, a.angle_to(b) * t)
		}
	}

	## The ratio `ax / (ax + bx)` of the distances from `x` to the endpoints.
	##
	## When `x` lies on the edge, this is the fraction `t` for which
	## `interpolate(a, b, t)` gives `x`. Requires `a != b`.
	distance_fraction : S2Point, S2Point, S2Point -> F64
	distance_fraction = |x, a, b| {
		da = x.angle_to(a).radians()
		db = x.angle_to(b).radians()
		da / (da + db)
	}

	## The point at distance `r` from `a` along the great circle towards `b`.
	##
	## The direction is well defined even when `a` and `b` are antipodal or
	## nearly so. When `a == b`, the direction is arbitrary.
	point_on_line : S2Point, S2Point, S1Angle -> S2Point
	point_on_line = |a, b, r| S2Edge.point_on_ray(a, line_direction(a, b), r)

	## `point_on_line` with the distance as a chord angle, which is faster but
	## cannot represent distances near 180 degrees accurately.
	point_on_line_chord : S2Point, S2Point, S1ChordAngle -> S2Point
	point_on_line_chord = |a, b, r| S2Edge.point_on_ray_chord(a, line_direction(a, b), r)

	## The point at distance `r` from `a`, to the left of the edge from `a` to
	## `b` and perpendicular to it.
	point_to_left : S2Point, S2Point, S1Angle -> S2Point
	point_to_left = |a, b, r| S2Edge.point_on_ray(a, a.robust_cross(b).normalize(), r)

	## `point_to_left` with the distance as a chord angle.
	point_to_left_chord : S2Point, S2Point, S1ChordAngle -> S2Point
	point_to_left_chord = |a, b, r| S2Edge.point_on_ray_chord(a, a.robust_cross(b).normalize(), r)

	## The point at distance `r` from `a`, to the right of the edge from `a`
	## to `b` and perpendicular to it.
	point_to_right : S2Point, S2Point, S1Angle -> S2Point
	point_to_right = |a, b, r| S2Edge.point_on_ray(a, b.robust_cross(a).normalize(), r)

	## `point_to_right` with the distance as a chord angle.
	point_to_right_chord : S2Point, S2Point, S1ChordAngle -> S2Point
	point_to_right_chord = |a, b, r| S2Edge.point_on_ray_chord(a, b.robust_cross(a).normalize(), r)

	## The point at distance `r` from `a` in the direction `direction`, which
	## must be a unit vector perpendicular to `a`.
	##
	## Faster than `point_on_line` when many points along the same ray are
	## wanted.
	point_on_ray : S2Point, S2Point, S1Angle -> S2Point
	point_on_ray = |a, direction, r| {
		trig = r.sin_cos()
		(a * trig.cos + direction * trig.sin).normalize()
	}

	## `point_on_ray` with the distance as a chord angle, which is faster but
	## cannot represent distances near 180 degrees accurately.
	point_on_ray_chord : S2Point, S2Point, S1ChordAngle -> S2Point
	point_on_ray_chord = |a, direction, r| (a * r.cos() + direction * r.sin()).normalize()

	## The point of the edge `ab` closest to `x`. All three must be unit
	## length.
	project : S2Point, S2Point, S2Point -> S2Point
	project = |x, a, b| S2Edge.project_with_cross(x, a, b, a.robust_cross(b))

	## `project` when the cross product `a_cross_b` of the endpoints is
	## already known. It need not be unit length, but it should come from
	## `S2Point.robust_cross` for the most accurate result.
	project_with_cross : S2Point, S2Point, S2Point, S2Point -> S2Point
	project_with_cross = |x, a, b, a_cross_b| {
		if x == a or x == b {
			return x
		}
		# The normalized normal, rather than a_cross_b itself, keeps the last
		# cross product from underflowing.
		n = a_cross_b.normalize()
		p = n.robust_cross(x).cross(n).normalize()

		# When the closest point on the full great circle lies within the
		# edge, that is the answer; otherwise an endpoint is.
		pn = p.cross(n)
		inside =
			S2Predicates.sign_with_cross(p, n, a, pn) > 0
				and S2Predicates.sign_with_cross(p, n, b, pn) < 0
		if inside {
			p
		} else if (x - a).norm2() <= (x - b).norm2() {
			a
		} else {
			b
		}
	}

	## The distance from `x` to the closest point of the edge `ab`.
	##
	## Very accurate for small distances, less so near 90 degrees and beyond.
	## `a == b` is allowed. To compare against a limit, `is_distance_less` is
	## faster.
	distance_to_edge : S2Point, S2Point, S2Point -> S1ChordAngle
	distance_to_edge = |x, a, b| min_distance(Bool.True, x, a, b, S1ChordAngle.zero()) ?? S1ChordAngle.zero()

	## The distance from `x` to the furthest point of the edge `ab`.
	##
	## That point is an endpoint unless the edge passes within 90 degrees of
	## the antipode of `x`.
	max_distance_to_edge : S2Point, S2Point, S2Point -> S1ChordAngle
	max_distance_to_edge = |x, a, b|
		S2Edge.update_max_distance(x, a, b, S1ChordAngle.negative()) ?? S1ChordAngle.negative()

	## True when the distance from `x` to the edge `ab` is less than `limit`.
	##
	## Use `limit.successor()` for "less than or equal to".
	## `S2Predicates.compare_edge_distance` is the exact version.
	is_distance_less : S2Point, S2Point, S2Point, S1ChordAngle -> Bool
	is_distance_less = |x, a, b, limit| S2Edge.update_min_distance(x, a, b, limit).is_ok()

	## True when the closest point of the edge `ab` to `x` is interior to the
	## edge rather than an endpoint, and its distance is less than `limit`.
	is_interior_distance_less : S2Point, S2Point, S2Point, S1ChordAngle -> Bool
	is_interior_distance_less = |x, a, b, limit|
		S2Edge.update_min_interior_distance(x, a, b, limit).is_ok()

	## The distance from `x` to the edge `ab`, when it is less than `min_dist`.
	##
	## `a == b` is allowed. Faster than `distance_to_edge` when many edges are
	## compared, since an edge that is obviously further away costs little.
	update_min_distance : S2Point, S2Point, S2Point, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
	update_min_distance = |x, a, b, min_dist| min_distance(Bool.False, x, a, b, min_dist)

	## The distance from `x` to the furthest point of the edge `ab`, when it
	## is greater than `max_dist`.
	update_max_distance : S2Point, S2Point, S2Point, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
	update_max_distance = |x, a, b, max_dist| {
		endpoint = S1ChordAngle.from_points(x, a).max(S1ChordAngle.from_points(x, b))
		dist =
			if endpoint > S1ChordAngle.right() {
				# Beyond 90 degrees the furthest point can be interior, and it
				# is the point closest to the antipode of x.
				antipodal = min_distance(Bool.True, -x, a, b, endpoint) ?? endpoint
				S1ChordAngle.straight() - antipodal
			} else {
				endpoint
			}
		if max_dist < dist {
			Ok(dist)
		} else {
			Err(Unchanged)
		}
	}

	## The distance from `x` to the edge `ab`, when the closest point is
	## interior to the edge and the distance is less than `min_dist`.
	update_min_interior_distance : S2Point, S2Point, S2Point, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
	update_min_interior_distance = |x, a, b, min_dist|
		min_interior_distance(Bool.False, x, a, b, (x - a).norm2(), (x - b).norm2(), min_dist)

	## The largest error in a distance from `update_min_distance` and the
	## functions built on it, in squared-chord units, for inputs normalized as
	## `S2Point.normalize` normalizes them.
	##
	## Add it with `S1ChordAngle.plus_error`. The error is about 1.2e-15
	## radians near zero, and grows towards 180 degrees: about 0.5 metres on
	## the Earth for exactly antipodal points.
	update_min_distance_max_error : S1ChordAngle -> F64
	update_min_distance_max_error = |dist|
		min_interior_distance_max_error(dist).max(dist.point_constructor_max_error())

	## The distance between the edges `a0a1` and `b0b1`, when it is less than
	## `min_dist`. Edges that cross are at distance zero.
	##
	## Degenerate edges are allowed.
	update_edge_pair_min_distance : S2Point, S2Point, S2Point, S2Point, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
	update_edge_pair_min_distance = |a0, a1, b0, b1, min_dist| {
		if min_dist == S1ChordAngle.zero() {
			return Err(Unchanged)
		}
		if S2Edge.crossing_sign(a0, a1, b0, b1) >= 0 {
			return Ok(S1ChordAngle.zero())
		}
		# Otherwise the minimum is at an endpoint of one of the edges. All
		# four are checked.
		[(a0, b0, b1), (a1, b0, b1), (b0, a0, a1), (b1, a0, a1)].fold(
			Err(Unchanged),
			|acc, (x, p, q)| {
				current = acc ?? min_dist
				match S2Edge.update_min_distance(x, p, q, current) {
					Ok(d) => Ok(d)
					Err(Unchanged) => acc
				}
			},
		)
	}

	## The largest distance between a point of `a0a1` and a point of `b0b1`,
	## when it is greater than `max_dist`.
	##
	## When one edge crosses the antipodal image of the other, the distance
	## is 180 degrees.
	update_edge_pair_max_distance : S2Point, S2Point, S2Point, S2Point, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
	update_edge_pair_max_distance = |a0, a1, b0, b1, max_dist| {
		if max_dist == S1ChordAngle.straight() {
			return Err(Unchanged)
		}
		if S2Edge.crossing_sign(a0, a1, -b0, -b1) >= 0 {
			return Ok(S1ChordAngle.straight())
		}
		[(a0, b0, b1), (a1, b0, b1), (b0, a0, a1), (b1, a0, a1)].fold(
			Err(Unchanged),
			|acc, (x, p, q)| {
				current = acc ?? max_dist
				match S2Edge.update_max_distance(x, p, q, current) {
					Ok(d) => Ok(d)
					Err(Unchanged) => acc
				}
			},
		)
	}

	## True when the distance between the edges `a0a1` and `b0b1` is less
	## than `distance`.
	##
	## `S2Predicates.compare_edge_distance` gives the exact version of the
	## underlying point test, and `compare_edge_pair_distance` the exact
	## version of this one.
	is_edge_pair_distance_less : S2Point, S2Point, S2Point, S2Point, S1ChordAngle -> Bool
	is_edge_pair_distance_less = |a0, a1, b0, b1, distance| {
		if S2Edge.crossing_sign(a0, a1, b0, b1) >= 0 {
			return distance != S1ChordAngle.zero()
		}
		S2Edge.is_distance_less(a0, b0, b1, distance)
			or S2Edge.is_distance_less(a1, b0, b1, distance)
			or S2Edge.is_distance_less(b0, a0, a1, distance)
			or S2Edge.is_distance_less(b1, a0, a1, distance)
	}

	## The pair of points, the first on `a0a1` and the second on `b0b1`, that
	## are closest to each other. When the edges cross, both are the
	## intersection.
	##
	## Degenerate edges are allowed.
	edge_pair_closest_points : S2Point, S2Point, S2Point, S2Point -> (S2Point, S2Point)
	edge_pair_closest_points = |a0, a1, b0, b1| {
		if S2Edge.crossing_sign(a0, a1, b0, b1) > 0 {
			x = S2Edge.intersection(a0, a1, b0, b1)
			return (x, x)
		}
		# Find which vertex and edge achieve the minimum first, then project
		# only that vertex.
		start = min_distance(Bool.True, a0, b0, b1, S1ChordAngle.zero()) ?? S1ChordAngle.zero()
		(_, closest) = [(A1, a1, b0, b1), (B0, b0, a0, a1), (B1, b1, a0, a1)].fold(
			(start, A0),
			|(best, which), (tag, x, p, q)|
				match S2Edge.update_min_distance(x, p, q, best) {
					Ok(d) => (d, tag)
					Err(Unchanged) => (best, which)
				},
		)
		match closest {
			A0 => (a0, S2Edge.project(a0, b0, b1))
			A1 => (a1, S2Edge.project(a1, b0, b1))
			B0 => (S2Edge.project(b0, a0, a1), b0)
			B1 => (S2Edge.project(b1, a0, a1), b1)
		}
	}

	## True when every point of the edge `b0b1` is within `tolerance` of some
	## point of the edge `a0a1`: the directed Hausdorff distance from `b` to
	## `a` is at most `tolerance`.
	##
	## Requires `0 < tolerance < 90 degrees`.
	is_edge_b_near_edge_a : S2Point, S2Point, S2Point, S2Point, S1Angle -> Bool
	is_edge_b_near_edge_a = |a0, a1, b0, b1, tolerance| {
		a_ortho0 = a0.robust_cross(a1).normalize()
		a_nearest_b0 = S2Edge.project_with_cross(b0, a0, a1, a_ortho0)
		a_nearest_b1 = S2Edge.project_with_cross(b1, a0, a1, a_ortho0)
		# Point the normal of a the way a_nearest_b0 x a_nearest_b1 points,
		# which handles edges that run in opposite directions.
		a_ortho =
			if S2Predicates.sign(a_ortho0, a_nearest_b0, a_nearest_b1) < 0 {
				a_ortho0 * -1.0
			} else {
				a_ortho0
			}

		# Both endpoints of b must be near a.
		if b0.angle_to(a_nearest_b0) > tolerance or b1.angle_to(a_nearest_b1) > tolerance {
			return Bool.False
		}

		# When the planes of the two great circles meet at an angle within
		# tolerance, no point of b can be further than that from a.
		b_ortho = b0.robust_cross(b1).normalize()
		planar_angle = a_ortho.angle_to(b_ortho)
		if planar_angle <= tolerance {
			return Bool.True
		}

		# From 90 degrees on, b is near a only when both its endpoints are
		# nearest the same endpoint of a.
		if planar_angle >= S1Angle.from_radians(0.5 * F64.pi) {
			return (b0.angle_to(a0) < b0.angle_to(a1)) == (b1.angle_to(a0) < b1.angle_to(a1))
		}

		# Otherwise b is not near a when one of the two points of its great
		# circle furthest from the great circle of a lies on b.
		furthest = b_ortho.cross(a_ortho.robust_cross(b_ortho)).normalize()
		furthest_inv = furthest * -1.0
		on_b = |p| S2Predicates.sign(b_ortho, b0, p) > 0 and S2Predicates.sign(p, b1, b_ortho) > 0
		!(on_b(furthest) or on_b(furthest_inv))
	}

	## Compares the distance between the edges `a0a1` and `b0b1` with `r`:
	## `-1` when it is less, `0` when it is equal, and `1` when it is greater.
	##
	## The answer is exact, with the points treated as though they lay exactly
	## on the unit sphere. Requires that neither edge has antipodal endpoints.
	## Upstream has this in `s2pred`; it lives here because it needs
	## `crossing_sign`, and `S2Predicates` cannot import this module.
	compare_edge_pair_distance : S2Point, S2Point, S2Point, S2Point, S1ChordAngle -> I8
	compare_edge_pair_distance = |a0, a1, b0, b1, r| {
		if S2Edge.crossing_sign(a0, a1, b0, b1) >= 0 {
			r2 = r.length2()
			return if r2 > 0.0 {
				-1
			} else if r2 < 0.0 {
				1
			} else {
				0
			}
		}
		S2Predicates.compare_edge_distance(a0, b0, b1, r)
			.min(S2Predicates.compare_edge_distance(a1, b0, b1, r))
			.min(S2Predicates.compare_edge_distance(b0, a0, a1, r))
			.min(S2Predicates.compare_edge_distance(b1, a0, a1, r))
	}
}

expect {
	# Two edges that cross at the origin of the coordinate frame.
	a = S2Point.new(1.0, 0.0, 0.1).normalize()
	b = S2Point.new(-1.0, 0.0, 0.1).normalize()
	c = S2Point.new(0.0, 1.0, 0.1).normalize()
	d = S2Point.new(0.0, -1.0, 0.1).normalize()
	S2Edge.crossing_sign(a, b, c, d) == 1
}
expect {
	# Disjoint edges on the same great circle.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(-1.0, 0.0, 0.0)
	d = S2Point.new(0.0, -1.0, 0.0)
	S2Edge.crossing_sign(a, b, c, d) == -1
}
expect {
	# A shared endpoint is a vertex crossing, reported as zero.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(1.0, 0.0, 0.0)
	d = S2Point.new(0.0, 0.0, 1.0)
	S2Edge.crossing_sign(a, b, c, d) == 0
}
expect {
	# A degenerate edge never crosses.
	a = S2Point.new(1.0, 0.0, 0.0)
	c = S2Point.new(0.0, 1.0, 0.0)
	d = S2Point.new(0.0, -1.0, 0.0)
	S2Edge.crossing_sign(a, a, c, d) == -1
}
expect {
	# crossing_sign is symmetric in each edge and between the two edges.
	a = S2Point.new(1.0, 0.0, 0.1).normalize()
	b = S2Point.new(-1.0, 0.0, 0.1).normalize()
	c = S2Point.new(0.0, 1.0, 0.1).normalize()
	d = S2Point.new(0.0, -1.0, 0.1).normalize()
	base = S2Edge.crossing_sign(a, b, c, d)
	base == S2Edge.crossing_sign(b, a, c, d)
		and base == S2Edge.crossing_sign(a, b, d, c)
		and base == S2Edge.crossing_sign(c, d, a, b)
}
expect {
	a = S2Point.new(1.0, 0.0, 0.1).normalize()
	b = S2Point.new(-1.0, 0.0, 0.1).normalize()
	c = S2Point.new(0.0, 1.0, 0.1).normalize()
	d = S2Point.new(0.0, -1.0, 0.1).normalize()
	simple_crossing(a, b, c, d)
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	d = S2Point.new(0.0, 0.0, -1.0)
	!simple_crossing(a, b, c, d)
}
expect {
	# The intersection of two crossing edges lies on both of them.
	a0 = S2Point.new(1.0, 0.0, 0.2).normalize()
	a1 = S2Point.new(-1.0, 0.0, 0.2).normalize()
	b0 = S2Point.new(0.0, 1.0, 0.2).normalize()
	b1 = S2Point.new(0.0, -1.0, 0.2).normalize()
	x = S2Edge.intersection(a0, a1, b0, b1)
	S2Edge.distance_to_edge(x, a0, a1).radians() < 1e-14
		and S2Edge.distance_to_edge(x, b0, b1).radians() < 1e-14
}
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 0.0)
	== S2Point.new(1.0, 0.0, 0.0)
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 1.0)
	== S2Point.new(0.0, 1.0, 0.0)
expect {
	mid = S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 0.5)
	mid.approx_eq(S2Point.new(1.0, 1.0, 0.0).normalize(), 1e-15)
}
expect {
	# Interpolating a quarter of the way covers a quarter of the angle.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	q = S2Edge.interpolate(a, b, 0.25)
	(a.angle_to(q).degrees() - 22.5).abs() < 1e-13
}
expect {
	p = S2Edge.point_on_line(
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(0.0, 1.0, 0.0),
		S1Angle.from_degrees(30.0),
	)
	p.approx_eq(S2Point.new(0.8660254037844387, 0.49999999999999994, 0.0), 1e-15)
}
expect {
	# The closest point to a point above the middle of an edge is that middle.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	x = S2Point.new(1.0, 1.0, 0.5).normalize()
	S2Edge.project(x, a, b).approx_eq(S2Point.new(1.0, 1.0, 0.0).normalize(), 1e-15)
}
expect {
	# Beyond an endpoint, the closest point is that endpoint.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	x = S2Point.new(1.0, -0.5, 0.0).normalize()
	S2Edge.project(x, a, b) == a
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	x = S2Point.new(1.0, 1.0, 0.0).normalize()
	S2Edge.distance_to_edge(x, a, b).radians() < 1e-15
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	x = S2Point.new(0.0, 0.0, 1.0)
	(S2Edge.distance_to_edge(x, a, b).degrees() - 90.0).abs() < 1e-13
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	x = S2Point.new(1.0, 0.1, 0.0).normalize()
	(S2Edge.max_distance_to_edge(x, a, b).degrees() - a.angle_to(b).degrees()).abs() > 0.0
		and S2Edge.max_distance_to_edge(x, a, b) >= S2Edge.distance_to_edge(x, a, b)
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	x = S2Point.new(1.0, 1.0, 0.0).normalize()
	S2Edge.is_distance_less(x, a, b, S1ChordAngle.from_angle(S1Angle.from_degrees(1.0)))
}
expect {
	# Two edges meeting head to tail at a shared vertex.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 1.0, 0.0)
	d = S2Point.new(0.0, 0.0, 1.0)
	S2Edge.edge_or_vertex_crossing(a, b, c, d)
		== S2Edge.vertex_crossing(a, b, c, d)
}

## A crossing test that uses only rounded arithmetic.
##
## Cheap, and correct whenever the edges are not nearly degenerate, but it
## can contradict itself for nearly collinear input. Prefer
## `crossing_sign` unless the cost has been measured to matter.
simple_crossing : S2Point, S2Point, S2Point, S2Point -> Bool
simple_crossing = |a, b, c, d| {
	ab = a.cross(b)
	acb = -ab.dot(c)
	bda = ab.dot(d)
	if acb * bda <= 0.0 {
		return Bool.False
	}
	cd = c.cross(d)
	cbd = -cd.dot(b)
	dac = cd.dot(a)
	acb * cbd > 0.0 and acb * dac > 0.0
}

# The values below were printed by upstream's S2::TurnAngle at v0.14.0 through
# tools/s2_oracle.cc.
expect S2Edge.turn_angle(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0))
	== 1.5707963267948966
expect S2Edge.turn_angle(S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0))
	== -1.5707963267948966
# Walking back along the same edge turns by pi, and the sign is negative.
expect S2Edge.turn_angle(S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0))
	== -3.1415926535897931
expect S2Edge.turn_angle(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0))
	== -3.1415926535897931

# Distances from upstream's s2edge_distances_test.cc, Distance, and two
# more. The angle and the chord length are both from upstream.
expect {
	d = S2Edge.distance_to_edge(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 0.0 and d.to_angle().radians() == 0.0
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 0.0 and d.to_angle().radians() == 0.0
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 1.232595164407831e-32 and d.to_angle().radians() == 1.1102230246251565e-16
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 2.0 and d.to_angle().radians() == 1.5707963267948968
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 2.0 and d.to_angle().radians() == 1.5707963267948968
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 3.414213562373095 and d.to_angle().radians() == 2.356194490192345
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize())
	d.length2() == 0.5857864376269049 and d.to_angle().radians() == 0.7853981633974482
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize())
	d.length2() == 2.0 and d.to_angle().radians() == 1.5707963267948968
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize())
	d.length2() == 2.0 and d.to_angle().radians() == 1.5707963267948968
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize())
	d.length2() == 1.9999999999999996 and d.to_angle().radians() == 1.5707963267948963
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 0.367006838144548 and d.to_angle().radians() == 0.6154797086703874
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(1.0, 1.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize())
	d.length2() == 0.367006838144548 and d.to_angle().radians() == 0.6154797086703874
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(-1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize())
	d.length2() == 3.414213562373095 and d.to_angle().radians() == 2.356194490192345
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(0.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize())
	d.length2() == 1.9999999999999998 and d.to_angle().radians() == 1.5707963267948963
}
expect {
	d = S2Edge.distance_to_edge(S2Point.new(-1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize())
	d.length2() == 4.0 and d.to_angle().radians() == 3.141592653589793
}
expect {
	d = S2Edge.distance_to_edge(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 40.0).to_point())
	d.length2() == 0.030384493975583876 and d.to_angle().radians() == 0.17453292519943295
}
expect {
	d = S2Edge.distance_to_edge(S2LatLng.from_degrees(-1.0e-09, 5.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point())
	d.length2() == 3.046174197990346e-22 and d.to_angle().radians() == 1.745329252029641e-11
}
# Maximum distances from upstream's MaxDistance test. Beyond 90 degrees the
# furthest point can be interior to the edge.
expect S2Edge.max_distance_to_edge(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()).length2() == 2.0
expect S2Edge.max_distance_to_edge(S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()).length2() == 2.0
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()).length2() == 2.0
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 1.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()).length2() == 2.0
expect S2Edge.max_distance_to_edge(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()).length2() == 0.8452994616207485
expect S2Edge.max_distance_to_edge(S2Point.new(1.0, 1.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()).length2() == 0.8452994616207485
expect S2Edge.max_distance_to_edge(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()).length2() == 0.5857864376269049
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize()).length2() == 0.5857864376269049
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(0.0, 1.0, 1.0).normalize(), S2Point.new(0.0, -1.0, 1.0).normalize()).length2() == 0.5857864376269049
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize()).length2() == 3.414213562373095
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 1.0, -1.4142135623730951).normalize()).length2() == 3.414213562373095
expect S2Edge.max_distance_to_edge(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(0.0, 0.0, -1.0).normalize(), S2Point.new(0.0, 0.0, -1.0).normalize()).length2() == 4.0
# The update functions against upstream's, from both sides of the current
# value.
expect S2Edge.update_min_distance(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.5)) == Ok(S1ChordAngle.from_length2(1.232595164407831e-32))
expect S2Edge.update_min_distance(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.01)) == Ok(S1ChordAngle.from_length2(1.232595164407831e-32))
expect S2Edge.update_min_distance(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(2.0))
expect S2Edge.update_min_distance(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == Err(Unchanged)
expect S2Edge.update_min_distance(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.3)) == Err(Unchanged)
expect S2Edge.update_min_interior_distance(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.367006838144548))
expect S2Edge.update_min_interior_distance(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.1)) == Err(Unchanged)
expect S2Edge.update_min_interior_distance(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Err(Unchanged)
expect S2Edge.update_min_interior_distance(S2Point.new(1.0, -1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Err(Unchanged)
expect S2Edge.update_max_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.1)) == Ok(S1ChordAngle.from_length2(2.0))
expect S2Edge.update_max_distance(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S1ChordAngle.from_length2(3.9)) == Err(Unchanged)
expect S2Edge.update_max_distance(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S1ChordAngle.from_length2(-1.0)) == Ok(S1ChordAngle.from_length2(3.414213562373095))
expect S2Edge.is_distance_less(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.5)) == Bool.True
expect S2Edge.is_interior_distance_less(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.5)) == Bool.True
expect S2Edge.is_distance_less(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.01)) == Bool.True
expect S2Edge.is_interior_distance_less(S2Point.new(1.0, 3.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.01)) == Bool.True
expect S2Edge.is_distance_less(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.0)) == Bool.False
expect S2Edge.is_interior_distance_less(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.0)) == Bool.False
expect S2Edge.is_distance_less(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.5)) == Bool.True
expect S2Edge.is_interior_distance_less(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.5)) == Bool.True
expect S2Edge.is_distance_less(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(3.9)) == Bool.True
expect S2Edge.is_interior_distance_less(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(3.9)) == Bool.False
# The error bounds from upstream's GetUpdateMinDistanceMaxError.
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(0.0)) == 1.5894366072377275e-30
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(1.0e-20)) == 1.324312481528003e-25
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(1.0e-10)) == 1.3243261796706453e-20
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(0.5)) == 2.147406153227418e-15
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(1.9999)) == 3.912197093732797e-15
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(2.0)) == 1.9984014443252826e-15
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(3.0)) == 2.9976021664879234e-15
expect S2Edge.update_min_distance_max_error(S1ChordAngle.from_length2(4.0)) == 3.996802888650564e-15
expect S2Edge.distance_fraction(S2LatLng.from_degrees(0.0, 3.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()) == 0.30000000000000004
expect S2Edge.distance_fraction(S2LatLng.from_degrees(1.0, 3.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()) == 0.3090178705271354
expect S2Edge.distance_fraction(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()) == 0.5
# Projections onto an edge, with and without a precomputed cross product.
expect S2Edge.project(S2Point.new(1.0, 1.0, 0.5).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()) == S2Point.new(0.7071067811865475, 0.7071067811865475, 0.0)
expect {
	a = S2Point.new(1.0, 0.0, 0.0).normalize()
	b = S2Point.new(0.0, 1.0, 0.0).normalize()
	S2Edge.project_with_cross(S2Point.new(1.0, 1.0, 0.5).normalize(), a, b, a.robust_cross(b)) == S2Point.new(0.7071067811865475, 0.7071067811865475, 0.0)
}
expect S2Edge.project(S2Point.new(1.0, -0.5, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()) == S2Point.new(1.0, 0.0, 0.0)
expect {
	a = S2Point.new(1.0, 0.0, 0.0).normalize()
	b = S2Point.new(0.0, 1.0, 0.0).normalize()
	S2Edge.project_with_cross(S2Point.new(1.0, -0.5, 0.0).normalize(), a, b, a.robust_cross(b)) == S2Point.new(1.0, 0.0, 0.0)
}
expect S2Edge.project(S2LatLng.from_degrees(5.0, 5.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()) == S2Point.new(0.9961946980917457, 0.08715574274765815, 0.0)
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	S2Edge.project_with_cross(S2LatLng.from_degrees(5.0, 5.0).to_point(), a, b, a.robust_cross(b)) == S2Point.new(0.9961946980917457, 0.08715574274765815, 0.0)
}
expect S2Edge.project(S2LatLng.from_degrees(-80.0, 170.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()) == S2Point.new(0.984807753012208, 0.17364817766693033, 0.0)
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	S2Edge.project_with_cross(S2LatLng.from_degrees(-80.0, 170.0).to_point(), a, b, a.robust_cross(b)) == S2Point.new(0.984807753012208, 0.17364817766693033, 0.0)
}
expect S2Edge.project(S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()) == S2Point.new(0.011999136093300807, 0.9999280077750672, 0.0)
expect {
	a = S2Point.new(1.0, 0.0, 0.0).normalize()
	b = S2Point.new(0.0, 1.0, 0.0).normalize()
	S2Edge.project_with_cross(S2Point.new(0.0, 0.0, 1.0).normalize(), a, b, a.robust_cross(b)) == S2Point.new(0.011999136093300807, 0.9999280077750672, 0.0)
}
expect S2Edge.project(S2LatLng.from_degrees(1.0, 2.0).to_point(), S2LatLng.from_degrees(1.0, 2.0).to_point(), S2LatLng.from_degrees(3.0, 4.0).to_point()) == S2Point.new(0.9992386149554826, 0.03489418134011367, 0.01745240643728351)
expect {
	a = S2LatLng.from_degrees(1.0, 2.0).to_point()
	b = S2LatLng.from_degrees(3.0, 4.0).to_point()
	S2Edge.project_with_cross(S2LatLng.from_degrees(1.0, 2.0).to_point(), a, b, a.robust_cross(b)) == S2Point.new(0.9992386149554826, 0.03489418134011367, 0.01745240643728351)
}
# Points along and beside an edge, from both the S1Angle and the S1ChordAngle
# forms of upstream's GetPointOnLine, GetPointToLeft and GetPointToRight.
expect S2Edge.point_on_line(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S1Angle.from_radians(0.3)) == S2Point.new(0.9553364891256062, 0.29552020666133955, 0.0)
expect S2Edge.point_on_line_chord(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S1ChordAngle.from_radians(0.3)) == S2Point.new(0.9553364891256062, 0.29552020666133955, 0.0)
expect S2Edge.point_on_line(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_radians(0.1)) == S2Point.new(0.9044725006561222, 0.32929580287571647, 0.27109734370756644)
expect S2Edge.point_on_line_chord(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(10.0, 20.0).to_point(), S1ChordAngle.from_radians(0.1)) == S2Point.new(0.9044725006561222, 0.32929580287571647, 0.27109734370756644)
# Antipodal endpoints: the direction comes from the symbolic perturbation in
# S2Point.robust_cross, as upstream's does. Upstream's GetPointOnLine and
# GetPointToLeft at v0.14.0 through tools/s2_oracle.cc.
expect S2Edge.point_on_line(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0), S1Angle.from_radians(0.5))
	== S2Point.new(0.87758256189037276, 0.0, 0.47942553860420301)
expect S2Edge.point_on_line_chord(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0), S1ChordAngle.from_radians(0.5))
	== S2Point.new(0.87758256189037276, 0.0, 0.47942553860420306)
expect {
	a = S2Point.new(0.2672612419124244, 0.53452248382484879, 0.80178372573727319)
	S2Edge.point_on_line(a, -a, S1Angle.from_radians(1.0))
		== S2Point.new(-0.15732319321568977, -0.31464638643137954, 0.9360806933069894)
}
expect S2Edge.point_to_left(S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, 0.0, -1.0), S1Angle.from_radians(0.25))
	== S2Point.new(-0.24740395925452299, 0.0, 0.96891242171064496)
expect S2Edge.point_to_left(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S1Angle.from_radians(0.2)) == S2Point.new(0.9800665778412416, 0.0, 0.1986693307950612)
expect S2Edge.point_to_left_chord(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S1ChordAngle.from_radians(0.2)) == S2Point.new(0.9800665778412416, 0.0, 0.1986693307950612)
expect S2Edge.point_to_right(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S1Angle.from_radians(0.2)) == S2Point.new(0.9800665778412416, 0.0, -0.1986693307950612)
expect S2Edge.point_to_right_chord(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S1ChordAngle.from_radians(0.2)) == S2Point.new(0.9800665778412416, 0.0, -0.1986693307950612)
expect S2Edge.point_to_left(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1Angle.from_radians(3.0)) == S2Point.new(-0.9899924966004456, 0.0, 0.14112000805986724)
expect S2Edge.point_to_left_chord(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_radians(3.0)) == S2Point.new(-0.9899924966004454, 0.0, 0.14112000805986752)
expect S2Edge.point_to_right(S2LatLng.from_degrees(30.0, 40.0).to_point(), S2LatLng.from_degrees(-20.0, 50.0).to_point(), S1Angle.from_radians(2.5)) == S2Point.new(-0.10720870748683226, -0.8537525899568696, -0.5095221370862506)
expect S2Edge.point_to_right_chord(S2LatLng.from_degrees(30.0, 40.0).to_point(), S2LatLng.from_degrees(-20.0, 50.0).to_point(), S1ChordAngle.from_radians(2.5)) == S2Point.new(-0.107208707486832, -0.8537525899568699, -0.5095221370862507)
expect S2Edge.point_on_ray(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1Angle.from_radians(0.5)) == S2Point.new(0.8775825618903728, 0.479425538604203, 0.0)
expect S2Edge.point_on_ray_chord(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_radians(0.5)) == S2Point.new(0.8775825618903728, 0.47942553860420306, 0.0)
expect S2Edge.point_on_ray(S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, -1.0, 0.0), S1Angle.from_radians(2.0)) == S2Point.new(0.0, -0.9092974268256817, -0.4161468365471424)
expect S2Edge.point_on_ray_chord(S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, -1.0, 0.0), S1ChordAngle.from_radians(2.0)) == S2Point.new(0.0, -0.9092974268256817, -0.41614683654714235)
# Interpolation, extrapolating as upstream's InterpolateCanExtrapolate does.
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 1.5) == S2Point.new(-0.7071067811865475, 0.7071067811865476, -0.0)
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), -1.0) == S2Point.new(6.123233995736766e-17, -1.0, 0.0)
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 3.0) == S2Point.new(-1.8369701987210297e-16, -1.0, 0.0)
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), 3.0) == S2Point.new(-0.7071067811865475, 0.7071067811865476, -0.0)
expect S2Edge.interpolate(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 0.3333333333333333) == S2Point.new(0.8660254037844387, 0.49999999999999994, 0.0)
expect S2Edge.interpolate(S2LatLng.from_degrees(10.0, 10.0).to_point(), S2LatLng.from_degrees(20.0, 30.0).to_point(), 0.25) == S2Point.new(0.9431993088895986, 0.24976190665198225, 0.21907545206104242)
# Edge pairs from upstream's EdgePairMinDistance and EdgePairMaxDistance tests,
# plus two disjoint pairs. Crossing pairs, shared vertices, degenerate edges
# and antipodal crossings are among them.
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.585786437626905))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(0.9999999999999998))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize()) == (S2Point.new(0.7071067811865475, 0.0, 0.7071067811865475), S2Point.new(1.0, 0.0, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.585786437626905))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(0.9999999999999998))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize()) == (S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.7071067811865475, 0.0, 0.7071067811865475))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(2.0))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(2.0))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()) == (S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.0))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(2.0))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize()) == (S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.True
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.0))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(0.9999999999999998))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize()) == (S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.True
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(1.9999999999999996))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(4.0))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize()) == (S2Point.new(0.7071067811865475, -0.7071067811865475, 0.0), S2Point.new(-0.7071067811865475, -0.7071067811865475, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(-1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(2.9999999999999996))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(-1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(4.0))
expect S2Edge.edge_pair_closest_points(S2Point.new(-1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == (S2Point.new(-0.7071067811865475, 0.0, 0.7071067811865475), S2Point.new(0.7071067811865475, 0.7071067811865475, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(-1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(2.9999999999999996))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(4.0))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize()) == (S2Point.new(0.7071067811865475, 0.0, 0.7071067811865475), S2Point.new(-0.7071067811865475, -0.7071067811865475, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(2.9999999999999996))
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(4.0))
expect S2Edge.edge_pair_closest_points(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize()) == (S2Point.new(0.7071067811865475, 0.0, 0.7071067811865475), S2Point.new(-0.7071067811865475, 0.7071067811865475, 0.0))
expect S2Edge.is_edge_pair_distance_less(S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, 5.0).to_point(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.00030460968721752167))
expect S2Edge.update_edge_pair_max_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, 5.0).to_point(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(0.03787947561918618))
expect S2Edge.edge_pair_closest_points(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, 5.0).to_point()) == (S2Point.new(0.9961946980917454, 0.08715574274765815, 0.0), S2Point.new(0.9960429728140489, 0.08714246850588939, 0.01745240643728351))
expect S2Edge.is_edge_pair_distance_less(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, 5.0).to_point(), S1ChordAngle.from_length2(0.001)) == Bool.True
expect S2Edge.update_edge_pair_min_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(2.0, 12.0).to_point(), S2LatLng.from_degrees(3.0, 20.0).to_point(), S1ChordAngle.from_length2(4.0)) == Ok(S1ChordAngle.from_length2(0.002435949740175753))
expect S2Edge.update_edge_pair_max_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(2.0, 12.0).to_point(), S2LatLng.from_degrees(3.0, 20.0).to_point(), S1ChordAngle.negative()) == Ok(S1ChordAngle.from_length2(0.12319039058452415))
expect S2Edge.edge_pair_closest_points(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(2.0, 12.0).to_point(), S2LatLng.from_degrees(3.0, 20.0).to_point()) == (S2Point.new(0.984807753012208, 0.17364817766693033, 0.0), S2Point.new(0.9775517396441024, 0.20778503663329906, 0.03489949670250097))
expect S2Edge.is_edge_pair_distance_less(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(2.0, 12.0).to_point(), S2LatLng.from_degrees(3.0, 20.0).to_point(), S1ChordAngle.from_length2(0.001)) == Bool.False
expect S2Edge.update_edge_pair_min_distance(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(0.0)) == Err(Unchanged)
expect S2Edge.update_edge_pair_max_distance(S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize(), S2Point.new(0.0, 0.0, 1.0).normalize(), S1ChordAngle.from_length2(4.0)) == Err(Unchanged)
expect S2Edge.update_edge_pair_min_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(2.0, 12.0).to_point(), S2LatLng.from_degrees(3.0, 20.0).to_point(), S1ChordAngle.from_length2(1.0e-06)) == Err(Unchanged)
# The cases of upstream's EdgeBNearEdgeA test, whose edges are "lat:lng" in
# degrees and whose tolerances are in degrees.
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(5.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, -5.0).to_point(), S2LatLng.from_degrees(5.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, -5.0).to_point(), S1Angle.from_radians(1.7453292519943295e-08)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(5.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, -5.0).to_point(), S2LatLng.from_degrees(10.0, -5.0).to_point(), S2LatLng.from_degrees(5.0, 5.0).to_point(), S1Angle.from_radians(1.7453292519943295e-08)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(10.0, 0.0).to_point(), S2LatLng.from_degrees(-10.0, 0.0).to_point(), S2LatLng.from_degrees(2.0, 1.0).to_point(), S2LatLng.from_degrees(-2.0, 1.0).to_point(), S1Angle.from_radians(0.017453292519943295)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(2.0, 1.0).to_point(), S2LatLng.from_degrees(-2.0, 1.0).to_point(), S2LatLng.from_degrees(10.0, 0.0).to_point(), S2LatLng.from_degrees(-10.0, 0.0).to_point(), S1Angle.from_radians(0.017453292519943295)) == Bool.False
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(10.0, 0.0).to_point(), S2LatLng.from_degrees(-10.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 1.5).to_point(), S2LatLng.from_degrees(0.0, -1.5).to_point(), S1Angle.from_radians(0.017453292519943295)) == Bool.False
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(10.0, 0.0).to_point(), S2LatLng.from_degrees(-10.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 1.5).to_point(), S2LatLng.from_degrees(0.0, -1.5).to_point(), S1Angle.from_radians(0.03490658503988659)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(89.0, 1.0).to_point(), S2LatLng.from_degrees(-89.0, 1.0).to_point(), S2LatLng.from_degrees(89.0, 2.0).to_point(), S2LatLng.from_degrees(-89.0, 2.0).to_point(), S1Angle.from_radians(0.008726646259971648)) == Bool.False
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(89.0, 1.0).to_point(), S2LatLng.from_degrees(-89.0, 1.0).to_point(), S2LatLng.from_degrees(89.0, 2.0).to_point(), S2LatLng.from_degrees(-89.0, 2.0).to_point(), S1Angle.from_radians(0.026179938779914945)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(89.0, 1.0).to_point(), S2LatLng.from_degrees(-89.0, 1.0).to_point(), S2LatLng.from_degrees(-89.0, 2.0).to_point(), S2LatLng.from_degrees(89.0, 2.0).to_point(), S1Angle.from_radians(0.026179938779914945)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(0.0, -100.0).to_point(), S2LatLng.from_degrees(0.0, 100.0).to_point(), S2LatLng.from_degrees(5.0, -80.0).to_point(), S2LatLng.from_degrees(-5.0, 80.0).to_point(), S1Angle.from_radians(1.2217304763960306)) == Bool.False
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(0.0, -100.0).to_point(), S2LatLng.from_degrees(0.0, 100.0).to_point(), S2LatLng.from_degrees(1.0, -35.0).to_point(), S2LatLng.from_degrees(10.0, 35.0).to_point(), S1Angle.from_radians(1.2217304763960306)) == Bool.False
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(0.0, -100.0).to_point(), S2LatLng.from_degrees(0.0, 100.0).to_point(), S2LatLng.from_degrees(5.0, 80.0).to_point(), S2LatLng.from_degrees(-5.0, -80.0).to_point(), S1Angle.from_radians(1.2217304763960306)) == Bool.False
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(40.0, 0.0).to_point(), S2LatLng.from_degrees(-5.0, 0.0).to_point(), S2LatLng.from_degrees(39.0, 0.975).to_point(), S2LatLng.from_degrees(-1.0, 0.975).to_point(), S1Angle.from_radians(0.017453292519943295)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(10.0, 0.0).to_point(), S2LatLng.from_degrees(-10.0, 0.0).to_point(), S2LatLng.from_degrees(-0.4, 0.975).to_point(), S2LatLng.from_degrees(0.4, 0.975).to_point(), S1Angle.from_radians(0.017453292519943295)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(1.0, 0.0).to_point(), S2LatLng.from_degrees(0.9, 0.0).to_point(), S2LatLng.from_degrees(1.1, 0.0).to_point(), S1Angle.from_radians(0.004363323129985824)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(1.0, 0.0).to_point(), S2LatLng.from_degrees(1.1, 0.0).to_point(), S2LatLng.from_degrees(1.2, 0.0).to_point(), S1Angle.from_radians(0.004363323129985824)) == Bool.True
expect S2Edge.is_edge_b_near_edge_a(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(1.0, 0.0).to_point(), S2LatLng.from_degrees(1.2, 0.0).to_point(), S2LatLng.from_degrees(1.1, 0.0).to_point(), S1Angle.from_radians(0.004363323129985824)) == Bool.True
# Crossings, with the vertex crossings that shared endpoints give.
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.1).normalize(), S2Point.new(-1.0, 0.0, 0.1).normalize(), S2Point.new(0.0, 1.0, 0.1).normalize(), S2Point.new(0.0, -1.0, 0.1).normalize()) == 1
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.1).normalize(), S2Point.new(-1.0, 0.0, 0.1).normalize(), S2Point.new(0.0, 1.0, 0.1).normalize(), S2Point.new(0.0, -1.0, 0.1).normalize()) == Bool.True
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 0
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == Bool.False
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 0
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == Bool.False
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0)) == 0
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0)) == Bool.False
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0)) == 0
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0)) == Bool.False
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 0
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == Bool.True
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == -1
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == Bool.True
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, -1.0), S2Point.new(0.0, 1.0, 0.0)) == 0
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, -1.0), S2Point.new(0.0, 1.0, 0.0)) == Bool.True
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, -1.0), S2Point.new(0.0, 1.0, 0.0)) == 1
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, -1.0), S2Point.new(0.0, 1.0, 0.0)) == Bool.True
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)) == 0
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)) == Bool.True
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)) == 1
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)) == Bool.True
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == 0
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == Bool.True
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == -1
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == Bool.True
expect S2Edge.crossing_sign(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == -1
expect S2Edge.vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == Bool.False
expect S2Edge.signed_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 0
expect S2Edge.edge_or_vertex_crossing(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == Bool.False
expect S2Edge.crossing_sign(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point()) == 0
expect S2Edge.vertex_crossing(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point()) == Bool.False
expect S2Edge.signed_vertex_crossing(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point()) == 0
expect S2Edge.edge_or_vertex_crossing(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point()) == Bool.False
expect S2Edge.crossing_sign(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 5.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point()) == 1
expect S2Edge.edge_or_vertex_crossing(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 5.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point()) == Bool.True
expect S2Edge.crossing_sign(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point()) == 1
expect S2Edge.edge_or_vertex_crossing(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point()) == Bool.True
expect S2Edge.crossing_sign(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point()) == 1
expect S2Edge.edge_or_vertex_crossing(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point()) == Bool.True
# Intersections from upstream's GetIntersection. The comment on each says
# whether upstream decided it in rounded arithmetic or needed exact
# arithmetic.
# Exact.
expect S2Edge.intersection(S2Point.new(1.0, 0.0, 0.2).normalize(), S2Point.new(-1.0, 0.0, 0.2).normalize(), S2Point.new(0.0, 1.0, 0.2).normalize(), S2Point.new(0.0, -1.0, 0.2).normalize()) == S2Point.new(0.0, 0.0, 1.0)
# Rounded.
expect S2Edge.intersection(S2LatLng.from_degrees(0.0, -1.0).to_point(), S2LatLng.from_degrees(0.0, 1.0).to_point(), S2LatLng.from_degrees(1.0e-14, -1.0).to_point(), S2LatLng.from_degrees(-1.0e-14, 1.0).to_point()) == S2Point.new(0.9999999999999999, 0.0, 0.0)
# Rounded.
expect S2Edge.intersection(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point()) == S2Point.new(0.9961946980917455, 0.08715574274765817, 0.0)
# Rounded.
expect S2Edge.intersection(S2LatLng.from_degrees(10.0, 10.0).to_point(), S2LatLng.from_degrees(-10.0, -10.0).to_point(), S2LatLng.from_degrees(-10.0, 10.0).to_point(), S2LatLng.from_degrees(10.0, -10.0).to_point()) == S2Point.new(1.0, 0.0, 0.0)
# Rounded.
expect S2Edge.intersection(S2LatLng.from_degrees(0.0, -1.0e-10).to_point(), S2LatLng.from_degrees(0.0, 1.0e-10).to_point(), S2LatLng.from_degrees(1.0e-20, -1.0e-10).to_point(), S2LatLng.from_degrees(-1.0e-20, 1.0e-10).to_point()) == S2Point.new(1.0, 0.0, 0.0)
# Exact.
expect S2Edge.intersection(S2LatLng.from_degrees(0.0, -60.0).to_point(), S2LatLng.from_degrees(0.0, 60.0).to_point(), S2LatLng.from_degrees(80.0, 0.0).to_point(), S2LatLng.from_degrees(-1.0e-300, 0.0).to_point()) == S2Point.new(1.0, -0.0, -0.0)
# Exact.
expect S2Edge.intersection(S2LatLng.from_degrees(30.0, -170.0).to_point(), S2LatLng.from_degrees(-30.0, 170.0).to_point(), S2LatLng.from_degrees(-30.0, -170.0).to_point(), S2LatLng.from_degrees(30.0, 170.0).to_point()) == S2Point.new(-1.0, -0.0, -0.0)
# Rounded.
expect S2Edge.intersection(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(1.0e-09, 1.0e-09).to_point(), S2LatLng.from_degrees(1.0e-09, 0.0).to_point(), S2LatLng.from_degrees(0.0, 1.0e-09).to_point()) == S2Point.new(1.0, 8.726646259971649e-12, 8.726646259971649e-12)
# compare_edge_pair_distance, which lives here rather than in S2Predicates.
expect S2Edge.compare_edge_pair_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, 5.0).to_point(), S1ChordAngle.from_length2(0.0003)) == 1
expect S2Edge.compare_edge_pair_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S2LatLng.from_degrees(10.0, 5.0).to_point(), S1ChordAngle.from_length2(0.0004)) == -1
expect S2Edge.compare_edge_pair_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point(), S2LatLng.from_degrees(-1.0, 5.0).to_point(), S2LatLng.from_degrees(1.0, 5.0).to_point(), S1ChordAngle.from_length2(1.0e-10)) == -1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(0.0)) == 0

# The cases of upstream's CompareEdgePairDistance.Coverage test. The last
# eight need exact arithmetic.
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(1.0, 1.0e-100, -1.0e-99), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(1.0, 1.0e-100, -1.0e-99), S1ChordAngle.from_length2(0.9193953882637206)) == -1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(1.0, 1.0e-100, -1.0e-99), S1ChordAngle.from_length2(-1.0)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(0.9193953882637206)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S1ChordAngle.from_length2(0.9193953882637206)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(0.9193953882637206)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(1.000000000000002e-200)) == -1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(9.99999999999998e-201)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(1.000000000000002e-200)) == -1
expect S2Edge.compare_edge_pair_distance(S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S1ChordAngle.from_length2(9.99999999999998e-201)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(1.000000000000002e-200)) == -1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(9.99999999999998e-201)) == 1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S1ChordAngle.from_length2(1.000000000000002e-200)) == -1
expect S2Edge.compare_edge_pair_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(1.0, 1.0e-100, 1.0e-99), S1ChordAngle.from_length2(9.99999999999998e-201)) == 1

# A current value equal to the distance is not improved on.
expect S2Edge.update_min_interior_distance(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.367006838144548)) == Err(Unchanged)
expect S2Edge.update_min_distance(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.367006838144548)) == Err(Unchanged)
expect S2Edge.update_min_interior_distance(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 40.0).to_point(), S1ChordAngle.from_length2(0.030384493975583876)) == Err(Unchanged)
expect S2Edge.update_min_distance(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 40.0).to_point(), S1ChordAngle.from_length2(0.030384493975583876)) == Err(Unchanged)

## Half of `F64` machine epsilon: the largest relative error of one rounded
## operation.
dbl_err : F64
dbl_err = 1.1102230246251565e-16

## `F64` machine epsilon.
f64_epsilon : F64
f64_epsilon = 2.220446049250313e-16

## The square root of 3.
sqrt3 : F64
sqrt3 = 1.7320508075688772

## The unit tangent at `a` pointing along the great circle towards `b`. It is
## well defined even when `a` and `b` are antipodal or nearly so.
line_direction : S2Point, S2Point -> S2Point
line_direction = |a, b| a.robust_cross(b).cross(a).normalize()

## Upstream's `AlwaysUpdateMinDistance`: the distance from `x` to the edge
## `ab`. With `always` false it answers `Err(Unchanged)` unless the distance
## is less than `min_dist`; with `always` true it ignores `min_dist`.
min_distance : Bool, S2Point, S2Point, S2Point, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
min_distance = |always, x, a, b, min_dist| {
	xa2 = (x - a).norm2()
	xb2 = (x - b).norm2()
	match min_interior_distance(always, x, a, b, xa2, xb2, min_dist) {
		Ok(d) => Ok(d)
		Err(Unchanged) => {
			# The minimum is at one of the endpoints.
			dist2 = xa2.min(xb2)
			if !always and dist2 >= min_dist.length2() {
				Err(Unchanged)
			} else {
				Ok(S1ChordAngle.from_length2(dist2))
			}
		}
	}
}

## Upstream's `AlwaysUpdateMinInteriorDistance`: the distance from `x` to the
## edge `ab` when the closest point is interior to the edge. `xa2` and `xb2`
## are the squared distances from `x` to `a` and `b`.
min_interior_distance : Bool, S2Point, S2Point, S2Point, F64, F64, S1ChordAngle -> Try(S1ChordAngle, [Unchanged])
min_interior_distance = |always, x, a, b, xa2, xb2, min_dist| {
	# The closest point can be interior only when the planar angles XAB and
	# XBA are both acute: |XA^2 - XB^2| < AB^2. The test is conservative, so
	# that rounding cannot hide an interior minimum.
	ab2 = (a - b).norm2()
	max_error = 4.75 * f64_epsilon * (xa2 + xb2 + ab2) + 8.0 * f64_epsilon * f64_epsilon
	if (xa2 - xb2).abs() >= ab2 + max_error {
		return Err(Unchanged)
	}

	# The squared distance from x to the plane of the edge is a lower bound
	# on the chord distance to the edge, and it is cheap.
	c = a.robust_cross(b)
	c2 = c.norm2()
	x_dot_c = x.dot(c)
	x_dot_c2 = x_dot_c * x_dot_c
	if !always and x_dot_c2 > c2 * min_dist.length2() {
		return Err(Unchanged)
	}

	# The exact test for the interior case.
	cx = c.cross(x)
	if (a - x).dot(cx) >= 0.0 or (b - x).dot(cx) <= 0.0 {
		return Err(Unchanged)
	}

	# The squared chord length XR^2 = XQ^2 + QR^2, where Q is x projected
	# onto the plane of the edge and R the closest point of the edge.
	qr = 1.0 - (cx.norm2() / c2).sqrt()
	dist2 = (x_dot_c2 / c2) + (qr * qr)
	if !always and dist2 >= min_dist.length2() {
		return Err(Unchanged)
	}
	Ok(S1ChordAngle.from_length2(dist2))
}

## The largest error in a distance from `min_interior_distance`, in
## squared-chord units.
min_interior_distance_max_error : S1ChordAngle -> F64
min_interior_distance_max_error = |dist| {
	# Beyond 90 degrees the minimum is always at an endpoint.
	if dist >= S1ChordAngle.right() {
		return 0.0
	}
	# a and b are the parts of the chord perpendicular and parallel to the
	# plane of the edge.
	b = (0.5 * dist.length2()).min(1.0)
	a = (b * (2.0 - b)).sqrt()
	((2.5 + 2.0 * sqrt3 + 8.5 * a) * a
		+ (2.0 + 2.0 * sqrt3 / 3.0 + 6.5 * (1.0 - b)) * b
		+ (23.0 + 16.0 / sqrt3) * f64_epsilon)
		* f64_epsilon
}

## Upstream's `CompareEdges`: a total order on edges that ignores their
## direction, used to break ties between edges of equal length.
edge_less : S2Point, S2Point, S2Point, S2Point -> Bool
edge_less = |a0, a1, b0, b1| {
	(pa0, pa1) = if (a0 >= a1) (a1, a0) else (a0, a1)
	(pb0, pb1) = if (b0 >= b1) (b1, b0) else (b0, b1)
	pa0 < pb0 or (pa0 == pb0 and pa1 < pb1)
}

## The intersection in rounded arithmetic, when its error bound is within
## `intersection_error`. The longer edge goes first, since its normal is the
## more accurate.
intersection_stable : S2Point, S2Point, S2Point, S2Point -> Try(S2Point, [Uncertain])
intersection_stable = |a0, a1, b0, b1| {
	a_len2 = (a1 - a0).norm2()
	b_len2 = (b1 - b0).norm2()
	if a_len2 < b_len2 or (a_len2 == b_len2 and edge_less(a0, a1, b0, b1)) {
		intersection_stable_sorted(b0, b1, a0, a1)
	} else {
		intersection_stable_sorted(a0, a1, b0, b1)
	}
}

## The signed distance from `x` to the plane of the edge `a0a1`, scaled by
## the length `a_norm_len` of its normal `a_norm`, and the largest error in
## it. Measured from the nearer endpoint, for accuracy.
projection : S2Point, S2Point, F64, S2Point, S2Point -> (F64, F64)
projection = |x, a_norm, a_norm_len, a0, a1| {
	x0 = x - a0
	x1 = x - a1
	x0_dist2 = x0.norm2()
	x1_dist2 = x1.norm2()
	(dist, result) =
		if x0_dist2 < x1_dist2 or (x0_dist2 == x1_dist2 and x0 < x1) {
			(x0_dist2.sqrt(), x0.dot(a_norm))
		} else {
			(x1_dist2.sqrt(), x1.dot(a_norm))
		}
	error = (((3.5 + 2.0 * sqrt3) * a_norm_len + 32.0 * sqrt3 * dbl_err) * dist + 1.5 * result.abs()) * dbl_err
	(result, error)
}

## The intersection of `b0b1` with the plane of `a0a1`, found by
## interpolating between the signed distances of `b0` and `b1` from that
## plane. Requires that `a0a1` is the longer edge.
intersection_stable_sorted : S2Point, S2Point, S2Point, S2Point -> Try(S2Point, [Uncertain])
intersection_stable_sorted = |a0, a1, b0, b1| {
	a_norm = (a0 - a1).cross(a0 + a1)
	a_norm_len = a_norm.norm()
	b_len = (b1 - b0).norm()
	(b0_signed, b0_error) = projection(b0, a_norm, a_norm_len, a0, a1)
	(b1_signed, b1_error) = projection(b1, a_norm, a_norm_len, a0, a1)
	# Make b0_dist positive and b1_dist negative.
	(b0_dist, b1_dist) = if (b0_signed < b1_signed) (-b0_signed, -b1_signed) else (b0_signed, b1_signed)
	dist_sum = b0_dist - b1_dist
	error_sum = b0_error + b1_error
	if dist_sum <= error_sum {
		return Err(Uncertain)
	}
	x = b1 * b0_dist - b0 * b1_dist
	error =
		b_len * (b0_dist * b1_error - b1_dist * b0_error).abs() / (dist_sum - error_sum)
			+ 2.0 * dbl_err * dist_sum
	x_len2 = x.norm2()
	# The smallest positive normal F64.
	if x_len2 < 2.2250738585072014e-308 {
		return Err(Uncertain)
	}
	x_len = x_len2.sqrt()
	if error > (8.0 * dbl_err - dbl_err) * x_len {
		return Err(Uncertain)
	}
	Ok(x * (1.0 / x_len))
}

## The intersection in exact arithmetic: `(a0 x a1) x (b0 x b1)`, rounded
## once. When that is exactly zero, the edges are collinear and share a
## stretch, and the answer is the smallest of the endpoints that lie on both
## edges.
intersection_exact : S2Point, S2Point, S2Point, S2Point -> S2Point
intersection_exact = |a0, a1, b0, b1| {
	a_norm_xf = S2Exact.cross(coords(a0), coords(a1))
	b_norm_xf = S2Exact.cross(coords(b0), coords(b1))
	x_xf = S2Exact.cross_exact(a_norm_xf, b_norm_xf)
	if !S2Exact.is_zero(x_xf) {
		return exact_to_point(x_xf) * S2Predicates.sign(a0, a1, b1).to_f64()
	}
	a_norm = {
		p = exact_to_point(a_norm_xf)
		if (p == S2Point.zero()) symbolic_cross(a0, a1) else p
	}
	b_norm = {
		p = exact_to_point(b_norm_xf)
		if (p == S2Point.zero()) symbolic_cross(b0, b1) else p
	}
	# Larger than any unit-length point.
	start = S2Point.new(10.0, 10.0, 10.0)
	[
		(a0, S2Predicates.ordered_ccw(b0, a0, b1, b_norm)),
		(a1, S2Predicates.ordered_ccw(b0, a1, b1, b_norm)),
		(b0, S2Predicates.ordered_ccw(a0, b0, a1, a_norm)),
		(b1, S2Predicates.ordered_ccw(a0, b1, a1, a_norm)),
	]
		.fold(start, |best, (p, on_both)| if (on_both and p < best) p else best)
}

## The three coordinates of a point, the form `S2Exact` takes.
coords : S2Point -> (F64, F64, F64)
coords = |p| (p.x(), p.y(), p.z())

## An exact vector rounded to doubles by upstream's `NormalizableFromExact`,
## and then normalized.
exact_to_point : (List(F64), List(F64), List(F64)) -> S2Point
exact_to_point = |v| {
	(x, y, z) = S2Exact.normalizable_from_exact(v, 0)
	S2Point.new(x, y, z).normalize()
}

## Upstream's `SymbolicCrossProd`: the direction of `a x b` for exactly
## proportional `a` and `b` under the symbolic perturbation that `sign` uses.
## Requires `a != b`.
symbolic_cross : S2Point, S2Point -> S2Point
symbolic_cross = |a, b| {
	(x, y, z) = S2Exact.symbolic_cross(coords(a), coords(b))
	S2Point.new(x, y, z)
}

import S1Angle
import S1ChordAngle
import S2Point
import S2Predicates

## Operations on geodesic edges: whether two cross, where they cross, and how
## far a point is from one.
##
## An edge is the shorter great-circle arc between two unit-length points. The
## crossing tests are exact, because they are built on `S2Predicates.sign`
## rather than on comparisons of rounded determinants.
S2Edge := [].{

	## The error bound on the tangent test in `crossing_sign`.
	tangent_error : F64
	tangent_error = 4.612644198131179e-16

	## How the edges `ab` and `cd` meet.
	##
	## - `1` when they cross at a point interior to both
	## - `0` when they share exactly one endpoint
	## - `-1` when they do not cross
	##
	## Degenerate edges, where `a == b` or `c == d`, never cross.
	crossing_sign : S2Point, S2Point, S2Point, S2Point -> I8
	crossing_sign = |a, b, c, d| {
		a_cross_b = a.cross(b)
		acb = -S2Predicates.triage_sign(c, a_cross_b)
		bda = S2Predicates.triage_sign(d, a_cross_b)

		# The common case: c and d sit on opposite sides of the great circle
		# through a and b, so no crossing is possible.
		if acb == -bda and bda != 0 {
			return -1
		}

		# Test whether cd lies entirely beyond one end of ab, which rules out
		# a crossing far more cheaply than exact arithmetic would.
		norm = a.robust_cross(b)
		a_tangent = a.cross(norm)
		b_tangent = norm.cross(b)
		beyond_a = c.dot(a_tangent) > S2Edge.tangent_error and d.dot(a_tangent) > S2Edge.tangent_error
		beyond_b = c.dot(b_tangent) > S2Edge.tangent_error and d.dot(b_tangent) > S2Edge.tangent_error
		if beyond_a or beyond_b {
			return -1
		}

		# A shared endpoint is a vertex crossing, not an edge crossing.
		if a == c or a == d or b == c or b == d {
			return 0
		}
		if a == b or c == d {
			return -1
		}

		# The four triangles acb, cbd, bda, dac must agree in orientation.
		exact_acb = if acb == 0 {
			-S2Predicates.expensive_sign(a, b, c)
		} else {
			acb
		}
		exact_bda = if bda == 0 {
			S2Predicates.expensive_sign(a, b, d)
		} else {
			bda
		}
		if exact_bda != exact_acb {
			return -1
		}
		c_cross_d = c.cross(d)
		if -S2Predicates.sign_with_cross(c, d, b, c_cross_d) != exact_acb {
			return -1
		}
		if S2Predicates.sign_with_cross(c, d, a, c_cross_d) != exact_acb {
			return -1
		}
		1
	}

	## Whether two edges that share an endpoint should be counted as crossing.
	##
	## The rule makes a shared vertex belong to exactly one of the two edges,
	## so that a point-in-polygon test that counts crossings gets a consistent
	## answer along a boundary.
	vertex_crossing : S2Point, S2Point, S2Point, S2Point -> Bool
	vertex_crossing = |a, b, c, d| {
		if a == b or c == d {
			return Bool.False
		}
		if a == c {
			b == d or S2Predicates.ordered_ccw(a.ortho(), d, b, a)
		} else if b == d {
			S2Predicates.ordered_ccw(b.ortho(), c, a, b)
		} else if a == d {
			b == c or S2Predicates.ordered_ccw(a.ortho(), c, b, a)
		} else if b == c {
			S2Predicates.ordered_ccw(b.ortho(), d, a, b)
		} else {
			Bool.False
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

	## The point where two crossing edges meet.
	##
	## Only meaningful when `crossing_sign` reports a crossing. The result is
	## accurate to about 1e-15 radians for edges that meet at a healthy angle,
	## and degrades as the angle between them shrinks.
	intersection : S2Point, S2Point, S2Point, S2Point -> S2Point
	intersection = |a0, a1, b0, b1| {
		a_norm = a0.robust_cross(a1)
		b_norm = b0.robust_cross(b1)
		x = a_norm.robust_cross(b_norm).normalize()

		# Of the two antipodal candidates, take the one on the same side as
		# the four endpoints.
		if x.dot(a0 + a1 + b0 + b1) < 0.0 {
			-x
		} else {
			x
		}
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

	## The point at distance `r` from `a` along the great circle towards `b`.
	point_on_line : S2Point, S2Point, S1Angle -> S2Point
	point_on_line = |a, b, r| {
		direction = a.robust_cross(b).cross(a).normalize()
		S2Edge.point_on_ray(a, direction, r)
	}

	## The point at distance `r` from `a` in the direction `direction`, which
	## must be a unit vector perpendicular to `a`.
	point_on_ray : S2Point, S2Point, S1Angle -> S2Point
	point_on_ray = |a, direction, r|
		(a * r.radians().cos() + direction * r.radians().sin()).normalize()

	## The point of the edge `ab` closest to `x`.
	project : S2Point, S2Point, S2Point -> S2Point
	project = |x, a, b| {
		if x == a or x == b {
			return x
		}
		a_cross_b = a.robust_cross(b)
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
	distance_to_edge : S2Point, S2Point, S2Point -> S1ChordAngle
	distance_to_edge = |x, a, b| S1ChordAngle.from_points(x, S2Edge.project(x, a, b))

	## The distance from `x` to the furthest point of the edge `ab`, which is
	## always one of its endpoints.
	max_distance_to_edge : S2Point, S2Point, S2Point -> S1ChordAngle
	max_distance_to_edge = |x, a, b|
		S1ChordAngle.from_points(x, a).max(S1ChordAngle.from_points(x, b))

	## True when `x` is within `limit` of the edge `ab`.
	is_distance_less : S2Point, S2Point, S2Point, S1ChordAngle -> Bool
	is_distance_less = |x, a, b, limit| S2Edge.distance_to_edge(x, a, b) < limit
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
	S2Edge.simple_crossing(a, b, c, d)
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	d = S2Point.new(0.0, 0.0, -1.0)
	!S2Edge.simple_crossing(a, b, c, d)
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

import S1Angle
import Internal/S2Math

## A point in three-dimensional Euclidean space.
##
## Points that lie on the unit sphere are the ones S2 treats as geographic
## positions; the type itself does not enforce unit length, so intermediate
## results such as cross products can be held in it unnormalized.
S2Point := { x : F64, y : F64, z : F64 }.{

	new : F64, F64, F64 -> S2Point
	new = |x, y, z| { x: x, y: y, z: z }

	## The zero vector, which is not a valid position on the sphere.
	zero : () -> S2Point
	zero = || { x: 0.0, y: 0.0, z: 0.0 }

	## S2's reference point for containment tests: a fixed point chosen to sit
	## off every cell boundary and away from both poles.
	origin : () -> S2Point
	origin = || {
		x: -0.0099994664350250197,
		y: 0.0025924542609324121,
		z: 0.99994664350250195,
	}

	x : S2Point -> F64
	x = |p| p.x

	y : S2Point -> F64
	y = |p| p.y

	z : S2Point -> F64
	z = |p| p.z

	## Coordinate `0` is `x`, `1` is `y`, and `2` is `z`.
	coord : S2Point, U64 -> F64
	coord = |p, k|
		if k == 0 {
			p.x
		} else if k == 1 {
			p.y
		} else {
			p.z
		}

	## A copy of the point with coordinate `k` replaced.
	with_coord : S2Point, U64, F64 -> S2Point
	with_coord = |p, k, v|
		if k == 0 {
			{ x: v, y: p.y, z: p.z }
		} else if k == 1 {
			{ x: p.x, y: v, z: p.z }
		} else {
			{ x: p.x, y: p.y, z: v }
		}

	plus : S2Point, S2Point -> S2Point
	plus = |a, b| { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

	minus : S2Point, S2Point -> S2Point
	minus = |a, b| { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }

	## Scales the vector. Written `p * 2.0`.
	times : S2Point, F64 -> S2Point
	times = |p, k| { x: p.x * k, y: p.y * k, z: p.z * k }

	div_by : S2Point, F64 -> S2Point
	div_by = |p, k| { x: p.x / k, y: p.y / k, z: p.z / k }

	negate : S2Point -> S2Point
	negate = |p| { x: -p.x, y: -p.y, z: -p.z }

	## The componentwise absolute value.
	abs : S2Point -> S2Point
	abs = |p| { x: p.x.abs(), y: p.y.abs(), z: p.z.abs() }

	dot : S2Point, S2Point -> F64
	dot = |a, b| a.x * b.x + a.y * b.y + a.z * b.z

	cross : S2Point, S2Point -> S2Point
	cross = |a, b| {
		x: a.y * b.z - a.z * b.y,
		y: a.z * b.x - a.x * b.z,
		z: a.x * b.y - a.y * b.x,
	}

	norm2 : S2Point -> F64
	norm2 = |p| p.x * p.x + p.y * p.y + p.z * p.z

	norm : S2Point -> F64
	norm = |p| p.norm2().sqrt()

	## The unit vector in the same direction. The zero vector maps to itself.
	normalize : S2Point -> S2Point
	normalize = |p| {
		n = p.norm()
		if n == 0.0 {
			p
		} else {
			{ x: p.x / n, y: p.y / n, z: p.z / n }
		}
	}

	## The index of the coordinate with the largest magnitude, with ties going
	## to the later coordinate.
	largest_abs_component : S2Point -> U64
	largest_abs_component = |p| {
		magnitude = p.abs()
		if magnitude.x > magnitude.y {
			if magnitude.x > magnitude.z {
				0
			} else {
				2
			}
		} else if magnitude.y > magnitude.z {
			1
		} else {
			2
		}
	}

	## True when the point is unit length to within the error `normalize`
	## can leave behind.
	is_unit_length : S2Point -> Bool
	is_unit_length = |p| (p.norm2() - 1.0).abs() <= 1.1102230246251565e-15

	## The angle between the two vectors, in `[0, pi]`.
	##
	## Computed from `atan2` of the cross and dot products rather than from
	## `acos` alone, which keeps it accurate for nearly parallel vectors.
	angle_to : S2Point, S2Point -> S1Angle
	angle_to = |a, b| S1Angle.from_radians(S2Math.atan2(a.cross(b).norm(), a.dot(b)))

	## A unit vector orthogonal to the point.
	##
	## The direction is chosen deterministically from the point's largest
	## component, so the same input always gives the same result.
	ortho : S2Point -> S2Point
	ortho = |a| {
		k = {
			largest = a.largest_abs_component()
			if largest == 0 {
				2
			} else {
				largest - 1
			}
		}
		temp = S2Point.new(0.012, 0.0053, 0.00457).with_coord(k, 1.0)
		a.cross(temp).normalize()
	}

	## A cross product that stays orthogonal to both inputs even when they are
	## nearly parallel or nearly opposite.
	##
	## `(b + a) x (b - a)` is twice `a x b` mathematically, but its two factors
	## are perpendicular for unit-length inputs, which is what makes it stable.
	## Exactly proportional inputs fall back to `ortho(a)`, so the result is
	## never zero.
	##
	## Upstream's current version escalates to exact arithmetic and symbolic
	## perturbation for the proportional case; this one does not, so the
	## direction it picks there is arbitrary rather than canonical.
	robust_cross : S2Point, S2Point -> S2Point
	robust_cross = |a, b| {
		result = (b + a).cross(b - a)
		if result == S2Point.zero() {
			a.ortho()
		} else {
			result
		}
	}

	## The point rotated `angle` counterclockwise about `axis`.
	rotate : S2Point, S2Point, S1Angle -> S2Point
	rotate = |p, axis, angle| {
		center = axis * p.dot(axis)
		dx = p - center
		dy = axis.cross(p)
		(dx * angle.radians().cos() + dy * angle.radians().sin() + center).normalize()
	}

	## An orthonormal frame with `z` as its third axis, returned as the triple
	## of column vectors `(x, y, z)`.
	frame : S2Point -> (S2Point, S2Point, S2Point)
	frame = |z_axis| {
		y_axis = z_axis.ortho()
		(y_axis.cross(z_axis), y_axis, z_axis)
	}

	## `p` expressed in the coordinates of the frame, which is the inverse of
	## `from_frame`.
	to_frame : (S2Point, S2Point, S2Point), S2Point -> S2Point
	to_frame = |(fx, fy, fz), p| S2Point.new(fx.dot(p), fy.dot(p), fz.dot(p))

	## The frame coordinates `q` expressed in the original coordinates.
	from_frame : (S2Point, S2Point, S2Point), S2Point -> S2Point
	from_frame = |(fx, fy, fz), q| fx * q.x + fy * q.y + fz * q.z

	is_eq : S2Point, S2Point -> Bool
	is_eq = |a, b| a.x == b.x and a.y == b.y and a.z == b.z

	## True when the angle between the points is at most `max_error` radians.
	approx_eq : S2Point, S2Point, F64 -> Bool
	approx_eq = |a, b, max_error| a.angle_to(b).radians() <= max_error

	## Orders points lexicographically by `(x, y, z)`, matching the ordering
	## upstream's symbolic perturbations are defined against.
	is_lt : S2Point, S2Point -> Bool
	is_lt = |a, b|
		if a.x != b.x {
			a.x < b.x
		} else if a.y != b.y {
			a.y < b.y
		} else {
			a.z < b.z
		}

	is_gt : S2Point, S2Point -> Bool
	is_gt = |a, b| b.is_lt(a)

	is_lte : S2Point, S2Point -> Bool
	is_lte = |a, b| !b.is_lt(a)

	is_gte : S2Point, S2Point -> Bool
	is_gte = |a, b| !a.is_lt(b)

	to_hash : S2Point, Hasher -> Hasher
	to_hash = |p, hasher| hasher
		.write_u64(p.x.to_bits())
		.write_u64(p.y.to_bits())
		.write_u64(p.z.to_bits())

	## The area of the spherical triangle `abc`, in steradians.
	##
	## Uses Girard's formula only for the skinny triangles where l'Huilier's
	## formula loses accuracy, which keeps the result good to about 1e-15 even
	## for triangles the size of a leaf cell. The side lengths come from
	## Kahan's stable angle formula, which stays accurate for nearly equal
	## points.
	triangle_area : S2Point, S2Point, S2Point -> F64
	triangle_area = |a, b, c| {
		sa = stable_angle(b, c)
		sb = stable_angle(c, a)
		sc = stable_angle(a, b)
		s = 0.5 * (sa + sb + sc)
		use_girard =
			if s >= 3e-4 {
				s2 = s * s
				dmin = s - sa.max(sb).max(sc)
				dmin < 1e-2 * s * s2 * s2
			} else {
				Bool.False
			}
		if use_girard {
			girard = S2Point.girard_area(a, b, c)
			dmin = s - sa.max(sb).max(sc)
			if dmin < s * (0.1 * (girard + 5e-15)) {
				return girard
			}
		}
		product =
			(0.5 * s).tan()
				* (0.5 * (s - sa)).tan()
				* (0.5 * (s - sb)).tan()
				* (0.5 * (s - sc)).tan()
		4.0 * product.max(0.0).sqrt().atan()
	}

	## The area of the spherical triangle `abc` by Girard's formula, the sum
	## of its angles less pi.
	girard_area : S2Point, S2Point, S2Point -> F64
	girard_area = |a, b, c| {
		ab = a.robust_cross(b)
		bc = b.robust_cross(c)
		ac = a.robust_cross(c)
		(ab.angle_to(ac).radians() - ab.angle_to(bc).radians() + bc.angle_to(ac).radians())
			.max(0.0)
	}

	## The area of the triangle `abc`, negated when the vertices wind
	## clockwise.
	##
	## The winding test here is the cheap rounded one, not the exact
	## `S2Predicates.sign`. It can pick the wrong sign for a triangle so
	## degenerate that its area is near zero, where the sign hardly matters;
	## use the predicate directly when it does.
	signed_area : S2Point, S2Point, S2Point -> F64
	signed_area = |a, b, c| {
		magnitude = S2Point.triangle_area(a, b, c)
		if c.cross(a).dot(b) > 0.0 {
			magnitude
		} else {
			-magnitude
		}
	}

	## The centroid of the spherical triangle `abc`, scaled by the triangle's
	## area so that the centroids of a subdivision can simply be summed.
	##
	## Rows two and three of the system have the first row subtracted from
	## them before Cramer's rule is applied, which is what keeps the result
	## meaningful for triangles whose vertices nearly coincide.
	true_centroid : S2Point, S2Point, S2Point -> S2Point
	true_centroid = |a, b, c| {
		angle_a = b.angle_to(c).radians()
		angle_b = c.angle_to(a).radians()
		angle_c = a.angle_to(b).radians()
		ra = if angle_a == 0.0 {
			1.0
		} else {
			angle_a / angle_a.sin()
		}
		rb = if angle_b == 0.0 {
			1.0
		} else {
			angle_b / angle_b.sin()
		}
		rc = if angle_c == 0.0 {
			1.0
		} else {
			angle_c / angle_c.sin()
		}

		xs = S2Point.new(a.x, b.x - a.x, c.x - a.x)
		ys = S2Point.new(a.y, b.y - a.y, c.y - a.y)
		zs = S2Point.new(a.z, b.z - a.z, c.z - a.z)
		r = S2Point.new(ra, rb - ra, rc - ra)
		S2Point.new(ys.cross(zs).dot(r), zs.cross(xs).dot(r), xs.cross(ys).dot(r)) * 0.5
	}

	to_inspect : S2Point -> Str
	to_inspect = |p| "S2Point(${p.x.to_str()}, ${p.y.to_str()}, ${p.z.to_str()})"
}

## The angle between two unit-length points by Kahan's formula,
## `2 * atan2(|a - b|, |a + b|)`.
##
## Unlike the cross product, the difference of two nearby points has no
## cancellation error, so this stays accurate when the points are nearly equal
## or nearly opposite.
stable_angle : S2Point, S2Point -> F64
stable_angle = |a, b| 2.0 * S2Math.atan2((a - b).norm(), (a + b).norm())

expect S2Point.new(1.0, 2.0, 3.0).coord(2) == 3.0
expect S2Point.new(1.0, 2.0, 3.0).with_coord(1, 9.0) == S2Point.new(1.0, 9.0, 3.0)
expect S2Point.new(1.0, 2.0, 3.0) + S2Point.new(1.0, 1.0, 1.0) == S2Point.new(2.0, 3.0, 4.0)
expect S2Point.new(1.0, 2.0, 3.0) - S2Point.new(1.0, 1.0, 1.0) == S2Point.new(0.0, 1.0, 2.0)
expect S2Point.new(1.0, 2.0, 3.0) * 2.0 == S2Point.new(2.0, 4.0, 6.0)
expect -S2Point.new(1.0, -2.0, 3.0) == S2Point.new(-1.0, 2.0, -3.0)
expect S2Point.new(1.0, -2.0, 3.0).abs() == S2Point.new(1.0, 2.0, 3.0)
expect S2Point.new(1.0, 0.0, 0.0).dot(S2Point.new(0.0, 1.0, 0.0)) == 0.0
expect S2Point.new(1.0, 0.0, 0.0).cross(S2Point.new(0.0, 1.0, 0.0)) == S2Point.new(0.0, 0.0, 1.0)
expect S2Point.new(0.0, 3.0, 4.0).norm() == 5.0
expect S2Point.new(0.0, 3.0, 4.0).normalize().is_unit_length()
expect S2Point.new(1.0, 0.0, 0.0).is_unit_length()
expect !S2Point.new(1.0, 1.0, 0.0).is_unit_length()
expect S2Point.new(1.0, 2.0, 3.0).largest_abs_component() == 2
expect S2Point.new(-5.0, 2.0, 3.0).largest_abs_component() == 0
expect S2Point.new(1.0, 5.0, 3.0).largest_abs_component() == 1
expect S2Point.origin().is_unit_length()
expect S2Point.new(1.0, 0.0, 0.0).angle_to(S2Point.new(0.0, 1.0, 0.0)).degrees() == 90.0
expect S2Point.new(1.0, 0.0, 0.0).angle_to(S2Point.new(-1.0, 0.0, 0.0)).radians() == F64.pi
expect S2Point.new(1.0, 0.0, 0.0).ortho().is_unit_length()
expect S2Point.new(1.0, 0.0, 0.0).ortho().dot(S2Point.new(1.0, 0.0, 0.0)).abs() < 1e-15
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(1.0, 1e-16, 0.0).normalize()
	cross = a.robust_cross(b).normalize()
	cross.dot(a).abs() < 1e-15 and cross.dot(b).abs() < 1e-15
}
expect S2Point.new(1.0, 0.0, 0.0).robust_cross(S2Point.new(1.0, 0.0, 0.0)) != S2Point.zero()
expect S2Point.new(1.0, 0.0, 0.0).robust_cross(S2Point.new(-1.0, 0.0, 0.0)) != S2Point.zero()
expect {
	rotated = S2Point.new(1.0, 0.0, 0.0)
		.rotate(S2Point.new(0.0, 0.0, 1.0), S1Angle.from_degrees(90.0))
	rotated.approx_eq(S2Point.new(0.0, 1.0, 0.0), 1e-15)
}
expect {
	z_axis = S2Point.new(0.2, 0.5, 0.8).normalize()
	f = z_axis.frame()
	p = S2Point.new(0.3, -0.7, 0.1).normalize()
	S2Point.from_frame(f, S2Point.to_frame(f, p)).approx_eq(p, 1e-15)
}
expect S2Point.new(1.0, 2.0, 3.0) < S2Point.new(1.0, 2.0, 4.0)
expect S2Point.new(1.0, 3.0, 0.0) > S2Point.new(1.0, 2.0, 9.0)

expect {
	# An octant of the sphere has area pi/2.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	(S2Point.triangle_area(a, b, c) - 0.5 * F64.pi).abs() < 1e-14
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	(S2Point.girard_area(a, b, c) - 0.5 * F64.pi).abs() < 1e-14
}
expect {
	# A degenerate triangle has no area.
	a = S2Point.new(1.0, 0.0, 0.0)
	S2Point.triangle_area(a, a, S2Point.new(0.0, 1.0, 0.0)) == 0.0
}
expect {
	# Reversing the winding negates the signed area.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	S2Point.signed_area(a, b, c) == -S2Point.signed_area(a, c, b)
}
expect {
	# A tiny triangle's area matches the flat-plane formula.
	scale = 1e-9
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(1.0, scale, 0.0).normalize()
	c = S2Point.new(1.0, 0.0, scale).normalize()
	expected = 0.5 * scale * scale
	(S2Point.triangle_area(a, b, c) - expected).abs() < 1e-22
}
expect {
	# The centroid of an octant points at its middle.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	centroid = S2Point.true_centroid(a, b, c)
	centroid.normalize().approx_eq(S2Point.new(1.0, 1.0, 1.0).normalize(), 1e-14)
}
expect {
	# Nearly equal points in general position, where the cross product has
	# cancellation error. The reference is upstream's formula (stable side
	# lengths, then l'Huilier's theorem) evaluated in 60-digit arithmetic on
	# exactly these doubles.
	a = S2Point.new(0.2672612419124244, 0.5345224838248488, 0.8017837257372732)
	b = S2Point.new(0.26726150917360897, 0.5345219493022504, 0.8017839929983432)
	c = S2Point.new(0.2672608410207381, 0.5345224838248012, 0.8017838593677558)
	expected = 1.3363055413749088e-13
	(S2Point.triangle_area(a, b, c) - expected).abs() < 1e-12 * expected
}

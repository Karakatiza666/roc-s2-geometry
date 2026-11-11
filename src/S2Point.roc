import S1Angle
import Internal/S2Math
import Internal/S2Coder

## A point in three-dimensional Euclidean space.
##
## Points that lie on the unit sphere are the ones S2 treats as geographic
## positions; the type itself does not enforce unit length, so intermediate
## results such as cross products can be held in it unnormalized.
S2Point := { x : F64, y : F64, z : F64 }.{

	## The point with the given coordinates. The length is not checked.
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

	## The x coordinate.
	x : S2Point -> F64
	x = |p| p.x

	## The y coordinate.
	y : S2Point -> F64
	y = |p| p.y

	## The z coordinate.
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

	## Adds the coordinates. Written `a + b`.
	plus : S2Point, S2Point -> S2Point
	plus = |a, b| { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

	## Subtracts the coordinates of `b` from those of `a`. Written `a - b`.
	minus : S2Point, S2Point -> S2Point
	minus = |a, b| { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }

	## Scales the vector. Written `p * 2.0`.
	times : S2Point, F64 -> S2Point
	times = |p, k| { x: p.x * k, y: p.y * k, z: p.z * k }

	## Divides every coordinate by `k`. Written `p / k`.
	div_by : S2Point, F64 -> S2Point
	div_by = |p, k| { x: p.x / k, y: p.y / k, z: p.z / k }

	## The point with every coordinate negated, which is the antipode of a unit
	## vector. Written `-p`.
	negate : S2Point -> S2Point
	negate = |p| { x: -p.x, y: -p.y, z: -p.z }

	## The componentwise absolute value.
	abs : S2Point -> S2Point
	abs = |p| { x: p.x.abs(), y: p.y.abs(), z: p.z.abs() }

	## Multiplies the coordinates of the two points one by one, so the result
	## is `(a.x * b.x, a.y * b.y, a.z * b.z)`.
	mul_components : S2Point, S2Point -> S2Point
	mul_components = |a, b| { x: a.x * b.x, y: a.y * b.y, z: a.z * b.z }

	## Divides the coordinates of `a` by those of `b` one by one. A zero
	## coordinate in `b` gives an infinite or NaN coordinate in the result.
	div_components : S2Point, S2Point -> S2Point
	div_components = |a, b| { x: a.x / b.x, y: a.y / b.y, z: a.z / b.z }

	## The smaller coordinate of each pair. When a coordinate is NaN, the
	## result follows `if b < a b else a`, as upstream's `std::min` does.
	min : S2Point, S2Point -> S2Point
	min = |a, b| { x: min_f64(a.x, b.x), y: min_f64(a.y, b.y), z: min_f64(a.z, b.z) }

	## The larger coordinate of each pair. When a coordinate is NaN, the
	## result follows `if a < b b else a`, as upstream's `std::max` does.
	max : S2Point, S2Point -> S2Point
	max = |a, b| { x: max_f64(a.x, b.x), y: max_f64(a.y, b.y), z: max_f64(a.z, b.z) }

	## The square root of each coordinate. A negative coordinate gives NaN.
	sqrt : S2Point -> S2Point
	sqrt = |p| { x: S2Math.sqrt(p.x), y: S2Math.sqrt(p.y), z: S2Math.sqrt(p.z) }

	## Each coordinate rounded down to a whole number.
	floor : S2Point -> S2Point
	floor = |p| { x: S2Math.floor(p.x), y: S2Math.floor(p.y), z: S2Math.floor(p.z) }

	## Each coordinate rounded up to a whole number.
	ceil : S2Point -> S2Point
	ceil = |p| { x: S2Math.ceil(p.x), y: S2Math.ceil(p.y), z: S2Math.ceil(p.z) }

	## The dot product of the two points, taken as vectors.
	dot : S2Point, S2Point -> F64
	dot = |a, b| a.x * b.x + a.y * b.y + a.z * b.z

	## The cross product of the two points, taken as vectors. It is the zero
	## vector when they are parallel.
	cross : S2Point, S2Point -> S2Point
	cross = |a, b| {
		x: a.y * b.z - a.z * b.y,
		y: a.z * b.x - a.x * b.z,
		z: a.x * b.y - a.y * b.x,
	}

	## The squared length of the point, taken as a vector.
	norm2 : S2Point -> F64
	norm2 = |p| p.x * p.x + p.y * p.y + p.z * p.z

	## The length of the point, taken as a vector.
	norm : S2Point -> F64
	norm = |p| p.norm2().sqrt()

	## The unit vector in the same direction. The zero vector maps to itself.
	##
	## Like upstream, it multiplies by the reciprocal of the length rather than
	## dividing, so the result can differ in the last digit from a division.
	normalize : S2Point -> S2Point
	normalize = |p| {
		n = p.norm()
		k = if (n == 0.0) 0.0 else 1.0 / n
		{ x: p.x * k, y: p.y * k, z: p.z * k }
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

	## A unit vector that differs from the point, used as the reference
	## direction when a polygon with semi-open boundaries decides whether it
	## contains the vertex `a`.
	##
	## Upstream defines it as `ortho`, so the result is orthogonal to `a`.
	ref_dir : S2Point -> S2Point
	ref_dir = |a| a.ortho()

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

	## The angle at `b` of the path `a`, `b`, `c`, in radians in `[0, pi]`.
	##
	## It is the angle between the great circles `ab` and `cb`, taken at `b`.
	## It uses `robust_cross` for the two circles, so it stays accurate when
	## two of the points are very close together. The points must be unit
	## length.
	angle : S2Point, S2Point, S2Point -> F64
	angle = |a, b, c| a.robust_cross(b).angle_to(c.robust_cross(b)).radians()

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

	## The centroid of the planar triangle `abc`, which is the mean of the
	## three points.
	##
	## Normalize it to get the surface centroid of the spherical triangle,
	## the point where the three medians meet. For a large triangle that
	## point may be far from the intuitive centre.
	planar_centroid : S2Point, S2Point, S2Point -> S2Point
	planar_centroid = |a, b, c| (a + b + c) * (1.0 / 3.0)

	## The true centroid of the geodesic edge `ab`, scaled by the length of
	## the edge, so that the centroids of several edges can simply be summed.
	##
	## Upstream names this `TrueCentroid` too, with two arguments. The name
	## here differs because Roc has no overloads. The result is the zero vector
	## when `a` and `b` are opposite or equal, which is the intended
	## behaviour. The points must be unit length.
	edge_true_centroid : S2Point, S2Point -> S2Point
	edge_true_centroid = |a, b| {
		vdiff = a - b
		vsum = a + b
		sin2 = vdiff.norm2()
		cos2 = vsum.norm2()
		if cos2 == 0.0 {
			S2Point.zero()
		} else {
			vsum * (sin2 / cos2).sqrt()
		}
	}

	to_inspect : S2Point -> Str
	to_inspect = |p| "S2Point(${p.x.to_str()}, ${p.y.to_str()}, ${p.z.to_str()})"

	## The 24 bytes that upstream's `S2Point::Encode` writes: the three
	## coordinates, each as a little-endian IEEE 754 double. There is no
	## version byte.
	##
	## A NaN coordinate is written as the quiet NaN, so its payload is lost.
	## Every other value keeps its bits.
	encode : S2Point -> List(U8)
	encode = |p| [] |> S2Coder.put_f64(p.x) |> S2Coder.put_f64(p.y) |> S2Coder.put_f64(p.z)

	## The point that `encode` writes. Bytes after the first 24 are ignored.
	## The point is not checked for unit length, as upstream does not check it.
	decode : List(U8) -> Try(S2Point, [Truncated])
	decode = |bytes| {
		px = S2Coder.get_f64(bytes, 0)?
		py = S2Coder.get_f64(bytes, 8)?
		pz = S2Coder.get_f64(bytes, 16)?
		Ok(S2Point.new(px, py, pz))
	}
}

min_f64 : F64, F64 -> F64
min_f64 = |a, b| if (b < a) b else a

max_f64 : F64, F64 -> F64
max_f64 = |a, b| if (a < b) b else a

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

# The values below were printed by upstream's Vector3_d, S2::Angle, S2::RefDir
# and S2::PlanarCentroid at v0.14.0 through tools/s2_oracle.cc.
expect S2Point.new(1.0, 2.0, 3.0).mul_components(S2Point.new(4.0, 5.0, 6.0)) == S2Point.new(4.0, 10.0, 18.0)
expect S2Point.new(1.5, -2.0, 0.0).mul_components(S2Point.new(-4.0, 5.0, 6.0)) == S2Point.new(-6.0, -10.0, 0.0)
expect S2Point.new(1.0, 2.0, 3.0).div_components(S2Point.new(4.0, 5.0, 8.0))
	== S2Point.new(0.25, 0.40000000000000002, 0.375)
expect {
	# A zero divisor gives an infinity, and zero over zero gives NaN.
	q = S2Point.new(1.0, -1.0, 0.0).div_components(S2Point.zero())
	q.x() == F64.infinity and q.y() == -F64.infinity and q.z().is_nan()
}
expect S2Point.new(1.0, 2.0, 3.0).div_components(S2Point.new(4.0, -0.0, 6.0)).y() == -F64.infinity
expect S2Point.new(1.0, 5.0, -3.0).min(S2Point.new(4.0, 2.0, -6.0)) == S2Point.new(1.0, 2.0, -6.0)
expect S2Point.new(1.0, 5.0, -3.0).max(S2Point.new(4.0, 2.0, -6.0)) == S2Point.new(4.0, 5.0, -3.0)
expect {
	# With a NaN, upstream's min keeps the first argument and its max too.
	lo = S2Point.new(0.0, -0.0, F64.nan).min(S2Point.new(1.0, 1.0, 1.0))
	hi = S2Point.new(F64.nan, 0.0, 1.0).max(S2Point.new(0.0, F64.nan, 2.0))
	lo.z().is_nan() and hi.x().is_nan() and hi.y() == 0.0 and hi.z() == 2.0
		and lo.y().to_bits() == (-0.0).to_bits()
}
expect S2Point.new(4.0, 2.0, 0.25).sqrt() == S2Point.new(2.0, 1.4142135623730951, 0.5)
expect S2Point.new(4.0, 2.0, -1.0).sqrt().z().is_nan()
expect S2Point.new(1.5, -1.5, 2.0).floor() == S2Point.new(1.0, -2.0, 2.0)
expect S2Point.new(1.5, -1.5, 2.0).ceil() == S2Point.new(2.0, -1.0, 2.0)
expect S2Point.new(0.0, 9.0, 0.0).sqrt() == S2Point.new(0.0, 3.0, 0.0)

expect S2Point.new(1.0, 0.0, 0.0).ref_dir() == S2Point.new(0.0, -0.99998595529588608, 0.0052999255630681958)
expect S2Point.new(0.0, 1.0, 0.0).ref_dir() == S2Point.new(0.004569952278750988, 0.0, -0.99998955771356413)
expect S2Point.new(0.0, 0.0, 1.0).ref_dir() == S2Point.new(-0.99992800777506696, 0.011999136093300803, 0.0)
expect S2Point.new(-1.0, 0.0, 0.0).ref_dir() == S2Point.new(0.0, 0.99998595529588608, -0.0052999255630681958)
expect {
	a = S2Point.new(0.2672612419124244, 0.5345224838248488, 0.8017837257372732)
	d = a.ref_dir()
	d.is_unit_length() and d != a and d.dot(a).abs() < 1e-15
}
expect S2Point.new(0.0, 0.0, 0.0).ref_dir() == S2Point.zero()

# S2::Angle is the angle at the middle point, from the cross products of the
# two edges.
expect S2Point.angle(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0))
	== 1.5707963267948966
expect S2Point.angle(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.0, 1.0, 0.0))
	== 1.5707963267948966
expect {
	a = S2Point.new(0.2672612419124244, 0.5345224838248488, 0.8017837257372732)
	b = S2Point.new(0.26726150917360897, 0.5345219493022504, 0.8017839929983432)
	c = S2Point.new(0.2672608410207381, 0.5345224838248012, 0.8017838593677558)
	(S2Point.angle(a, b, c) - 0.49088250009853068).abs() < 1e-14
}

expect S2Point.planar_centroid(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0))
	== S2Point.new(0.33333333333333331, 0.33333333333333331, 0.33333333333333331)
expect S2Point.planar_centroid(
	S2Point.new(0.2672612419124244, 0.5345224838248488, 0.8017837257372732),
	S2Point.new(0.26726150917360897, 0.5345219493022504, 0.8017839929983432),
	S2Point.new(0.2672608410207381, 0.5345224838248012, 0.8017838593677558),
)
	== S2Point.new(0.26726119736892379, 0.53452230565063341, 0.80178385936779062)

# The edge form of upstream's TrueCentroid.
expect S2Point.edge_true_centroid(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0))
	== S2Point.new(1.0, 1.0, 0.0)
expect S2Point.edge_true_centroid(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0)) == S2Point.zero()
expect S2Point.edge_true_centroid(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == S2Point.zero()
expect S2Point.edge_true_centroid(S2Point.new(0.6, 0.8, 0.0), S2Point.new(0.0, 0.6, 0.8))
	== S2Point.new(0.35564938701829146, 0.82984856970934673, 0.47419918269105532)

# S2Point encoding against upstream's `Encode`, and decoding it back.
expect S2Coder.to_hex(S2Point.new(1.0, 0.0, 0.0).encode()) == "000000000000f03f00000000000000000000000000000000"
expect S2Point.decode(S2Coder.from_hex("000000000000f03f00000000000000000000000000000000")) == Ok(S2Point.new(1.0, 0.0, 0.0))
expect S2Coder.to_hex(S2Point.new(0.6, 0.8, 0.0).encode()) == "333333333333e33f9a9999999999e93f0000000000000000"
expect S2Point.decode(S2Coder.from_hex("333333333333e33f9a9999999999e93f0000000000000000")) == Ok(S2Point.new(0.6, 0.8, 0.0))
expect S2Coder.to_hex(S2Point.new(-0.0, 0.0, 1.0).encode()) == "00000000000000800000000000000000000000000000f03f"
expect S2Point.decode(S2Coder.from_hex("00000000000000800000000000000000000000000000f03f")) == Ok(S2Point.new(-0.0, 0.0, 1.0))
expect S2Coder.to_hex(S2Point.new(-1.5, 2.5e-300, 4.9406564584124654e-324).encode()) == "000000000000f8bf2f30b7b3a7c9ba010100000000000000"
expect S2Point.decode(S2Coder.from_hex("000000000000f8bf2f30b7b3a7c9ba010100000000000000")) == Ok(S2Point.new(-1.5, 2.5e-300, 4.9406564584124654e-324))

# Short input is refused, and bytes after the point are ignored.
expect S2Point.decode(S2Coder.from_hex("000000000000f03f000000000000000000000000000000")) == Err(Truncated)
expect S2Point.decode([]) == Err(Truncated)
expect S2Point.decode(S2Coder.from_hex("000000000000f03f00000000000000000000000000000000ff")) == Ok(S2Point.new(1.0, 0.0, 0.0))
# A point is not checked for unit length.
expect S2Point.decode(S2Coder.from_hex("000000000000004000000000000008400000000000001040")) == Ok(S2Point.new(2.0, 3.0, 4.0))
# A NaN is written as the quiet NaN, as the C library writes the NaN of `strtod`.
expect S2Coder.to_hex(S2Point.new(F64.nan, 0.0, 0.0).encode()) == "000000000000f87f00000000000000000000000000000000"
expect S2Coder.to_hex(S2Point.new(F64.infinity, -F64.infinity, 0.0).encode()) == "000000000000f07f000000000000f0ff0000000000000000"

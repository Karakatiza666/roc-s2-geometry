import S1Angle
import S2Point

## An angle between two points, stored as the squared straight-line distance
## between them on the unit sphere.
##
## Comparing and adding chord angles needs no trigonometry, so distance
## queries that only order or bound results run far faster than they would on
## `S1Angle`. The representable range is `[0, pi]`, plus two sentinels:
## `negative` sorts below every angle and `infinity` sorts above every angle.
##
## Resolution degrades near `pi`, where the squared chord length changes
## slowly with the angle: near 180 degrees the smallest representable step is
## about 1e-8 radians rather than 1e-16.
S1ChordAngle := { length2 : F64 }.{

	## The chord angle whose squared chord length is `length2`, which is
	## capped at 4 (180 degrees). A negative value stays as it is.
	from_length2 : F64 -> S1ChordAngle
	from_length2 = |length2| { length2: length2.min(4.0) }

	## The chord angle equal to `angle`, clamped to `[0, pi]`.
	##
	## A negative angle becomes `negative` and an infinite angle becomes
	## `infinity`.
	from_angle : S1Angle -> S1ChordAngle
	from_angle = |angle| {
		if angle.radians() < 0.0 {
			S1ChordAngle.negative()
		} else if !angle.is_finite() {
			S1ChordAngle.infinity()
		} else {
			length = 2.0 * (0.5 * angle.radians().min(F64.pi)).sin()
			{ length2: length * length }
		}
	}

	## The chord angle for `radians`, clamped as `from_angle` clamps it.
	from_radians : F64 -> S1ChordAngle
	from_radians = |radians| S1ChordAngle.from_angle(S1Angle.from_radians(radians))

	## The chord angle for `degrees`, clamped as `from_angle` clamps it.
	from_degrees : F64 -> S1ChordAngle
	from_degrees = |degrees| S1ChordAngle.from_angle(S1Angle.from_degrees(degrees))

	## The chord angle for degrees scaled by 1e5. A negative value gives
	## `negative`, as in `from_angle`.
	from_e5 : I64 -> S1ChordAngle
	from_e5 = |v| S1ChordAngle.from_angle(S1Angle.from_e5(v))

	## The chord angle for degrees scaled by 1e6. A negative value gives
	## `negative`, as in `from_angle`.
	from_e6 : I64 -> S1ChordAngle
	from_e6 = |v| S1ChordAngle.from_angle(S1Angle.from_e6(v))

	## The chord angle for degrees scaled by 1e7. A negative value gives
	## `negative`, as in `from_angle`.
	from_e7 : I64 -> S1ChordAngle
	from_e7 = |v| S1ChordAngle.from_angle(S1Angle.from_e7(v))

	## A chord angle that is never smaller than `angle`, for angles of at most
	## pi.
	##
	## It squares the angle instead of calling `sin`, so it is very fast. The
	## bound is within 1% for distances up to about 3100 km on the Earth. An
	## angle of 2 radians or more gives `straight`.
	fast_upper_bound_from : S1Angle -> S1ChordAngle
	fast_upper_bound_from = |angle|
		S1ChordAngle.from_length2(angle.radians() * angle.radians())

	## The angle subtended by two points on the unit sphere.
	##
	## This is the cheapest way to build one: it is a subtraction and a dot
	## product, with no trigonometry at all.
	from_points : S2Point, S2Point -> S1ChordAngle
	from_points = |a, b| { length2: (a - b).norm2().min(4.0) }

	## The zero angle.
	zero : () -> S1ChordAngle
	zero = || { length2: 0.0 }

	## 90 degrees.
	right : () -> S1ChordAngle
	right = || { length2: 2.0 }

	## 180 degrees, the largest real chord angle.
	straight : () -> S1ChordAngle
	straight = || { length2: 4.0 }

	## A sentinel below every real angle, used for "no result yet".
	negative : () -> S1ChordAngle
	negative = || { length2: -1.0 }

	## A sentinel above every real angle, used for "no limit".
	infinity : () -> S1ChordAngle
	infinity = || { length2: F64.infinity }

	## The squared chord length.
	length2 : S1ChordAngle -> F64
	length2 = |c| c.length2

	## The equivalent `S1Angle`. `negative` maps to -1 radian and `infinity`
	## maps to an infinite angle.
	to_angle : S1ChordAngle -> S1Angle
	to_angle = |c| {
		if c.is_negative() {
			S1Angle.from_radians(-1.0)
		} else if c.is_infinity() {
			S1Angle.infinity()
		} else {
			S1Angle.from_radians(2.0 * (0.5 * c.length2.sqrt()).asin())
		}
	}

	## The angle in degrees scaled by 1e5, rounded half away from zero.
	e5 : S1ChordAngle -> I64
	e5 = |c| c.to_angle().e5()

	## The angle in degrees scaled by 1e6, rounded half away from zero.
	e6 : S1ChordAngle -> I64
	e6 = |c| c.to_angle().e6()

	## The angle in degrees scaled by 1e7, rounded half away from zero.
	e7 : S1ChordAngle -> I64
	e7 = |c| c.to_angle().e7()

	## The angle in radians.
	radians : S1ChordAngle -> F64
	radians = |c| c.to_angle().radians()

	## The angle in degrees.
	degrees : S1ChordAngle -> F64
	degrees = |c| c.to_angle().degrees()

	## True when the squared chord length is exactly zero.
	is_zero : S1ChordAngle -> Bool
	is_zero = |c| c.length2 == 0.0

	## True for the negative sentinel and for any other negative squared
	## length.
	is_negative : S1ChordAngle -> Bool
	is_negative = |c| c.length2 < 0.0

	## True for the infinity sentinel.
	is_infinity : S1ChordAngle -> Bool
	is_infinity = |c| c.length2 == F64.infinity

	## True for the `negative` and `infinity` sentinels.
	is_special : S1ChordAngle -> Bool
	is_special = |c| c.is_negative() or c.is_infinity()

	## True when the angle is in `[0, pi]` or is one of the two sentinels.
	is_valid : S1ChordAngle -> Bool
	is_valid = |c| (c.length2 >= 0.0 and c.length2 <= 4.0) or c.is_special()

	## `sin(angle)^2`, without computing the angle.
	sin2 : S1ChordAngle -> F64
	sin2 = |c| c.length2 * (1.0 - 0.25 * c.length2)

	## The sine of the angle.
	sin : S1ChordAngle -> F64
	sin = |c| c.sin2().sqrt()

	## The cosine of the angle.
	cos : S1ChordAngle -> F64
	cos = |c| 1.0 - 0.5 * c.length2

	## The tangent of the angle. It is infinite at 90 degrees.
	tan : S1ChordAngle -> F64
	tan = |c| c.sin() / c.cos()

	## The sum of two angles, clamped to 180 degrees.
	##
	## One square root and a few multiplications, rather than a round trip
	## through `S1Angle`.
	plus : S1ChordAngle, S1ChordAngle -> S1ChordAngle
	plus = |a, b| {
		if b.length2 == 0.0 {
			return a
		}
		if a.length2 + b.length2 >= 4.0 {
			return S1ChordAngle.straight()
		}
		x = a.length2 * (1.0 - 0.25 * b.length2)
		y = b.length2 * (1.0 - 0.25 * a.length2)
		{ length2: (x + y + 2.0 * (x * y).sqrt()).min(4.0) }
	}

	## The most relative error in the `length2` of a sum from `plus`, about
	## 2.02 times `F64` machine epsilon.
	##
	## A caller that must contain the true sum adds this much of `length2`
	## with `plus_error`.
	relative_sum_error : F64
	relative_sum_error = 2.02 * 2.220446049250313e-16

	## The difference of two angles, clamped to zero.
	minus : S1ChordAngle, S1ChordAngle -> S1ChordAngle
	minus = |a, b| {
		if b.length2 == 0.0 {
			return a
		}
		if a.length2 <= b.length2 {
			return S1ChordAngle.zero()
		}
		x = a.length2 * (1.0 - 0.25 * b.length2)
		y = b.length2 * (1.0 - 0.25 * a.length2)
		c = (x.sqrt() - y.sqrt()).max(0.0)
		{ length2: c * c }
	}

	## The angle shifted by `error` in squared-chord units, clamped to the
	## valid range. The sentinels are returned unchanged.
	plus_error : S1ChordAngle, F64 -> S1ChordAngle
	plus_error = |c, error| {
		if c.is_special() {
			c
		} else {
			{ length2: (c.length2 + error).max(0.0).min(4.0) }
		}
	}

	## The error bound for a chord angle built by `from_points` from
	## normalized points.
	point_constructor_max_error : S1ChordAngle -> F64
	point_constructor_max_error = |c| 4.5 * 2.220446049250313e-16 * c.length2
		+ 16.0 * 2.220446049250313e-16 * 2.220446049250313e-16

	## The error bound for a chord angle built by `from_angle`, in squared-chord
	## units.
	angle_constructor_max_error : S1ChordAngle -> F64
	angle_constructor_max_error = |c| 1.5 * 2.220446049250313e-16 * c.length2

	## The smallest chord angle greater than this one, which turns a `<`
	## comparison into a `<=` comparison.
	successor : S1ChordAngle -> S1ChordAngle
	successor = |c| {
		if c.length2 >= 4.0 {
			S1ChordAngle.infinity()
		} else if c.length2 < 0.0 {
			S1ChordAngle.zero()
		} else {
			{ length2: F64.from_bits(c.length2.to_bits() + 1) }
		}
	}

	## The largest chord angle less than this one.
	predecessor : S1ChordAngle -> S1ChordAngle
	predecessor = |c| {
		if c.length2 <= 0.0 {
			S1ChordAngle.negative()
		} else if c.length2 > 4.0 {
			S1ChordAngle.straight()
		} else {
			{ length2: F64.from_bits(c.length2.to_bits() - 1) }
		}
	}

	is_eq : S1ChordAngle, S1ChordAngle -> Bool
	is_eq = |a, b| a.length2 == b.length2

	is_lt : S1ChordAngle, S1ChordAngle -> Bool
	is_lt = |a, b| a.length2 < b.length2

	is_lte : S1ChordAngle, S1ChordAngle -> Bool
	is_lte = |a, b| a.length2 <= b.length2

	is_gt : S1ChordAngle, S1ChordAngle -> Bool
	is_gt = |a, b| a.length2 > b.length2

	is_gte : S1ChordAngle, S1ChordAngle -> Bool
	is_gte = |a, b| a.length2 >= b.length2

	## The smaller of the two angles.
	min : S1ChordAngle, S1ChordAngle -> S1ChordAngle
	min = |a, b| if (a.length2 <= b.length2) a else b

	## The larger of the two angles.
	max : S1ChordAngle, S1ChordAngle -> S1ChordAngle
	max = |a, b| if (a.length2 >= b.length2) a else b

	to_inspect : S1ChordAngle -> Str
	to_inspect = |c| "S1ChordAngle(${c.degrees().to_str()} deg)"
}

expect S1ChordAngle.zero().length2() == 0.0
expect (S1ChordAngle.right().degrees() - 90.0).abs() < 1e-13
expect S1ChordAngle.straight().degrees() == 180.0
expect S1ChordAngle.negative().is_negative()
expect S1ChordAngle.infinity().is_infinity()
expect S1ChordAngle.negative().is_special()
expect !S1ChordAngle.right().is_special()
expect S1ChordAngle.right().is_valid()
expect S1ChordAngle.infinity().is_valid()
expect (S1ChordAngle.from_angle(S1Angle.from_degrees(90.0)).length2() - 2.0).abs() < 1e-15
expect S1ChordAngle.from_angle(S1Angle.from_degrees(180.0)) == S1ChordAngle.straight()
expect S1ChordAngle.from_angle(S1Angle.from_degrees(270.0)) == S1ChordAngle.straight()
expect S1ChordAngle.from_angle(S1Angle.from_degrees(-1.0)).is_negative()
expect S1ChordAngle.from_angle(S1Angle.infinity()).is_infinity()
expect S1ChordAngle.negative().to_angle().radians() == -1.0
expect S1ChordAngle.infinity().to_angle().is_finite() == Bool.False
expect S1ChordAngle.from_points(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0))
	== S1ChordAngle.right()
expect S1ChordAngle.from_points(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0))
	== S1ChordAngle.straight()
expect S1ChordAngle.from_points(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)).is_zero()
expect (S1ChordAngle.right().sin() - 1.0).abs() < 1e-15
expect S1ChordAngle.right().cos().abs() < 1e-15
expect (S1ChordAngle.from_angle(S1Angle.from_degrees(45.0)).sin2() - 0.5).abs() < 1e-15
expect {
	sum = S1ChordAngle.from_angle(S1Angle.from_degrees(30.0))
		+ S1ChordAngle.from_angle(S1Angle.from_degrees(60.0))
	(sum.degrees() - 90.0).abs() < 1e-13
}
expect S1ChordAngle.right() + S1ChordAngle.right() == S1ChordAngle.straight()
expect S1ChordAngle.straight() + S1ChordAngle.right() == S1ChordAngle.straight()
expect {
	diff = S1ChordAngle.from_angle(S1Angle.from_degrees(90.0))
		- S1ChordAngle.from_angle(S1Angle.from_degrees(30.0))
	(diff.degrees() - 60.0).abs() < 1e-13
}
expect S1ChordAngle.right() - S1ChordAngle.straight() == S1ChordAngle.zero()
expect S1ChordAngle.zero().successor() > S1ChordAngle.zero()
expect S1ChordAngle.straight().successor().is_infinity()
expect S1ChordAngle.negative().successor() == S1ChordAngle.zero()
expect S1ChordAngle.zero().predecessor().is_negative()
expect S1ChordAngle.right().predecessor() < S1ChordAngle.right()
expect S1ChordAngle.right().plus_error(-10.0) == S1ChordAngle.zero()
expect S1ChordAngle.right().plus_error(10.0) == S1ChordAngle.straight()
expect S1ChordAngle.infinity().plus_error(-10.0).is_infinity()
expect S1ChordAngle.right() < S1ChordAngle.straight()
expect S1ChordAngle.negative() < S1ChordAngle.zero()
expect S1ChordAngle.straight() < S1ChordAngle.infinity()
expect S1ChordAngle.right().min(S1ChordAngle.straight()) == S1ChordAngle.right()
expect S1ChordAngle.right().max(S1ChordAngle.straight()) == S1ChordAngle.straight()

# The values below were printed by upstream's S1ChordAngle at v0.14.0 through
# tools/s2_oracle.cc.
expect S1ChordAngle.from_radians(1.0).length2() == 0.91939538826372058
expect S1ChordAngle.from_radians(0.0) == S1ChordAngle.zero()
expect S1ChordAngle.from_radians(F64.infinity).is_infinity()
expect S1ChordAngle.from_degrees(45.0).length2() == 0.58578643762690497
expect S1ChordAngle.from_degrees(180.0) == S1ChordAngle.straight()
expect S1ChordAngle.from_degrees(200.0) == S1ChordAngle.straight()
expect S1ChordAngle.from_degrees(-1.0) == S1ChordAngle.negative()
expect S1ChordAngle.from_degrees(90.0).length2() == 1.9999999999999996
expect S1ChordAngle.from_e5(4500000).length2() == 0.58578643762690519
expect S1ChordAngle.from_e6(-12345678) == S1ChordAngle.negative()
expect S1ChordAngle.from_e7(123456789).length2() == 0.046249147866173478
expect S1ChordAngle.from_radians(1.0).e5() == 5729578
expect S1ChordAngle.from_radians(1.0).e6() == 57295780
expect S1ChordAngle.from_radians(1.0).e7() == 572957795
expect S1ChordAngle.from_degrees(180.0).e7() == 1800000000
expect S1ChordAngle.from_degrees(90.0).e6() == 90000000
expect S1ChordAngle.from_e7(123456789).e7() == 123456789
expect S1ChordAngle.zero().e5() == 0
expect S1ChordAngle.fast_upper_bound_from(S1Angle.from_radians(0.5)).length2() == 0.25
expect S1ChordAngle.fast_upper_bound_from(S1Angle.from_radians(1.0)).length2() == 1.0
expect S1ChordAngle.fast_upper_bound_from(S1Angle.from_radians(2.0)) == S1ChordAngle.straight()
expect S1ChordAngle.fast_upper_bound_from(S1Angle.from_radians(100.0)) == S1ChordAngle.straight()
expect S1ChordAngle.fast_upper_bound_from(S1Angle.zero()) == S1ChordAngle.zero()
expect S1ChordAngle.fast_upper_bound_from(S1Angle.from_radians(0.0015696123057604772)).length2()
	== 2.4636827903947219e-06
expect S1ChordAngle.from_radians(1.0).angle_constructor_max_error() == 3.0622017863537042e-16
expect S1ChordAngle.from_degrees(45.0).angle_constructor_max_error() == 1.951060771699614e-16
expect S1ChordAngle.straight().angle_constructor_max_error() == 1.3322676295501878e-15
expect S1ChordAngle.zero().angle_constructor_max_error() == 0.0
expect S1ChordAngle.negative().angle_constructor_max_error() == -3.3306690738754696e-16

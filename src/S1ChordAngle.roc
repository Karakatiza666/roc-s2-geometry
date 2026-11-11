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

	## The chord angle whose squared chord length is `length2`.
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

	## The angle subtended by two points on the unit sphere.
	##
	## This is the cheapest way to build one: it is a subtraction and a dot
	## product, with no trigonometry at all.
	from_points : S2Point, S2Point -> S1ChordAngle
	from_points = |a, b| { length2: (a - b).norm2().min(4.0) }

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

	radians : S1ChordAngle -> F64
	radians = |c| c.to_angle().radians()

	degrees : S1ChordAngle -> F64
	degrees = |c| c.to_angle().degrees()

	is_zero : S1ChordAngle -> Bool
	is_zero = |c| c.length2 == 0.0

	is_negative : S1ChordAngle -> Bool
	is_negative = |c| c.length2 < 0.0

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

	sin : S1ChordAngle -> F64
	sin = |c| c.sin2().sqrt()

	cos : S1ChordAngle -> F64
	cos = |c| 1.0 - 0.5 * c.length2

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

	min : S1ChordAngle, S1ChordAngle -> S1ChordAngle
	min = |a, b| if (a.length2 <= b.length2) a else b

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

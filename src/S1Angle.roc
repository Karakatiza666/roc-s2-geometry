import Internal/S2Math

## A one-dimensional angle, stored as radians in an `F64`.
##
## `S1Angle` is a thin unit-carrying wrapper: it has no notion of being
## normalized, so it can represent angles outside `[-pi, pi]` and can
## accumulate turns. Use `normalized` to fold one back into `(-pi, pi]`.
##
##     S1Angle.from_degrees(90.0).radians() == 0.5 * F64.pi
S1Angle := { radians : F64 }.{

	## An angle of `r` radians.
	from_radians : F64 -> S1Angle
	from_radians = |r| { radians: r }

	## An angle of `d` degrees.
	from_degrees : F64 -> S1Angle
	from_degrees = |d| { radians: d * (F64.pi / 180.0) }

	## An angle from degrees scaled by 1e5, the unit many geodata formats use.
	from_e5 : I64 -> S1Angle
	from_e5 = |v| S1Angle.from_degrees(v.to_f64() * 1e-5)

	## An angle from degrees scaled by 1e6.
	from_e6 : I64 -> S1Angle
	from_e6 = |v| S1Angle.from_degrees(v.to_f64() * 1e-6)

	## An angle from degrees scaled by 1e7.
	from_e7 : I64 -> S1Angle
	from_e7 = |v| S1Angle.from_degrees(v.to_f64() * 1e-7)

	## The zero angle.
	zero : () -> S1Angle
	zero = || { radians: 0.0 }

	## An angle larger than any finite angle, used as a "no distance" sentinel.
	infinity : () -> S1Angle
	infinity = || { radians: F64.infinity }

	## The angle in radians.
	radians : S1Angle -> F64
	radians = |a| a.radians

	## The angle in degrees.
	degrees : S1Angle -> F64
	degrees = |a| a.radians * (180.0 / F64.pi)

	## The angle in degrees scaled by 1e5, rounded half away from zero.
	e5 : S1Angle -> I64
	e5 = |a| S2Math.round(a.degrees() * 1e5).to_i64_wrap()

	## The angle in degrees scaled by 1e6, rounded half away from zero.
	e6 : S1Angle -> I64
	e6 = |a| S2Math.round(a.degrees() * 1e6).to_i64_wrap()

	## The angle in degrees scaled by 1e7, rounded half away from zero.
	e7 : S1Angle -> I64
	e7 = |a| S2Math.round(a.degrees() * 1e7).to_i64_wrap()

	## The angle folded into `(-pi, pi]`.
	normalized : S1Angle -> S1Angle
	normalized = |a| {
		r = S2Math.remainder(a.radians, 2.0 * F64.pi)
		if r <= -F64.pi {
			{ radians: F64.pi }
		} else {
			{ radians: r }
		}
	}

	## The magnitude of the angle.
	abs : S1Angle -> S1Angle
	abs = |a| { radians: a.radians.abs() }

	## True when the angle is neither infinite nor NaN.
	is_finite : S1Angle -> Bool
	is_finite = |a| a.radians.is_finite()

	plus : S1Angle, S1Angle -> S1Angle
	plus = |a, b| { radians: a.radians + b.radians }

	minus : S1Angle, S1Angle -> S1Angle
	minus = |a, b| { radians: a.radians - b.radians }

	## Scales the angle. Written `angle * 2.0`.
	times : S1Angle, F64 -> S1Angle
	times = |a, k| { radians: a.radians * k }

	## Divides the angle. Written `angle / 2.0`.
	div_by : S1Angle, F64 -> S1Angle
	div_by = |a, k| { radians: a.radians / k }

	negate : S1Angle -> S1Angle
	negate = |a| { radians: -a.radians }

	is_eq : S1Angle, S1Angle -> Bool
	is_eq = |a, b| a.radians == b.radians

	is_lt : S1Angle, S1Angle -> Bool
	is_lt = |a, b| a.radians < b.radians

	is_lte : S1Angle, S1Angle -> Bool
	is_lte = |a, b| a.radians <= b.radians

	is_gt : S1Angle, S1Angle -> Bool
	is_gt = |a, b| a.radians > b.radians

	is_gte : S1Angle, S1Angle -> Bool
	is_gte = |a, b| a.radians >= b.radians

	## The smaller of two angles.
	min : S1Angle, S1Angle -> S1Angle
	min = |a, b| if (a.radians <= b.radians) a else b

	## The larger of two angles.
	max : S1Angle, S1Angle -> S1Angle
	max = |a, b| if (a.radians >= b.radians) a else b

	## True when the two angles differ by at most `max_error` radians.
	approx_eq : S1Angle, S1Angle, F64 -> Bool
	approx_eq = |a, b, max_error| (a.radians - b.radians).abs() <= max_error

	to_inspect : S1Angle -> Str
	to_inspect = |a| "S1Angle(${a.degrees().to_str()} deg)"
}

expect S1Angle.from_degrees(90.0).radians() == 0.5 * F64.pi
expect S1Angle.from_radians(F64.pi).degrees() == 180.0
expect S1Angle.zero().radians() == 0.0
expect S1Angle.from_degrees(-45.0).abs() == S1Angle.from_degrees(45.0)
expect S1Angle.from_degrees(1.0).e6() == 1000000
expect S1Angle.from_e7(-450000000).degrees() == -45.0
expect S1Angle.from_degrees(360.0).normalized().radians().abs() < 1e-15
expect S1Angle.from_degrees(-180.0).normalized() == S1Angle.from_degrees(180.0)
expect S1Angle.from_degrees(180.0).normalized() == S1Angle.from_degrees(180.0)
expect S1Angle.from_degrees(270.0).normalized().degrees() == -90.0
expect S1Angle.from_degrees(30.0) + S1Angle.from_degrees(60.0) == S1Angle.from_degrees(90.0)
expect (S1Angle.from_degrees(90.0) - S1Angle.from_degrees(30.0)).approx_eq(S1Angle.from_degrees(60.0), 1e-15)
expect S1Angle.from_degrees(30.0) * 3.0 == S1Angle.from_degrees(90.0)
expect S1Angle.from_degrees(90.0) / 3.0 == S1Angle.from_degrees(30.0)
expect -S1Angle.from_degrees(30.0) == S1Angle.from_degrees(-30.0)
expect S1Angle.from_degrees(30.0) < S1Angle.from_degrees(60.0)
expect S1Angle.from_degrees(60.0) >= S1Angle.from_degrees(60.0)
expect S1Angle.infinity().is_finite() == Bool.False
expect S1Angle.from_degrees(10.0).min(S1Angle.from_degrees(20.0)).degrees() == 10.0
expect S1Angle.from_degrees(10.0).max(S1Angle.from_degrees(20.0)).degrees() == 20.0

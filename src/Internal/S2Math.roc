## Floating-point helpers the S2 algorithms need that the builtins do not
## provide: `floor`, `ceil`, `round`, `atan2`, `remainder`, and the `frexp`/`ldexp`
## exponent manipulation the cell metrics are defined in terms of.
##
## Internal to this package.
S2Math := [].{

	## Largest integral value not greater than `x`, as an `F64`.
	##
	## Exact for every finite `x`. A value of magnitude 2^52 or more is
	## already an integer, so it is returned as it is.
	floor : F64 -> F64
	floor = |x| {
		if !x.is_finite() or x.abs() >= 4503599627370496.0 {
			return x
		}
		truncated = x.to_i64_wrap().to_f64()
		if (truncated > x) truncated - 1.0 else truncated
	}

	## Smallest integral value not less than `x`, as an `F64`.
	##
	## A value of magnitude 2^52 or more is already an integer, so it is
	## returned as it is.
	ceil : F64 -> F64
	ceil = |x| {
		if !x.is_finite() or x.abs() >= 4503599627370496.0 {
			return x
		}
		truncated = x.to_i64_wrap().to_f64()
		if (truncated < x) truncated + 1.0 else truncated
	}

	## Rounds half away from zero, matching C's `round`.
	##
	## The fraction is taken from `floor`, not from `x + 0.5`, because that sum
	## rounds up for 0.49999999999999994 and for values of 2^52 or more.
	round : F64 -> F64
	round = |x| {
		if !x.is_finite() {
			return x
		}
		magnitude = x.abs()
		low = S2Math.floor(magnitude)
		rounded = if (magnitude - low >= 0.5) low + 1.0 else low
		if (x < 0.0) -rounded else rounded
	}

	## Rounds half to even, the tie-break IEEE 754 rounding uses.
	round_half_even : F64 -> F64
	round_half_even = |x| {
		if !x.is_finite() {
			return x
		}
		low = S2Math.floor(x)
		frac = x - low
		if frac > 0.5 {
			low + 1.0
		} else if frac < 0.5 {
			low
		} else if S2Math.floor(low / 2.0) * 2.0 == low {
			low
		} else {
			low + 1.0
		}
	}

	## The IEEE 754 remainder of `x / y`: `x - y * n`, where `n` is `x / y`
	## rounded half to even. Unlike `%` the result may be negative, and its
	## magnitude never exceeds `|y| / 2`.
	##
	## The result is exact for every finite `x` and `y`, as C's `remainder`
	## is. It comes from binary long division: every step subtracts a power
	## of two times `|y|`, and each such subtraction is exact. The cost is
	## proportional to the difference of the binary exponents of `x` and
	## `y`, so it is a few steps for the angles S2 uses and about 1000 steps
	## at most. Gives NaN when `x` is infinite or NaN, when `y` is zero or
	## NaN, and gives `x` when `y` is infinite.
	remainder : F64, F64 -> F64
	remainder = |x, y| {
		if x.is_nan() or y.is_nan() or y == 0.0 or !x.is_finite() {
			return F64.nan
		}
		if !y.is_finite() {
			return x
		}
		ay = y.abs()
		var $r = x.abs()
		var $t = ay
		while $t * 2.0 <= $r {
			$t = $t * 2.0
		}
		# Now `$r < 2 * $t` whenever `$r >= ay`; each subtraction keeps it so.
		var $odd = Bool.False
		var $more = $r >= ay
		while $more {
			if $r >= $t {
				$r = $r - $t
				$odd = Bool.True
			} else {
				$odd = Bool.False
			}
			if $t == ay {
				$more = Bool.False
			} else {
				$t = $t * 0.5
			}
		}
		half = ay * 0.5
		if $r > half or ($r == half and $odd) {
			$r = $r - ay
		}
		result = $r
		if (x < 0.0) -result else result
	}

	## Angle in radians from the positive x-axis to the point `(x, y)`,
	## in `[-pi, pi]`.
	atan2 : F64, F64 -> F64
	atan2 = |y, x| {
		if x.is_nan() or y.is_nan() {
			F64.nan
		} else if x > 0.0 {
			(y / x).atan()
		} else if x < 0.0 {
			if y >= 0.0 {
				(y / x).atan() + F64.pi
			} else {
				(y / x).atan() - F64.pi
			}
		} else if y > 0.0 {
			0.5 * F64.pi
		} else if y < 0.0 {
			-0.5 * F64.pi
		} else {
			0.0
		}
	}

	## `x * 2^n`, computed without rounding error for the exponents S2 uses.
	ldexp : F64, I32 -> F64
	ldexp = |x, n| {
		two : F64
		two = 2.0
		if n >= 0 {
			x * two.pow(n.to_f64())
		} else {
			x / two.pow((-n).to_f64())
		}
	}

	## The exponent `e` for which `x = m * 2^e` with `0.5 <= |m| < 1`,
	## which is what `frexp` returns alongside the mantissa. Zero for `x = 0`.
	frexp_exponent : F64 -> I32
	frexp_exponent = |x| {
		magnitude = x.abs()
		if magnitude == 0.0 or !magnitude.is_finite() {
			return 0
		}
		bits = magnitude.to_bits()
		raw = bits.shr_zf_wrap(52).bitwise_and(0x7ff).to_i32_wrap()
		if raw == 0 {
			# Subnormal: scale into the normal range, then correct.
			two : F64
			two = 2.0
			scaled = (magnitude * two.pow(64.0)).to_bits()
			scaled.shr_zf_wrap(52).bitwise_and(0x7ff).to_i32_wrap() - 1022 - 64
		} else {
			raw - 1022
		}
	}

	## Clamps `x` to `[lo, hi]`.
	clamp : F64, F64, F64 -> F64
	clamp = |x, lo, hi| x.max(lo).min(hi)

	## Clamps a `U64` to `[lo, hi]`.
	clamp_u64 : U64, U64, U64 -> U64
	clamp_u64 = |x, lo, hi| x.max(lo).min(hi)

	## Clamps an `I64` to `[lo, hi]`.
	clamp_i64 : I64, I64, I64 -> I64
	clamp_i64 = |x, lo, hi| x.max(lo).min(hi)
}

expect S2Math.floor(-1.5) == -2.0
expect S2Math.floor(1.5) == 1.0
expect S2Math.floor(2.0) == 2.0
expect S2Math.ceil(-1.5) == -1.0
expect S2Math.ceil(1.5) == 2.0
expect S2Math.round(0.5) == 1.0
expect S2Math.round(-0.5) == -1.0
expect S2Math.round(2.5) == 3.0
expect S2Math.round_half_even(0.5) == 0.0
expect S2Math.round_half_even(1.5) == 2.0
expect S2Math.round_half_even(2.5) == 2.0
expect S2Math.round_half_even(-2.5) == -2.0
expect S2Math.remainder(5.0, 3.0) == -1.0
expect S2Math.remainder(-5.0, 3.0) == 1.0
expect S2Math.remainder(4.5, 3.0) == -1.5
expect S2Math.atan2(0.0, 1.0) == 0.0
expect S2Math.atan2(1.0, 0.0) == 0.5 * F64.pi
expect S2Math.atan2(0.0, -1.0) == F64.pi
expect (S2Math.atan2(1.0, 1.0) - 0.25 * F64.pi).abs() < 1e-15
expect S2Math.ldexp(1.0, -3) == 0.125
expect S2Math.ldexp(3.0, 4) == 48.0
expect S2Math.frexp_exponent(1.0) == 1
expect S2Math.frexp_exponent(0.5) == 0
expect S2Math.frexp_exponent(1024.0) == 11
expect S2Math.frexp_exponent(0.0) == 0
expect S2Math.floor(1e20) == 1e20
expect S2Math.floor(-1e20) == -1e20
expect S2Math.ceil(-1e300) == -1e300
expect S2Math.floor(4503599627370497.0) == 4503599627370497.0
expect S2Math.round(0.49999999999999994) == 0.0
expect S2Math.round(-0.49999999999999994) == 0.0
expect S2Math.round(4503599627370497.0) == 4503599627370497.0
expect S2Math.round(-4503599627370497.0) == -4503599627370497.0
expect S2Math.round(-2.5) == -3.0
expect S2Math.round(1.4999999999999998) == 1.0
expect S2Math.remainder(1e20, 8.0) == 0.0
expect S2Math.remainder(1e20, 3.0) == 1.0
expect S2Math.remainder(-1e20, 3.0) == -1.0
expect S2Math.remainder(1e20, 7.0) == 2.0
expect S2Math.remainder(7.0, 2.0) == -1.0
expect S2Math.remainder(5.0, F64.infinity) == 5.0
expect S2Math.remainder(0.25, 1.0) == 0.25
expect S2Math.remainder(3.0, 2.0) == -1.0
expect S2Math.remainder(F64.infinity, 1.0).is_nan()
expect S2Math.remainder(1.0, 0.0).is_nan()
expect S2Math.atan2(F64.nan, 1.0).is_nan()
expect S2Math.atan2(1.0, F64.nan).is_nan()

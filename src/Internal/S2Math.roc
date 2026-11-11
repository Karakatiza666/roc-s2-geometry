## Floating-point helpers the S2 algorithms need that the builtins do not
## provide: `floor`, `ceil`, `atan2`, `remainder`, and the `frexp`/`ldexp`
## exponent manipulation the cell metrics are defined in terms of.
##
## Internal to this package.
S2Math := [].{

	## Largest integral value not greater than `x`, as an `F64`.
	##
	## Exact for every `x` whose magnitude fits in an `I64`, which covers
	## every value S2 feeds it.
	floor : F64 -> F64
	floor = |x| {
		if !x.is_finite() {
			return x
		}
		truncated = x.to_i64_wrap().to_f64()
		if (truncated > x) truncated - 1.0 else truncated
	}

	## Smallest integral value not less than `x`, as an `F64`.
	ceil : F64 -> F64
	ceil = |x| {
		if !x.is_finite() {
			return x
		}
		truncated = x.to_i64_wrap().to_f64()
		if (truncated < x) truncated + 1.0 else truncated
	}

	## Rounds half away from zero, matching C's `lround`.
	round : F64 -> F64
	round = |x| {
		if !x.is_finite() {
			return x
		}
		if (x < 0.0) -S2Math.floor(-x + 0.5) else S2Math.floor(x + 0.5)
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
	remainder : F64, F64 -> F64
	remainder = |x, y| {
		if y == 0.0 or !x.is_finite() {
			return F64.nan
		}
		x - y * S2Math.round_half_even(x / y)
	}

	## Angle in radians from the positive x-axis to the point `(x, y)`,
	## in `[-pi, pi]`.
	atan2 : F64, F64 -> F64
	atan2 = |y, x| {
		if x > 0.0 {
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

## Floating-point helpers the S2 algorithms need that the builtins do not
## provide: `floor`, `ceil`, `round`, `atan2`, `remainder`, and the `frexp`/`ldexp`
## exponent manipulation the cell metrics are defined in terms of.
##
## Internal to this package.
S2Math := [].{

	## The square root of `x`, or NaN when `x` is negative.
	##
	## The builtin `sqrt` crashes on a negative number, where C gives NaN.
	sqrt : F64 -> F64
	sqrt = |x| if (x < 0.0) F64.nan else x.sqrt()

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

	## `e` to the power `x`.
	##
	## This is the algorithm of fdlibm's `e_exp.c`, whose error is below one
	## unit in the last place. The result can differ from the C library by one
	## unit in the last place.
	exp : F64 -> F64
	exp = |x| {
		if x.is_nan() {
			return x
		}
		if x > 709.782712893384 {
			return F64.infinity
		}
		if x < -745.1332191019411 {
			return 0.0
		}
		negative = x < 0.0
		ax = x.abs()
		high = ax.to_bits().shr_zf_wrap(32)
		if high < 0x3e300000 {
			return 1.0 + x
		}
		# The reduced argument is `hi - lo`, and the result is `2^k` times
		# `e^(hi - lo)`.
		reduction =
			if high > 0x3fd62e42 {
				if high < 0x3ff0a2b2 {
					if (negative) (x + exp_ln2_hi, -exp_ln2_lo, -1) else (x - exp_ln2_hi, exp_ln2_lo, 1)
				} else {
					k = (exp_inv_ln2 * x + (if (negative) -0.5 else 0.5)).to_i64_wrap()
					t = k.to_f64()
					(x - t * exp_ln2_hi, t * exp_ln2_lo, k)
				}
			} else {
				(x, 0.0, 0)
			}
		(hi, lo, k) = reduction
		r = hi - lo
		t = r * r
		c = r - t * (exp_p1 + t * (exp_p2 + t * (exp_p3 + t * (exp_p4 + t * exp_p5))))
		if k == 0 {
			1.0 - ((r * c) / (c - 2.0) - r)
		} else {
			y = 1.0 - ((lo - (r * c) / (2.0 - c)) - hi)
			if k >= -1021 {
				if k > 1000 {
					y * exp_two_pow(1000) * exp_two_pow(k - 1000)
				} else {
					y * exp_two_pow(k)
				}
			} else {
				y * exp_two_pow(k + 1000) * exp_two_pow(-1000)
			}
		}
	}

	## The natural logarithm of `x`: NaN for a negative number and negative
	## infinity for zero.
	##
	## This is the algorithm of fdlibm's `e_log.c`, whose error is below one
	## unit in the last place. The result can differ from the C library by one
	## unit in the last place.
	log : F64 -> F64
	log = |x| {
		if x.is_nan() or x < 0.0 {
			return F64.nan
		}
		if x == 0.0 {
			return -F64.infinity
		}
		if x == F64.infinity {
			return x
		}
		bits = x.to_bits()
		subnormal = bits.shr_zf_wrap(32) < 0x00100000
		scaled = if (subnormal) x * 18014398509481984.0 else x
		scaled_bits = scaled.to_bits()
		high = scaled_bits.shr_zf_wrap(32)
		exponent = high.shr_zf_wrap(20).to_i64_wrap() - 1023 - (if (subnormal) 54 else 0)
		mantissa_high = high.bitwise_and(0x000fffff)
		# Rescale the mantissa into [sqrt(2)/2, sqrt(2)).
		i = (mantissa_high + 0x95f64).bitwise_and(0x100000)
		normalized_high = mantissa_high.bitwise_or(i.bitwise_xor(0x3ff00000))
		v = F64.from_bits(normalized_high.shl_wrap(32).bitwise_or(scaled_bits.bitwise_and(0xffffffff)))
		k = exponent + i.shr_zf_wrap(20).to_i64_wrap()
		dk = k.to_f64()
		f = v - 1.0
		if mantissa_high.plus_wrap(2).bitwise_and(0x000fffff) < 3 {
			# |f| < 2^-20
			if f == 0.0 {
				if k == 0 {
					0.0
				} else {
					dk * log_ln2_hi + dk * log_ln2_lo
				}
			} else {
				rr = f * f * (0.5 - 0.33333333333333333 * f)
				if k == 0 {
					f - rr
				} else {
					dk * log_ln2_hi - ((rr - dk * log_ln2_lo) - f)
				}
			}
		} else {
			s = f / (2.0 + f)
			z = s * s
			w = z * z
			t1 = w * (log_g2 + w * (log_g4 + w * log_g6))
			t2 = z * (log_g1 + w * (log_g3 + w * (log_g5 + w * log_g7)))
			rr = t2 + t1
			near_half = mantissa_high.to_i64_wrap() - 0x6147a
			near_half_other = 0x6b851 - mantissa_high.to_i64_wrap()
			positive = near_half.bitwise_or(near_half_other) > 0
			if positive {
				hfsq = 0.5 * f * f
				if k == 0 {
					f - (hfsq - s * (hfsq + rr))
				} else {
					dk * log_ln2_hi - ((hfsq - (s * (hfsq + rr) + dk * log_ln2_lo)) - f)
				}
			} else if k == 0 {
				f - s * (f - rr)
			} else {
				dk * log_ln2_hi - ((s * (f - rr) - dk * log_ln2_lo) - f)
			}
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

exp_ln2_hi = 6.93147180369123816490e-01

exp_ln2_lo = 1.90821492927058770002e-10

exp_inv_ln2 = 1.44269504088896338700e+00

exp_p1 = 1.66666666666666019037e-01

exp_p2 = -2.77777777770155933842e-03

exp_p3 = 6.61375632143793436117e-05

exp_p4 = -1.65339022054652515390e-06

exp_p5 = 4.13813679705723846039e-08

## Two to the power `n`, for `n` from -1022 to 1023.
exp_two_pow : I64 -> F64
exp_two_pow = |n| F64.from_bits((n + 1023).to_u64_wrap().shl_wrap(52))

log_ln2_hi = 6.93147180369123816490e-01

log_ln2_lo = 1.90821492927058770002e-10

log_g1 = 6.666666666666735130e-01

log_g2 = 3.999999999940941908e-01

log_g3 = 2.857142874366239149e-01

log_g4 = 2.222219843214978396e-01

log_g5 = 1.818357216161805012e-01

log_g6 = 1.531383769920937332e-01

log_g7 = 1.479819860511658591e-01

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

# The C library's `exp` and `log`, through tools/s2_oracle.cc. These two
# functions are fdlibm's, so a result can differ from the C library by one
# unit in the last place and no more.
expect {
	ulps = |a, b| a.to_bits().to_i64_wrap().abs_diff(b.to_bits().to_i64_wrap())
	exps = [(0.0, 1.0), (1.0, 2.7182818284590455), (-1.0, 0.36787944117144233), (0.5, 1.6487212707001282), (-0.5, 0.60653065971263342), (2.0, 7.3890560989306504), (10.0, 22026.465794806718), (-10.0, 4.5399929762484847e-05), (0.3, 1.3498588075760032), (1.0e-10, 1.0000000001), (-1.0e-10, 0.99999999989999999), (100.0, 2.6881171418161356e43), (-100.0, 3.7200759760208361e-44), (700.0, 1.0142320547350045e304), (709.7, 1.6549840276802644e308), (-745.0, 4.9406564584124654e-324), (-720.0, 2.0322308024183599e-313), (0.34, 1.404947590563594), (0.35, 1.4190675485932571), (1.03, 2.8010658346990791), (1.04, 2.8292170143515598), (1.1, 3.0041660239464334), (3.7, 40.447304360067399), (-3.7, 0.024723526470339388), (1.0e-300, 1.0), (5.0e-324, 1.0), (4.916067795588077, 136.46494870257095), (9.671479570429177, 15858.795879023644), (11.807742622627867, 134288.08007666437), (17.698011351082016, 48545465.563133985), (9.595942989597226, 14705.002038247412), (16.892999866616677, 21703842.284024473), (-18.83979086865541, 6.5763176977661317e-09), (-1.375093824875787, 0.25281587427392832), (17.734268679932548, 50337892.422144033), (5.958982125476968, 387.2157864946704), (16.036019670024906, 9212019.6225223038), (-15.471761413874226, 1.9085317651111323e-07), (-1.2372380887134504, 0.29018457622724925), (-10.137086695206786, 3.9583955133438117e-05), (1.7504343694372153, 5.7571028424901485), (2.9576475171240304, 19.252626964741051), (-19.475432416443912, 3.4827890380093477e-09), (-11.330807981446075, 1.1997551370620788e-05), (-8.820705359555587, 0.00014764418126045757), (16.653814872342075, 17086767.172614872)]
	logs = [(1.0e-300, -690.77552789821368), (1.0, 0.0), (1.0, 0.0), (0.5, -0.69314718055994529), (0.5, -0.69314718055994529), (2.0, 0.69314718055994529), (10.0, 2.3025850929940459), (10.0, 2.3025850929940459), (0.3, -1.2039728043259361), (1.0e-10, -23.025850929940457), (1.0e-10, -23.025850929940457), (100.0, 4.6051701859880918), (100.0, 4.6051701859880918), (700.0, 6.5510803350434044), (709.7, 6.5648423455309377), (745.0, 6.6133842183795597), (720.0, 6.5792512120101012), (0.34, -1.0788096613719298), (0.35, -1.0498221244986778), (1.03, 0.029558802241544429), (1.04, 0.039220713153281329), (1.1, 0.095310179804324935), (3.7, 1.3083328196501789), (3.7, 1.3083328196501789), (2.0e-300, -690.08238071765379), (1.0e-300, -690.77552789821368), (1.0, 0.0), (2.0, 0.69314718055994529), (0.5, -0.69314718055994529), (1.0e-310, -713.80137882815416), (1.0e300, 690.77552789821368), (1.0000000001, 1.000000082690371e-10), (0.9999999999, -1.000000082790371e-10), (3.0, 1.0986122886681098), (10.0, 2.3025850929940459), (4.916067795588077, 1.5925089824118037), (9.671479570429177, 2.2691813040100799), (11.807742622627867, 2.4687554707563906), (17.698011351082016, 2.8734522802214935), (9.595942989597226, 2.2613404039007365), (16.892999866616677, 2.8268993270448162), (18.83979086865541, 2.9359711686967671), (1.375093824875787, 0.31852196506384561), (17.734268679932548, 2.8754988513974928), (5.958982125476968, 1.7848996821760115), (16.036019670024906, 2.7748374213961773), (15.471761413874226, 2.7390165180823609), (1.2372380887134504, 0.21288154757656175), (10.137086695206786, 2.3162006487171278), (1.7504343694372153, 0.55986396824312246), (2.9576475171240304, 1.0843941946202442), (19.475432416443912, 2.9691537951788076), (11.330807981446075, 2.4275253859523129), (8.820705359555587, 2.1771018395597799), (16.653814872342075, 2.812639311644126)]
	exps.all(|(x, e)| ulps(S2Math.exp(x), e) <= 1) and logs.all(|(x, e)| ulps(S2Math.log(x), e) <= 1)
}
expect S2Math.exp(0.0) == 1.0
expect S2Math.exp(710.0) == F64.infinity
expect S2Math.exp(-746.0) == 0.0
expect S2Math.exp(F64.nan).is_nan()
expect S2Math.log(1.0) == 0.0
expect S2Math.log(0.0) == -F64.infinity
expect S2Math.log(-1.0).is_nan()
expect S2Math.log(F64.infinity) == F64.infinity

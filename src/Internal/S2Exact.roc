## Exact arithmetic on `F64` values, used to resolve orientation tests that
## floating point cannot decide.
##
## A sum of products of doubles is represented as an *expansion*: a list of
## non-overlapping doubles, ordered by increasing magnitude, whose exact sum is
## the value. Because the components do not overlap, the sign of the whole is
## the sign of the largest component, which is what makes the sign tests here
## exact rather than merely careful.
##
## The technique is Shewchuk's, from "Adaptive Precision Floating-Point
## Arithmetic and Fast Robust Geometric Predicates" (1997). Every operation
## below is error-free: no information is discarded at any step, with one
## limit. The error term of `two_product` is exact only when no partial
## product underflows. A product with a magnitude below about 1e-290 can lose
## bits of its error term, or become zero, because the error term becomes
## subnormal. An operand with a magnitude above about 1e300 overflows in
## `split`. The coordinates of unit-length points stay far from the overflow
## limit, but a component that is almost zero can reach the underflow limit.
##
## Internal to this package.
S2Exact := [].{

	## `2^27 + 1`, the constant that splits a double into two halves whose
	## product with another half is exact.
	splitter : F64
	splitter = 134217729.0

	## Splits `a` into a high and a low half, each with at most 26 significant
	## bits, so that products of halves are exact.
	split : F64 -> (F64, F64)
	split = |a| {
		c = S2Exact.splitter * a
		big = c - a
		hi = c - big
		(hi, a - hi)
	}

	## The exact sum of `a` and `b` as a rounded result plus its error term.
	two_sum : F64, F64 -> (F64, F64)
	two_sum = |a, b| {
		x = a + b
		b_virtual = x - a
		a_virtual = x - b_virtual
		b_roundoff = b - b_virtual
		a_roundoff = a - a_virtual
		(x, a_roundoff + b_roundoff)
	}

	## The exact product of `a` and `b` as a rounded result plus its error
	## term.
	two_product : F64, F64 -> (F64, F64)
	two_product = |a, b| {
		x = a * b
		(a_hi, a_lo) = S2Exact.split(a)
		(b_hi, b_lo) = S2Exact.split(b)
		err1 = x - a_hi * b_hi
		err2 = err1 - a_lo * b_hi
		err3 = err2 - a_hi * b_lo
		(x, a_lo * b_lo - err3)
	}

	## Adds one double to an expansion, keeping the result non-overlapping and
	## ordered by increasing magnitude.
	grow : List(F64), F64 -> List(F64)
	grow = |expansion, b| {
		var $carry = b
		var $out = []
		for term in expansion {
			(sum, error) = S2Exact.two_sum($carry, term)
			$carry = sum
			if error != 0.0 {
				$out = $out.append(error)
			}
		}
		if $carry != 0.0 {
			$out.append($carry)
		} else {
			$out
		}
	}

	## The exact sum of two expansions.
	add : List(F64), List(F64) -> List(F64)
	add = |a, b| b.fold(a, |acc, term| S2Exact.grow(acc, term))

	## The exact product of an expansion and a double.
	scale : List(F64), F64 -> List(F64)
	scale = |expansion, factor| {
		var $out = []
		for term in expansion {
			(hi, lo) = S2Exact.two_product(term, factor)
			$out = S2Exact.grow($out, lo)
			$out = S2Exact.grow($out, hi)
		}
		$out
	}

	## The exact product of three doubles, as an expansion.
	product3 : F64, F64, F64 -> List(F64)
	product3 = |x, y, z| {
		(hi, lo) = S2Exact.two_product(x, y)
		S2Exact.scale([lo, hi], z)
	}

	## The sign of an expansion: `1`, `-1`, or `0`.
	##
	## The components do not overlap, so the largest one decides the sign no
	## matter how many smaller ones follow it.
	sign_of : List(F64) -> I8
	sign_of = |expansion| {
		var $sign = 0
		for term in expansion {
			if term > 0.0 {
				$sign = 1
			} else if term < 0.0 {
				$sign = -1
			}
		}
		$sign
	}

	## The exact sign of the 2x2 determinant `a * d - b * c`.
	det2_sign : F64, F64, F64, F64 -> I8
	det2_sign = |a, b, c, d| {
		(hi1, lo1) = S2Exact.two_product(a, d)
		(hi2, lo2) = S2Exact.two_product(b, c)
		S2Exact.sign_of(S2Exact.add([lo1, hi1], [-lo2, -hi2]))
	}

	## The exact sign of the 3x3 determinant of the three rows.
	det3_sign : (F64, F64, F64), (F64, F64, F64), (F64, F64, F64) -> I8
	det3_sign = |(a0, a1, a2), (b0, b1, b2), (c0, c1, c2)| {
		positive = S2Exact.product3(a0, b1, c2)
			|> S2Exact.add(S2Exact.product3(a1, b2, c0))
			|> S2Exact.add(S2Exact.product3(a2, b0, c1))
		negative = S2Exact.product3(a2, b1, c0)
			|> S2Exact.add(S2Exact.product3(a0, b2, c1))
			|> S2Exact.add(S2Exact.product3(a1, b0, c2))
		S2Exact.sign_of(S2Exact.add(positive, negative.map(|t| -t)))
	}

	## The expansion whose value is exactly `a`.
	from_f64 : F64 -> List(F64)
	from_f64 = |a| if (a == 0.0) [] else [a]

	## The exact negation of an expansion.
	negate : List(F64) -> List(F64)
	negate = |expansion| expansion.map(|t| -t)

	## The exact difference of two expansions.
	sub : List(F64), List(F64) -> List(F64)
	sub = |a, b| S2Exact.add(a, S2Exact.negate(b))

	## The exact product of two expansions.
	mul : List(F64), List(F64) -> List(F64)
	mul = |a, b| b.fold([], |acc, term| S2Exact.add(acc, S2Exact.scale(a, term)))

	## The exact square of an expansion.
	square : List(F64) -> List(F64)
	square = |a| S2Exact.mul(a, a)

	## The exact cross product of two vectors of doubles, as a vector of
	## expansions.
	cross : (F64, F64, F64), (F64, F64, F64) -> (List(F64), List(F64), List(F64))
	cross = |(a0, a1, a2), (b0, b1, b2)| (
		S2Exact.det2(a1, a2, b1, b2),
		S2Exact.det2(a2, a0, b2, b0),
		S2Exact.det2(a0, a1, b0, b1),
	)

	## The exact 2x2 determinant `a * d - b * c`.
	det2 : F64, F64, F64, F64 -> List(F64)
	det2 = |a, b, c, d| {
		(hi1, lo1) = S2Exact.two_product(a, d)
		(hi2, lo2) = S2Exact.two_product(b, c)
		S2Exact.add([lo1, hi1], [-lo2, -hi2])
	}

	## The exact cross product of two vectors of expansions.
	cross_exact : (List(F64), List(F64), List(F64)), (List(F64), List(F64), List(F64)) -> (List(F64), List(F64), List(F64))
	cross_exact = |(a0, a1, a2), (b0, b1, b2)| (
		S2Exact.sub(S2Exact.mul(a1, b2), S2Exact.mul(a2, b1)),
		S2Exact.sub(S2Exact.mul(a2, b0), S2Exact.mul(a0, b2)),
		S2Exact.sub(S2Exact.mul(a0, b1), S2Exact.mul(a1, b0)),
	)

	## The exact dot product of two vectors of expansions.
	dot_exact : (List(F64), List(F64), List(F64)), (List(F64), List(F64), List(F64)) -> List(F64)
	dot_exact = |(a0, a1, a2), (b0, b1, b2)|
		S2Exact.mul(a0, b0)
			|> S2Exact.add(S2Exact.mul(a1, b1))
			|> S2Exact.add(S2Exact.mul(a2, b2))

	## A vector of doubles as a vector of expansions.
	vector : (F64, F64, F64) -> (List(F64), List(F64), List(F64))
	vector = |(x, y, z)| (S2Exact.from_f64(x), S2Exact.from_f64(y), S2Exact.from_f64(z))

	## The exact dot product of two vectors of doubles.
	dot : (F64, F64, F64), (F64, F64, F64) -> List(F64)
	dot = |a, b| S2Exact.dot_exact(S2Exact.vector(a), S2Exact.vector(b))

	## The exact squared length of a vector of expansions.
	norm2_exact : (List(F64), List(F64), List(F64)) -> List(F64)
	norm2_exact = |v| S2Exact.dot_exact(v, v)

	## The value of an expansion rounded to the nearest double, with ties to
	## the even neighbour, as upstream's `ExactFloat` conversion rounds.
	##
	## A first estimate sums the components. The exact remainder then decides
	## whether a neighbour of that estimate is nearer, and the step repeats
	## until no neighbour is. The estimate is within a few units in the last
	## place, so the loop stops after a few steps.
	to_f64 : List(F64) -> F64
	to_f64 = |expansion| {
		sign = S2Exact.sign_of(expansion)
		if sign == 0 {
			return 0.0
		}
		# Work with a positive value; the neighbours of a positive double are
		# the next bit patterns.
		positive = if (sign < 0) S2Exact.negate(expansion) else expansion
		var $estimate = positive.fold(0.0, |acc, t| acc + t)
		var $steps = 0.U64
		while $steps < 64 {
			$steps = $steps + 1
			remainder = S2Exact.grow(positive, $estimate.negate())
			above = S2Exact.sign_of(remainder)
			if above == 0 {
				break
			}
			neighbour =
				if above > 0 {
					F64.from_bits($estimate.to_bits() + 1)
				} else {
					F64.from_bits($estimate.to_bits() - 1)
				}
			# Half the gap to the neighbour, which is exact.
			half_gap = 0.5 * (neighbour - $estimate)
			beyond = S2Exact.sign_of(S2Exact.grow(remainder, -half_gap)) * above
			if beyond > 0 {
				$estimate = neighbour
			} else if beyond == 0 and $estimate.to_bits() % 2 == 1 {
				# A tie goes to the even neighbour.
				$estimate = neighbour
				break
			} else {
				break
			}
		}
		if (sign < 0) $estimate.negate() else $estimate
	}

	## The expansion multiplied by `2^n`, which is exact while nothing
	## overflows or underflows.
	scale_by_power_of_two : List(F64), I32 -> List(F64)
	scale_by_power_of_two = |expansion, n| {
		var $out = expansion
		var $left = n
		while $left != 0 {
			step = $left.max(-600).min(600)
			factor = power_of_two(step)
			$out = $out.map(|t| t * factor)
			$left = $left - step
		}
		$out
	}

	## True when every component of a vector of expansions is zero.
	is_zero : (List(F64), List(F64), List(F64)) -> Bool
	is_zero = |(x, y, z)|
		S2Exact.sign_of(x) == 0 and S2Exact.sign_of(y) == 0 and S2Exact.sign_of(z) == 0

	## The exponent `e` of the exact value `v` of a non-zero expansion, for
	## which `2^(e - 1) <= |v| < 2^e`. This is the exponent `frexp` gives, and
	## upstream's `ExactFloat::exp`.
	##
	## The largest component gives a first guess. The smaller components can
	## carry the value across a power of two, so exact comparisons correct it.
	exponent : List(F64) -> I32
	exponent = |expansion| {
		magnitude = if (S2Exact.sign_of(expansion) < 0) S2Exact.negate(expansion) else expansion
		top = magnitude.fold(0.0, |acc, t| if (t.abs() > acc) t.abs() else acc)
		var $e = frexp_exponent(top)
		var $steps = 0.U64
		while $steps < 4 {
			$steps = $steps + 1
			if $e > -1073 and S2Exact.sign_of(S2Exact.grow(magnitude, -pow2($e - 1))) < 0 {
				$e = $e - 1
			} else if $e < 1024 and S2Exact.sign_of(S2Exact.grow(magnitude, -pow2($e))) >= 0 {
				$e = $e + 1
			} else {
				break
			}
		}
		$e
	}

	## Upstream's `NormalizableFromExact` for the vector `v * 2^-shift`, where
	## `v` is the given vector of expansions.
	##
	## The vector is rounded to doubles. When its largest component is then
	## below `2^-242`, too small to normalize without a loss of precision, it
	## is first scaled by a power of two so that its largest component is in
	## `[0.5, 1)`. The zero vector gives zero. The result is not normalized.
	##
	## The `shift` lets a caller scale its inputs up to keep the products of
	## small coordinates exact, and take the scale out here.
	normalizable_from_exact : (List(F64), List(F64), List(F64)), I32 -> (F64, F64, F64)
	normalizable_from_exact = |(x, y, z), shift| {
		round = |e| S2Exact.to_f64(S2Exact.scale_by_power_of_two(e, -shift))
		rounded = (round(x), round(y), round(z))
		if is_normalizable(rounded) {
			return rounded
		}
		exponents = [x, y, z].keep_if(|e| S2Exact.sign_of(e) != 0).map(S2Exact.exponent)
		match exponents.max() {
			Ok(e) => {
				scaled = |c| S2Exact.to_f64(S2Exact.scale_by_power_of_two(c, -e))
				(scaled(x), scaled(y), scaled(z))
			}
			Err(_) => (0.0, 0.0, 0.0)
		}
	}

	## Upstream's `EnsureNormalizable`: the vector itself when its largest
	## component is at least `2^-242`, and otherwise the vector scaled by a
	## power of two so that its largest component is in `[1, 2)`.
	##
	## Requires a non-zero vector. Upstream multiplies by one power of two,
	## which overflows for a subnormal component; this port scales in steps.
	ensure_normalizable : (F64, F64, F64) -> (F64, F64, F64)
	ensure_normalizable = |(x, y, z)| {
		if is_normalizable((x, y, z)) {
			return (x, y, z)
		}
		p_max = x.abs().max(y.abs()).max(z.abs())
		# ldexp(2, -1 - ilogb(p_max)) is 2^(1 - e) for the frexp exponent e.
		n = 1 - frexp_exponent(p_max)
		(scale_f64(x, n), scale_f64(y, n), scale_f64(z, n))
	}

	## Upstream's `SymbolicCrossProd`: the direction of `a x b` for exactly
	## proportional `a` and `b` under the symbolic perturbation that
	## `S2Predicates.sign` uses, scaled by `ensure_normalizable`. Requires
	## `a != b`.
	symbolic_cross : (F64, F64, F64), (F64, F64, F64) -> (F64, F64, F64)
	symbolic_cross = |a, b|
		if lexicographic_less(a, b) {
			S2Exact.ensure_normalizable(symbolic_cross_sorted(a, b))
		} else {
			(x, y, z) = S2Exact.ensure_normalizable(symbolic_cross_sorted(b, a))
			(-x, -y, -z)
		}

	## Upstream's `ExactCrossProd`: the cross product of `a` and `b` in exact
	## arithmetic, rounded by `normalizable_from_exact`, and the symbolic
	## cross product `symbolic_cross` when the exact one is zero. Requires
	## `a != b`.
	##
	## Each input is first scaled by a power of two that puts its largest
	## coordinate near `2^256`. The cross product is linear in each input,
	## so this changes only its scale, which `normalizable_from_exact` takes
	## out again. It keeps the error terms of the products exact when a
	## coordinate is tiny or subnormal, where they would otherwise underflow.
	exact_cross_prod : (F64, F64, F64), (F64, F64, F64) -> (F64, F64, F64)
	exact_cross_prod = |a, b| {
		a_shift = 256 - frexp_exponent(largest_abs(a))
		b_shift = 256 - frexp_exponent(largest_abs(b))
		product = S2Exact.cross(scale3(a, a_shift), scale3(b, b_shift))
		if S2Exact.is_zero(product) {
			S2Exact.symbolic_cross(a, b)
		} else {
			S2Exact.normalizable_from_exact(product, a_shift + b_shift)
		}
	}
}

## True when the largest component of the vector is at least `2^-242`, which
## is large enough to normalize, and to measure the angle to another such
## vector, without a loss of precision to underflow.
is_normalizable : (F64, F64, F64) -> Bool
is_normalizable = |v| largest_abs(v) >= pow2(-242)

## The largest magnitude among the three components.
largest_abs : (F64, F64, F64) -> F64
largest_abs = |(x, y, z)| x.abs().max(y.abs()).max(z.abs())

## The lexicographic order on `(x, y, z)` that the symbolic perturbations are
## defined against.
lexicographic_less : (F64, F64, F64), (F64, F64, F64) -> Bool
lexicographic_less = |(ax, ay, az), (bx, by, bz)|
	if ax != bx {
		ax < bx
	} else if ay != by {
		ay < by
	} else {
		az < bz
	}

## `symbolic_cross` for `a < b`, before scaling. The tests enumerate the
## coefficients of the perturbations in decreasing order of size, and the
## first non-zero one decides. The last two cases need `b` to be zero.
symbolic_cross_sorted : (F64, F64, F64), (F64, F64, F64) -> (F64, F64, F64)
symbolic_cross_sorted = |(ax, ay, _az), (bx, by, bz)|
	if bx != 0.0 or by != 0.0 {
		(-by, bx, 0.0)
	} else if bz != 0.0 {
		(bz, 0.0, 0.0)
	} else if ax != 0.0 or ay != 0.0 {
		(ay, -ax, 0.0)
	} else {
		(1.0, 0.0, 0.0)
	}

## The vector multiplied by `2^n`.
scale3 : (F64, F64, F64), I32 -> (F64, F64, F64)
scale3 = |(x, y, z), n| (scale_f64(x, n), scale_f64(y, n), scale_f64(z, n))

## `x` multiplied by `2^n`, in steps whose factors are exact doubles.
scale_f64 : F64, I32 -> F64
scale_f64 = |x, n| {
	var $out = x
	var $left = n
	while $left != 0 {
		step = $left.max(-1000).min(1000)
		$out = $out * pow2(step)
		$left = $left - step
	}
	$out
}

## `2^n` for `n` in `[-1074, 1023]`, built from its bits so that it is exact
## in the subnormal range too.
pow2 : I32 -> F64
pow2 = |n|
	if n >= -1022 {
		F64.from_bits((n + 1023).to_u64_wrap().shl_wrap(52))
	} else {
		F64.from_bits((1.U64).shl_wrap((n + 1074).to_u8_wrap()))
	}

## The exponent `e` for which `x = m * 2^e` with `0.5 <= |m| < 1`, as `frexp`
## gives it. Zero for zero.
frexp_exponent : F64 -> I32
frexp_exponent = |x| {
	magnitude = x.abs()
	if magnitude == 0.0 or !magnitude.is_finite() {
		return 0
	}
	raw = magnitude.to_bits().shr_zf_wrap(52).bitwise_and(0x7ff).to_i32_wrap()
	if raw == 0 {
		# A subnormal: the position of its top bit.
		mantissa = magnitude.to_bits()
		-1074 + (64 - mantissa.count_leading_zero_bits().to_i32())
	} else {
		raw - 1022
	}
}

## `2^n` for `n` in `[-600, 600]`.
power_of_two : I32 -> F64
power_of_two = |n| {
	two : F64
	two = 2.0
	if n >= 0 {
		two.pow(n.to_f64())
	} else {
		1.0 / two.pow((-n).to_f64())
	}
}

expect S2Exact.two_sum(1.0, 1e-20) == (1.0, 1e-20)
expect S2Exact.sign_of([]) == 0
expect S2Exact.sign_of([1e-30, -1.0]) == -1
expect S2Exact.sign_of([-1e-30, 1.0]) == 1
expect S2Exact.det2_sign(1.0, 0.0, 0.0, 1.0) == 1
expect S2Exact.det2_sign(0.0, 1.0, 1.0, 0.0) == -1
expect S2Exact.det2_sign(2.0, 1.0, 4.0, 2.0) == 0
expect S2Exact.det3_sign((1.0, 0.0, 0.0), (0.0, 1.0, 0.0), (0.0, 0.0, 1.0)) == 1
expect S2Exact.det3_sign((0.0, 1.0, 0.0), (1.0, 0.0, 0.0), (0.0, 0.0, 1.0)) == -1
expect S2Exact.det3_sign((1.0, 2.0, 3.0), (2.0, 4.0, 6.0), (1.0, 0.0, 1.0)) == 0

# 2^27+1 times 2^27-1 is 2^54-1, one bit too wide for a double, so the naive
# product rounds up to 2^54 and the naive difference below is exactly zero.
# The exact difference is -1.
expect {
	x = 134217729.0
	y = 134217727.0
	two_54 = 18014398509481984.0
	x * y - two_54 == 0.0 and S2Exact.det2_sign(x, 1.0, two_54, y) == -1
}

# The same cancellation inside a 3x3 determinant, whose value is -1.
expect {
	x = 134217729.0
	y = 134217727.0
	two_54 = 18014398509481984.0
	S2Exact.det3_sign((x, 1.0, 0.0), (two_54, y, 0.0), (0.0, 0.0, 1.0)) == -1
}

# two_product recovers the bit the rounded product dropped.
expect {
	(hi, lo) = S2Exact.two_product(134217729.0, 134217727.0)
	hi == 18014398509481984.0 and lo == -1.0
}

# Nearly proportional rows from the exact corpus in `tests/ExactCorpus.roc`,
# whose signs come from rational arithmetic. Naive doubles give 0 for each one.
expect S2Exact.det2_sign(0.32677721703340623, -0.604824612593132, 0.3267772170334063, -0.6048246125931321) == -1
expect S2Exact.det2_sign(0.7219546678013288, 0.5260949552878555, 0.7219546678013289, 0.5260949552878557) == 1
expect S2Exact.det2_sign(0.5980446657127914, 0.6959116725577938, 0.5980446657127915, 0.695911672557794) == -1
expect S2Exact.det2_sign(0.9525510241450761, 0.7034237480599241, 0.9525510241450762, 0.7034237480599242) == 1

# to_f64 rounds to the nearest double, with ties to the even neighbour. 1 +
# 2^-53 is halfway between 1 and 1 + 2^-52, and 1 + 3 * 2^-53 is halfway
# between 1 + 2^-52 and 1 + 2^-51.
expect S2Exact.to_f64([1.1102230246251565e-16, 1.0]) == 1.0
expect S2Exact.to_f64([1.1102230246251565e-16, 1.0000000000000002]) == 1.0000000000000004
expect S2Exact.to_f64([5.551115123125783e-17, 1.0]) == 1.0
expect S2Exact.to_f64([-1e-30, -1.1102230246251565e-16, -1.0]) == -1.0000000000000002
expect S2Exact.to_f64([]) == 0.0

# (2^27 + 1)^2 = 2^54 + 2^28 + 1. The nearest double drops the 1, and the
# exact square keeps it.
expect {
	square = S2Exact.square([134217729.0])
	S2Exact.to_f64(square) == 18014398777917440.0
		and S2Exact.sign_of(S2Exact.sub(square, [18014398777917440.0])) == 1
}
expect S2Exact.to_f64(S2Exact.mul([0.5, 3.0], [-2.0])) == -7.0
expect S2Exact.scale_by_power_of_two([3.0], -2) == [0.75]
# A shift larger than one step goes in several steps.
expect S2Exact.scale_by_power_of_two([1.0], 1000) == [1.0715086071862673e301]
expect S2Exact.sign_of(S2Exact.dot_exact(S2Exact.cross((1.0, 2.0, 3.0), (4.0, 5.0, 6.0)), S2Exact.vector((1.0, 2.0, 3.0)))) == 0

# Upstream's internal::SymbolicCrossProd and ExactCrossProd at v0.14.0,
# through tools/s2_oracle.cc. The first three are the cases that cannot occur
# in practice from upstream's RobustCrossProdCoverage test, where one input is
# zero.
expect S2Exact.symbolic_cross((-1.0, 0.0, 0.0), (0.0, 0.0, 0.0)) == (0.0, 1.0, 0.0)
expect S2Exact.symbolic_cross((0.0, 0.0, 0.0), (0.0, -1.0, 0.0)) == (1.0, 0.0, -0.0)
expect S2Exact.symbolic_cross((0.0, 0.0, 0.0), (0.0, 0.0, -1.0)) == (-1.0, -0.0, -0.0)
# Tiny inputs whose cross product is far below the smallest double.
expect S2Exact.exact_cross_prod((1e-200, 0.0, 0.0), (0.0, 1e-200, 0.0)) == (0.0, 0.0, 0.58591449441984966)
expect S2Exact.exact_cross_prod((3.0, 0.0, 0.0), (0.0, 1e-300, 1e-300)) == (0.0, -0.50226965961856285, 0.50226965961856285)
expect S2Exact.exponent([1.0]) == 1
expect S2Exact.exponent([-0.75]) == 0
expect S2Exact.exponent([5e-324]) == -1073
# 1 - 2^-60 is below 1, although its largest component is 1.
expect S2Exact.exponent([-8.673617379884035e-19, 1.0]) == 0
expect S2Exact.exponent([1.1102230246251565e-16, 0.5, 1.0]) == 1

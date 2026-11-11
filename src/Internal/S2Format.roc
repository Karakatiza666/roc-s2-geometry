## The number formatting and parsing that upstream's text format relies on
## from the C library and from abseil: `printf("%.15g")` and
## `absl::SimpleAtod`.
##
## Internal to this package.
S2Format := [].{

	## The text that C's `"%.{precision}g"` gives for `x`.
	##
	## The value is `m * 2^e` with `m` below `2^53`. Its exact decimal
	## expansion is `m * 5^k` shifted by `k` places for a negative `e = -k`,
	## and `m * 2^e` for a positive one, so the digits are found with integer
	## arithmetic on a list of decimal digits. The rounding to `precision`
	## significant digits is then exact and goes to the even digit on a tie, as
	## the C library does. Trailing zeros are removed, and the exponent form
	## is used when the exponent is below -4 or at least `precision`.
	general : F64, U64 -> Str
	general = |x, precision| {
		bits = x.to_bits()
		negative = bits.shr_zf_wrap(63) == 1
		sign = if (negative) "-" else ""
		if x.is_nan() {
			return "${sign}nan"
		}
		if !x.is_finite() {
			return "${sign}inf"
		}
		if x == 0.0 {
			return "${sign}0"
		}
		p = precision.max(1)
		exponent_field = bits.shr_zf_wrap(52).bitwise_and(0x7ff)
		fraction = bits.bitwise_and(0xfffffffffffff)
		mantissa = if (exponent_field == 0) fraction else fraction.bitwise_or(0x10000000000000)
		exponent = if (exponent_field == 0) -1074 else exponent_field.to_i64_wrap() - 1075
		start = digits_of(mantissa)
		# The value is `exact * 10^-shift`.
		exact_and_shift =
			if exponent >= 0 {
				(times_pow(start, 2, exponent.to_u64_wrap()), 0)
			} else {
				k = (-exponent).to_u64_wrap()
				(times_pow(start, 5, k), k)
			}
		(exact_digits, shift) = exact_and_shift
		# `exact_digits` is least significant first.
		digits = exact_digits.rev()
		n = digits.len()
		unrounded_exponent = n.to_i64_wrap() - 1 - shift.to_i64_wrap()
		rounded = round_digits(digits, p)
		(kept, carried) = rounded
		decimal_exponent = if (carried) unrounded_exponent + 1 else unrounded_exponent
		body =
			if decimal_exponent < -4 or decimal_exponent >= p.to_i64_wrap() {
				scientific(kept, decimal_exponent)
			} else {
				fixed(kept, decimal_exponent)
			}
		"${sign}${body}"
	}

	## The number that `absl::SimpleAtod` reads from `text`, or an error when
	## abseil would refuse the text.
	##
	## Whitespace is stripped from both ends. The rest must be an optional
	## sign (a `+` is allowed only without a following `-`), then either
	## `inf`, `infinity` or `nan` in any case, or decimal digits with an
	## optional point and an optional exponent, or `0x` and hexadecimal
	## digits with an optional point and an optional binary exponent after a
	## `p`. A number too large for a double is infinite, and one too small is
	## zero. A hexadecimal number that is below the smallest normal double and
	## has more than 16 digits can differ from abseil in the last bit.
	parse_double : Str -> Try(F64, [InvalidNumber])
	parse_double = |text| {
		stripped = strip_ascii(text.to_utf8())
		unsigned_plus =
			match stripped {
				['+', '-', ..] => return Err(InvalidNumber)
				['+', .. as rest] => rest
				_ => stripped
			}
		(negative, body) =
			match unsigned_plus {
				['-', .. as rest] => (Bool.True, rest)
				_ => (Bool.False, unsigned_plus)
			}
		lowered = body.map(ascii_lower)
		magnitude =
			if lowered == "inf".to_utf8() or lowered == "infinity".to_utf8() {
				Ok(F64.infinity)
			} else if is_nan_text(lowered) {
				Ok(F64.nan)
			} else if is_hex_prefix(body) {
				parse_hex(body.drop_first(2))
			} else {
				parse_decimal(body)
			}
		value = magnitude?
		Ok(if (negative) -value else value)
	}

	## The bytes of `text` without the ASCII whitespace at either end.
	## Abseil's `StripAsciiWhitespace`.
	strip_ascii_whitespace : Str -> Str
	strip_ascii_whitespace = |text| Str.from_utf8_lossy(strip_ascii(text.to_utf8()))

	## True when the text is nothing but ASCII whitespace.
	is_blank : Str -> Bool
	is_blank = |text| strip_ascii(text.to_utf8()).is_empty()
}

is_space : U8 -> Bool
is_space = |b| b == 32 or (b >= 9 and b <= 13)

strip_ascii : List(U8) -> List(U8)
strip_ascii = |bytes| {
	var $start = 0.U64
	var $end = bytes.len()
	while $start < $end and is_space(bytes.get($start) ?? 0) {
		$start = $start + 1
	}
	while $end > $start and is_space(bytes.get($end - 1) ?? 0) {
		$end = $end - 1
	}
	bytes.sublist({ start: $start, len: $end - $start })
}

ascii_lower : U8 -> U8
ascii_lower = |b| if (b >= 65 and b <= 90) b + 32 else b

is_digit : U8 -> Bool
is_digit = |b| b >= 48 and b <= 57

## `nan` or `nan(chars)` where chars are letters, digits and underscores.
is_nan_text : List(U8) -> Bool
is_nan_text = |lowered|
	match lowered {
		['n', 'a', 'n'] => Bool.True
		['n', 'a', 'n', '(', .. as rest] =>
			match rest.last() {
				Ok(')') =>
					rest.drop_last(1).all(
						|b| is_digit(b) or (b >= 97 and b <= 122) or b == 95,
					)
				_ => Bool.False
			}
		_ => Bool.False
	}

is_hex_prefix : List(U8) -> Bool
is_hex_prefix = |body|
	match body {
		['0', 'x', ..] => Bool.True
		['0', 'X', ..] => Bool.True
		_ => Bool.False
	}

## The value of a digit in base 16, or 255 for a byte that is not one.
hex_value : U8 -> U8
hex_value = |b|
	if b >= 48 and b <= 57 {
		b - 48
	} else if b >= 97 and b <= 102 {
		b - 87
	} else if b >= 65 and b <= 70 {
		b - 55
	} else {
		255
	}

is_hex_digit : U8 -> Bool
is_hex_digit = |b| hex_value(b) != 255

## The value of hexadecimal digits with an optional point and an optional
## exponent of two, given without their `0x` prefix. The first 16 digits
## are kept exactly, and a lower bit stands for any digit after them that is
## not zero, so the final conversion rounds correctly.
parse_hex : List(U8) -> Try(F64, [InvalidNumber])
parse_hex = |body| {
	whole_len = count_while(body, is_hex_digit)
	after_whole = body.drop_first(whole_len)
	(fraction_len, after_fraction) =
		match after_whole {
			['.', .. as rest] => {
				len = count_while(rest, is_hex_digit)
				(len, rest.drop_first(len))
			}
			_ => (0, after_whole)
		}
	if whole_len + fraction_len == 0 {
		return Err(InvalidNumber)
	}
	binary_exponent =
		match after_fraction {
			[] => Ok(0)
			[e, .. as rest] if e == 'p' or e == 'P' => {
				negative = rest.first() == Ok('-')
				digits =
					match rest {
						['+', .. as tail] => tail
						['-', .. as tail] => tail
						_ => rest
					}
				if digits.is_empty() or !digits.all(is_digit) {
					Err(InvalidNumber)
				} else {
					magnitude = digits.fold(0.I64, |acc, d| (acc * 10 + (d - 48).to_i64()).min(1000000))
					Ok(if (negative) -magnitude else magnitude)
				}
			}
			_ => Err(InvalidNumber)
		}
	exponent = binary_exponent?
	fraction_start = if (fraction_len > 0) whole_len + 1 else whole_len
	all_digits =
		body.take_first(whole_len)
			.concat(if (fraction_len > 0) body.drop_first(fraction_start).take_first(fraction_len) else [])
			.map(hex_value)
	digits = drop_leading_zeros(all_digits)
	if digits.is_empty() {
		return Ok(0.0)
	}
	kept = digits.take_first(16)
	dropped = digits.drop_first(16)
	mantissa = kept.fold(0.U64, |acc, d| acc * 16 + d.to_u64())
	sticky = dropped.any(|d| d != 0)
	rounded_mantissa = if (sticky) mantissa.bitwise_or(1) else mantissa
	scale = 4 * dropped.len().to_i64_wrap() - 4 * fraction_len.to_i64_wrap() + exponent
	Ok(scale_by_two_power(rounded_mantissa.to_f64(), scale))
}

drop_leading_zeros : List(U8) -> List(U8)
drop_leading_zeros = |digits| {
	var $n = 0.U64
	var $going = Bool.True
	for d in digits {
		if $going {
			if d == 0 {
				$n = $n + 1
			} else {
				$going = Bool.False
			}
		}
	}
	digits.drop_first($n)
}

## `x * 2^n`, in steps that never overflow the factor.
scale_by_two_power : F64, I64 -> F64
scale_by_two_power = |x, n| {
	var $x = x
	var $n = n
	while $n > 1000 and $x != 0.0 and $x.is_finite() {
		$x = $x * power_of_two(1000)
		$n = $n - 1000
	}
	while $n < -1000 and $x != 0.0 {
		$x = $x * power_of_two(-1000)
		$n = $n + 1000
	}
	if $x == 0.0 or !$x.is_finite() {
		$x
	} else {
		$x * power_of_two($n)
	}
}

## Two to the power `n`, for `n` from -1022 to 1023.
power_of_two : I64 -> F64
power_of_two = |n| F64.from_bits((n + 1023).to_u64_wrap().shl_wrap(52))

## The value of a run of decimal digits with an optional point and exponent,
## as one whole text.
parse_decimal : List(U8) -> Try(F64, [InvalidNumber])
parse_decimal = |body| {
	whole_len = count_while(body, is_digit)
	after_whole = body.drop_first(whole_len)
	(fraction_len, after_fraction) =
		match after_whole {
			['.', .. as rest] => {
				len = count_while(rest, is_digit)
				(len, rest.drop_first(len))
			}
			_ => (0, after_whole)
		}
	has_point = after_whole.first() == Ok('.')
	if whole_len + fraction_len == 0 {
		return Err(InvalidNumber)
	}
	exponent_text =
		match after_fraction {
			[] => Ok([])
			[e, .. as rest] if e == 'e' or e == 'E' => {
				signed =
					match rest {
						['+', .. as tail] => tail
						['-', .. as tail] => ['-'].concat(tail)
						_ => rest
					}
				digits = if (signed.first() == Ok('-')) signed.drop_first(1) else signed
				if digits.is_empty() or !digits.all(is_digit) {
					Err(InvalidNumber)
				} else {
					Ok(signed)
				}
			}
			_ => Err(InvalidNumber)
		}
	exponent = exponent_text?
	whole = if (whole_len == 0) ['0'] else body.take_first(whole_len)
	fraction_digits =
		if has_point and fraction_len > 0 {
			after_whole.drop_first(1).take_first(fraction_len)
		} else {
			['0']
		}
	canonical = whole.concat(['.']).concat(fraction_digits)
	full = if (exponent.is_empty()) canonical else canonical.concat(['e']).concat(exponent)
	text = Str.from_utf8_lossy(full)
	match F64.from_str(text) {
		Ok(value) => Ok(value)
		Err(_) => Ok(overflow_or_underflow(exponent))
	}
}

## What a number that `F64.from_str` refused is: abseil gives infinity for
## a huge exponent and zero for a tiny one.
overflow_or_underflow : List(U8) -> F64
overflow_or_underflow = |exponent|
	if exponent.first() == Ok('-') {
		0.0
	} else {
		F64.infinity
	}

count_while : List(U8), (U8 -> Bool) -> U64
count_while = |bytes, test| {
	var $n = 0.U64
	var $going = Bool.True
	for b in bytes {
		if $going {
			if test(b) {
				$n = $n + 1
			} else {
				$going = Bool.False
			}
		}
	}
	$n
}

## The decimal digits of `n`, least significant first.
digits_of : U64 -> List(U8)
digits_of = |n| {
	var $rest = n
	var $out = []
	while $rest > 0 {
		$out = $out.append(($rest % 10).to_u8_wrap())
		$rest = $rest // 10
	}
	$out
}

## `digits` (least significant first) times `factor`.
times_small : List(U8), U64 -> List(U8)
times_small = |digits, factor| {
	var $out = List.with_capacity(digits.len() + 12)
	var $carry = 0.U64
	for d in digits {
		t = d.to_u64() * factor + $carry
		$out = $out.append((t % 10).to_u8_wrap())
		$carry = t // 10
	}
	while $carry > 0 {
		$out = $out.append(($carry % 10).to_u8_wrap())
		$carry = $carry // 10
	}
	$out
}

## `digits` times `base` to the power `times`, with `base` 2 or 5.
times_pow : List(U8), U64, U64 -> List(U8)
times_pow = |digits, base, times| {
	# 2^30 and 5^13 are the largest chunks whose product with a digit stays far
	# below 2^64.
	chunk_exponent = if (base == 2) 30.U64 else 13
	chunk = if (base == 2) 1073741824.U64 else 1220703125
	var $out = digits
	var $left = times
	while $left >= chunk_exponent {
		$out = times_small($out, chunk)
		$left = $left - chunk_exponent
	}
	var $tail = 1.U64
	var $i = 0.U64
	while $i < $left {
		$tail = $tail * base
		$i = $i + 1
	}
	if $left > 0 {
		times_small($out, $tail)
	} else {
		$out
	}
}

## The first `p` digits of `digits` (most significant first) rounded to the
## nearest, ties to even, and whether rounding carried into a new leading
## digit. The result always has `p` digits.
round_digits : List(U8), U64 -> (List(U8), Bool)
round_digits = |digits, p| {
	n = digits.len()
	if n <= p {
		return (digits.concat(List.repeat(0, p - n)), Bool.False)
	}
	head = digits.take_first(p)
	rest = digits.drop_first(p)
	first = rest.first() ?? 0
	any_more = rest.drop_first(1).any(|d| d != 0)
	last_odd = (head.last() ?? 0) % 2 == 1
	round_up = first > 5 or (first == 5 and (any_more or last_odd))
	if !round_up {
		return (head, Bool.False)
	}
	incremented = increment(head)
	if incremented.len() > p {
		(incremented.take_first(p), Bool.True)
	} else {
		(incremented, Bool.False)
	}
}

## One added to a number given as digits, most significant first. The result
## has one more digit when every digit was 9.
increment : List(U8) -> List(U8)
increment = |digits| {
	var $out = []
	var $carry = 1.U8
	for d in digits.rev() {
		sum = d + $carry
		if sum == 10 {
			$out = $out.append(0)
			$carry = 1
		} else {
			$out = $out.append(sum)
			$carry = 0
		}
	}
	if $carry == 1 {
		$out.append(1).rev()
	} else {
		$out.rev()
	}
}

digit_text : List(U8) -> Str
digit_text = |digits| Str.from_utf8_lossy(digits.map(|d| d + 48))

without_trailing_zeros : List(U8) -> List(U8)
without_trailing_zeros = |digits| {
	var $n = digits.len()
	while $n > 0 and (digits.get($n - 1) ?? 1) == 0 {
		$n = $n - 1
	}
	digits.take_first($n)
}

## `d.ddde+XX` with the trailing zeros of the fraction removed.
scientific : List(U8), I64 -> Str
scientific = |digits, exponent| {
	lead = digits.take_first(1)
	fraction = without_trailing_zeros(digits.drop_first(1))
	mantissa =
		if fraction.is_empty() {
			digit_text(lead)
		} else {
			"${digit_text(lead)}.${digit_text(fraction)}"
		}
	magnitude = exponent.abs_diff(0).to_u64()
	sign = if (exponent < 0) "-" else "+"
	padding = if (magnitude < 10) "0" else ""
	"${mantissa}e${sign}${padding}${magnitude.to_str()}"
}

## The digits placed around the decimal point for a number with the given
## decimal exponent, trailing zeros of the fraction removed.
fixed : List(U8), I64 -> Str
fixed = |digits, exponent| {
	if exponent >= 0 {
		int_len = (exponent + 1).to_u64_wrap()
		whole = digit_text(digits.take_first(int_len))
		fraction = without_trailing_zeros(digits.drop_first(int_len))
		if (fraction.is_empty()) "${whole}" else "${whole}.${digit_text(fraction)}"
	} else {
		zeros = Str.repeat("0", (-exponent - 1).to_u64_wrap())
		fraction = without_trailing_zeros(digits)
		"0.${zeros}${digit_text(fraction)}"
	}
}

# `"%.15g"` and its relatives, as printed by the C library behind
# tools/s2_oracle.cc. The cases cover the exponent form on both sides, a carry
# into a new digit, and exact ties (100000000000000.5 goes to the even digit,
# 100000000000001.5 also does).
expect S2Format.general(37.7749, 15) == "37.7749"
expect S2Format.general(1.0e-20, 15) == "1e-20"
expect S2Format.general(1.0e-30, 15) == "1e-30"
expect S2Format.general(0.0, 15) == "0"
expect S2Format.general(-0.0, 15) == "-0"
expect S2Format.general(100000.0, 15) == "100000"
expect S2Format.general(1000000000000000.0, 15) == "1e+15"
expect S2Format.general(1.2345678901234568e17, 15) == "1.23456789012346e+17"
expect S2Format.general(0.0001, 15) == "0.0001"
expect S2Format.general(1.234e-05, 15) == "1.234e-05"
expect S2Format.general(5.0e-324, 15) == "4.94065645841247e-324"
expect S2Format.general(1.7976931348623157e308, 15) == "1.79769313486232e+308"
expect S2Format.general(0.1, 15) == "0.1"
expect S2Format.general(2.5e-05, 15) == "2.5e-05"
expect S2Format.general(999999999999999.5, 15) == "1e+15"
expect S2Format.general(99999.99999999999, 15) == "100000"
expect S2Format.general(-122.4194, 15) == "-122.4194"
expect S2Format.general(180.0, 15) == "180"
expect S2Format.general(1.0e21, 15) == "1e+21"
expect S2Format.general(0.30000000000000004, 15) == "0.3"
expect S2Format.general(100000000000000.5, 15) == "100000000000000"
expect S2Format.general(100000000000001.5, 15) == "100000000000002"
expect S2Format.general(0.0123456789, 15) == "0.0123456789"
expect S2Format.general(1.0e100, 15) == "1e+100"
expect S2Format.general(-1.5e-07, 15) == "-1.5e-07"
expect S2Format.general(F64.infinity, 15) == "inf"
expect S2Format.general(-F64.infinity, 15) == "-inf"
expect S2Format.general(9.999999999999999e-05, 15) == "0.0001"
expect S2Format.general(99999999999999.95, 15) == "100000000000000"
expect S2Format.general(999999999999999.4, 15) == "999999999999999"
expect S2Format.general(1.0e16, 15) == "1e+16"
expect S2Format.general(1.2345678901234567e19, 15) == "1.23456789012346e+19"
expect S2Format.general(2.2250738585072014e-308, 15) == "2.2250738585072e-308"
expect S2Format.general(0.1234567890123456, 15) == "0.123456789012346"
expect S2Format.general(0.1, 17) == "0.10000000000000001"
expect S2Format.general(37.7749, 17) == "37.774900000000002"
expect S2Format.general(1.0e-05, 17) == "1.0000000000000001e-05"
expect S2Format.general(0.0001234567, 6) == "0.000123457"
expect S2Format.general(123456789.0, 6) == "1.23457e+08"
expect S2Format.general(1.0e-05, 6) == "1e-05"
expect S2Format.general(F64.nan, 15) == "nan"

# `absl::SimpleAtod`, through tools/s2_oracle.cc.
expect S2Format.parse_double("12.5") == Ok(12.5)
expect S2Format.parse_double("-12.5") == Ok(-12.5)
expect S2Format.parse_double("+12.5") == Ok(12.5)
expect S2Format.parse_double("+-1") == Err(InvalidNumber)
expect S2Format.parse_double("-+1") == Err(InvalidNumber)
expect S2Format.parse_double("") == Err(InvalidNumber)
expect S2Format.parse_double("+") == Err(InvalidNumber)
expect S2Format.parse_double("-") == Err(InvalidNumber)
expect S2Format.parse_double(".") == Err(InvalidNumber)
expect S2Format.parse_double(".5") == Ok(0.5)
expect S2Format.parse_double("5.") == Ok(5.0)
expect S2Format.parse_double("-.5e1") == Ok(-5.0)
expect S2Format.parse_double("1e5") == Ok(100000.0)
expect S2Format.parse_double("1E5") == Ok(100000.0)
expect S2Format.parse_double("1e+5") == Ok(100000.0)
expect S2Format.parse_double("1e-5") == Ok(1.0000000000000001e-05)
expect S2Format.parse_double("1e") == Err(InvalidNumber)
expect S2Format.parse_double("1e+") == Err(InvalidNumber)
expect S2Format.parse_double("1ex") == Err(InvalidNumber)
expect S2Format.parse_double("1.5.5") == Err(InvalidNumber)
expect S2Format.parse_double("12 ") == Ok(12.0)
expect S2Format.parse_double("  12") == Ok(12.0)
expect S2Format.parse_double("	12\n") == Ok(12.0)
expect S2Format.parse_double("1 2") == Err(InvalidNumber)
expect S2Format.parse_double("inf") == Ok(F64.infinity)
expect S2Format.parse_double("-inf") == Ok(-F64.infinity)
expect S2Format.parse_double("+inf") == Ok(F64.infinity)
expect S2Format.parse_double("Infinity") == Ok(F64.infinity)
expect S2Format.parse_double("-INFINITY") == Ok(-F64.infinity)
expect S2Format.parse_double("infinit") == Err(InvalidNumber)
expect S2Format.parse_double("infx") == Err(InvalidNumber)
expect S2Format.parse_double("nan").map_ok(|x| x.is_nan()) == Ok(Bool.True)
expect S2Format.parse_double("NaN").map_ok(|x| x.is_nan()) == Ok(Bool.True)
expect S2Format.parse_double("nan(abc_1)").map_ok(|x| x.is_nan()) == Ok(Bool.True)
expect S2Format.parse_double("nan()").map_ok(|x| x.is_nan()) == Ok(Bool.True)
expect S2Format.parse_double("nan(a-b)") == Err(InvalidNumber)
expect S2Format.parse_double("nan(abc") == Err(InvalidNumber)
expect S2Format.parse_double("1e400") == Ok(F64.infinity)
expect S2Format.parse_double("-1e400") == Ok(-F64.infinity)
expect S2Format.parse_double("1e-400") == Ok(0.0)
expect S2Format.parse_double("-1e-400") == Ok(-0.0)
expect S2Format.parse_double("1e999999999999") == Ok(F64.infinity)
expect S2Format.parse_double("1e-999999999999") == Ok(0.0)
expect S2Format.parse_double("00012") == Ok(12.0)
expect S2Format.parse_double("0.0000000000000000000000000000001") == Ok(1.0000000000000001e-31)
expect S2Format.parse_double("123456789012345678901234567890") == Ok(1.2345678901234568e29)
expect S2Format.parse_double("4.9406564584124654e-324") == Ok(4.9406564584124654e-324)
expect S2Format.parse_double("1.7976931348623157e308") == Ok(1.7976931348623157e308)
expect S2Format.parse_double("1.7976931348623159e308") == Ok(F64.infinity)
expect S2Format.parse_double("0.1") == Ok(0.10000000000000001)
expect S2Format.parse_double("-0") == Ok(-0.0)
expect S2Format.parse_double("-0.0") == Ok(-0.0)
expect S2Format.parse_double("1,5") == Err(InvalidNumber)
expect S2Format.parse_double("--1") == Err(InvalidNumber)
expect S2Format.parse_double("1e5e5") == Err(InvalidNumber)
expect S2Format.parse_double("e5") == Err(InvalidNumber)
expect S2Format.parse_double("+.e1") == Err(InvalidNumber)
expect S2Format.parse_double("0x10") == Ok(16.0)
expect S2Format.parse_double("0x") == Err(InvalidNumber)
expect S2Format.parse_double("0x.8") == Ok(0.5)
expect S2Format.parse_double("0x1p3") == Ok(8.0)
expect S2Format.parse_double("0x1.8p3") == Ok(12.0)
expect S2Format.parse_double("0x1p") == Err(InvalidNumber)
expect S2Format.parse_double("-0x10") == Ok(-16.0)
expect S2Format.parse_double("0x1e5") == Ok(485.0)
expect S2Format.parse_double("0x1.8P-1") == Ok(0.75)
expect S2Format.parse_double("0X1F") == Ok(31.0)
expect S2Format.parse_double("0x.") == Err(InvalidNumber)
expect S2Format.parse_double("0xg") == Err(InvalidNumber)
expect S2Format.parse_double("0x1p+2") == Ok(4.0)
expect S2Format.parse_double("+0x10") == Ok(16.0)
expect S2Format.parse_double("0x1.") == Ok(1.0)
expect S2Format.parse_double("0x1pz") == Err(InvalidNumber)
expect S2Format.parse_double("0x1.8p3x") == Err(InvalidNumber)
expect S2Format.parse_double("0x1p99999999999") == Ok(F64.infinity)
expect S2Format.parse_double("0x1p-99999999999") == Ok(0.0)
expect S2Format.parse_double("0x0.0000000000001p-1022") == Ok(4.9406564584124654e-324)
expect S2Format.parse_double("0x1.fffffffffffff8p0") == Ok(2.0)
expect S2Format.parse_double("0x1.00000000000008p0") == Ok(1.0)
expect S2Format.parse_double("0x1.00000000000018p0") == Ok(1.0000000000000004)
expect S2Format.parse_double("0x123456789abcdef01p0") == Ok(2.0988295479420645e19)
expect S2Format.parse_double("0x.0000000000000000000000000001p120") == Ok(256.0)
expect S2Format.parse_double("0x0") == Ok(0.0)
expect S2Format.parse_double("0x0.0p5") == Ok(0.0)
expect S2Format.parse_double("0x00000000000000000000001") == Ok(1.0)
expect S2Format.parse_double("0x1.0000000000000000000000001p0") == Ok(1.0)
expect S2Format.parse_double("0x1.00000000000008000000001p0") == Ok(1.0000000000000002)
expect S2Format.parse_double("0x7fffffffffffffffp0") == Ok(9.2233720368547758e18)

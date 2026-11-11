## The byte-level coding that upstream's `Encoder` and `Decoder` do, which the
## `encode` and `decode` of the geometry types are built from: little-endian
## fixed-width integers, `double` values as their IEEE 754 bit patterns, and the
## variable-length integers of `util/coding/varint`.
##
## An encoder is a `List(U8)` that the `put_` functions append to. A decoder is
## a byte list and a position. Each `get_` function reads at a position and
## gives back the value, and the caller moves the position on by the size of
## the field. A read past the end of the bytes gives `Err(Truncated)` and never
## crashes.
##
## Internal to this package.
S2Coder := [].{

	## The list with one byte added at the end.
	put_u8 : List(U8), U8 -> List(U8)
	put_u8 = |out, value| out.append(value)

	## The list with the low 32 bits of `value` added as four bytes, least
	## significant first.
	put_u32 : List(U8), U64 -> List(U8)
	put_u32 = |out, value| put_le(out, value, 4)

	## The list with `value` added as eight bytes, least significant first.
	put_u64 : List(U8), U64 -> List(U8)
	put_u64 = |out, value| put_le(out, value, 8)

	## The list with the IEEE 754 bit pattern of `value` added as eight bytes,
	## least significant first.
	##
	## The builtin `to_bits` gives one bit pattern for every NaN, so a NaN with
	## another payload is written as the quiet NaN. Every other value, `-0.0`,
	## the infinities and the subnormal numbers included, keeps its bits.
	put_f64 : List(U8), F64 -> List(U8)
	put_f64 = |out, value| put_le(out, value.to_bits(), 8)

	## The list with `value` added as a varint: seven bits per byte, least
	## significant group first, and the top bit of a byte set when more bytes
	## follow. This is upstream's `put_varint64`, and `put_varint32` writes the
	## same bytes for a value below 2^32.
	put_varint64 : List(U8), U64 -> List(U8)
	put_varint64 = |out, value| {
		var $out = out
		var $rest = value
		while $rest >= 128 {
			$out = $out.append($rest.bitwise_and(127).bitwise_or(128).to_u8_wrap())
			$rest = $rest.shr_zf_wrap(7)
		}
		$out.append($rest.to_u8_wrap())
	}

	## The list with the low 32 bits of `value` added as a varint.
	put_varint32 : List(U8), U64 -> List(U8)
	put_varint32 = |out, value| put_varint64(out, value.bitwise_and(0xffffffff))

	## The bytes as lowercase hex, two digits for each byte. This is for the
	## expected values of tests, which are easier to read as hex.
	to_hex : List(U8) -> Str
	to_hex = |bytes|
		bytes.fold(
			"",
			|acc, byte|
				acc
					.concat(hex_digit(byte.shr_zf_wrap(4)))
					.concat(hex_digit(byte.bitwise_and(15))),
		)

	## The bytes of a hex string. A character that is not a hex digit counts as
	## the digit 0, and a last single digit is dropped.
	from_hex : Str -> List(U8)
	from_hex = |text| {
		chars = text.to_utf8()
		var $out = []
		for i in 0..<(chars.len() // 2) {
			high = hex_value(chars.get(2 * i) ?? 48)
			low = hex_value(chars.get(2 * i + 1) ?? 48)
			$out = $out.append(high.shl_wrap(4).bitwise_or(low))
		}
		$out
	}

	## True when `count` bytes can be read at `pos`.
	can_read : List(U8), U64, U64 -> Bool
	can_read = |bytes, pos, count| pos <= bytes.len() and count <= bytes.len() - pos

	## The byte at `pos`.
	get_u8 : List(U8), U64 -> Try(U8, [Truncated])
	get_u8 = |bytes, pos| bytes.get(pos).map_err(|_| Truncated)

	## The four bytes at `pos` as an unsigned integer, least significant first.
	get_u32 : List(U8), U64 -> Try(U64, [Truncated])
	get_u32 = |bytes, pos| get_le(bytes, pos, 4)

	## The eight bytes at `pos` as an unsigned integer, least significant first.
	get_u64 : List(U8), U64 -> Try(U64, [Truncated])
	get_u64 = |bytes, pos| get_le(bytes, pos, 8)

	## The eight bytes at `pos` as the bit pattern of an `F64`. Any NaN payload
	## is kept.
	get_f64 : List(U8), U64 -> Try(F64, [Truncated])
	get_f64 = |bytes, pos| get_le(bytes, pos, 8).map_ok(F64.from_bits)

	## The varint at `pos` and the position after it. A varint of more than
	## ten bytes, or a tenth byte above 1, is `BadVarint`, as for upstream's
	## `get_varint64`.
	get_varint64 : List(U8), U64 -> Try((U64, U64), [Truncated, BadVarint])
	get_varint64 = |bytes, pos| get_varint(bytes, pos, 10, 2)

	## Like `get_varint64`, for a value of 32 bits: of more than five bytes, or
	## a fifth byte above 15, is `BadVarint`.
	get_varint32 : List(U8), U64 -> Try((U64, U64), [Truncated, BadVarint])
	get_varint32 = |bytes, pos| get_varint(bytes, pos, 5, 16)
}

hex_digit : U8 -> Str
hex_digit = |n| match n {
	0 => "0"
	1 => "1"
	2 => "2"
	3 => "3"
	4 => "4"
	5 => "5"
	6 => "6"
	7 => "7"
	8 => "8"
	9 => "9"
	10 => "a"
	11 => "b"
	12 => "c"
	13 => "d"
	14 => "e"
	_ => "f"
}

hex_value : U8 -> U8
hex_value = |c| if c >= 97 and c <= 102 {
	c - 87
} else if c >= 65 and c <= 70 {
	c - 55
} else if c >= 48 and c <= 57 {
	c - 48
} else {
	0
}

put_le : List(U8), U64, U64 -> List(U8)
put_le = |out, value, width| {
	var $out = out
	var $i = 0
	while $i < width {
		$out = $out.append(value.shr_zf_wrap(($i * 8).to_u8_wrap()).bitwise_and(255).to_u8_wrap())
		$i = $i + 1
	}
	$out
}

get_le : List(U8), U64, U64 -> Try(U64, [Truncated])
get_le = |bytes, pos, width| {
	if !S2Coder.can_read(bytes, pos, width) {
		return Err(Truncated)
	}
	var $value = 0
	var $i = width
	while $i > 0 {
		$i = $i - 1
		byte = bytes.get(pos + $i) ?? 0
		$value = $value.shl_wrap(8).bitwise_or(byte.to_u64())
	}
	Ok($value)
}

## The groups of a varint of at most `max_bytes` bytes, where the last byte
## must be below `last_limit`.
get_varint : List(U8), U64, U64, U8 -> Try((U64, U64), [Truncated, BadVarint])
get_varint = |bytes, pos, max_bytes, last_limit| {
	var $value = 0
	var $i = 0
	while $i < max_bytes {
		byte = bytes.get(pos + $i) ?? 0
		if !S2Coder.can_read(bytes, pos + $i, 1) {
			return Err(Truncated)
		}
		$value = $value.bitwise_or(byte.to_u64().bitwise_and(127).shl_wrap(($i * 7).to_u8_wrap()))
		if byte < 128 {
			if $i + 1 == max_bytes and byte >= last_limit {
				return Err(BadVarint)
			}
			return Ok(($value, pos + $i + 1))
		}
		$i = $i + 1
	}
	Err(BadVarint)
}

# The expected bytes below are upstream's `Encoder`, from the oracle.
expect S2Coder.put_u8([], 171) == [171]
expect S2Coder.put_u32([], 305419896) == [0x78, 0x56, 0x34, 0x12]
expect S2Coder.put_u32([], 0x1ffffffff) == [255, 255, 255, 255]
expect S2Coder.put_u64([], 18446744073709551615) == [255, 255, 255, 255, 255, 255, 255, 255]
expect S2Coder.put_u64([7], 0x0102030405060708) == [7, 8, 7, 6, 5, 4, 3, 2, 1]
expect S2Coder.put_f64([], -0.0) == [0, 0, 0, 0, 0, 0, 0, 0x80]
expect S2Coder.put_f64([], 0.0) == [0, 0, 0, 0, 0, 0, 0, 0]
expect S2Coder.put_f64([], F64.infinity) == [0, 0, 0, 0, 0, 0, 0xf0, 0x7f]
expect S2Coder.put_f64([], -F64.infinity) == [0, 0, 0, 0, 0, 0, 0xf0, 0xff]
expect S2Coder.put_f64([], 4.9406564584124654e-324) == [1, 0, 0, 0, 0, 0, 0, 0]
expect S2Coder.put_f64([], 1.7976931348623157e308) == [255, 255, 255, 255, 255, 255, 0xef, 0x7f]
expect S2Coder.put_f64([], 1.0) == [0, 0, 0, 0, 0, 0, 0xf0, 0x3f]
expect S2Coder.put_f64([], F64.nan) == [0, 0, 0, 0, 0, 0, 0xf8, 0x7f]

expect S2Coder.get_u8([5, 6], 1) == Ok(6)
expect S2Coder.get_u8([5, 6], 2) == Err(Truncated)
expect S2Coder.get_u32([0x78, 0x56, 0x34, 0x12], 0) == Ok(305419896)
expect S2Coder.get_u32([0, 0x78, 0x56, 0x34, 0x12], 1) == Ok(305419896)
expect S2Coder.get_u32([0x78, 0x56, 0x34], 0) == Err(Truncated)
expect S2Coder.get_u32([0x78, 0x56, 0x34, 0x12], 1) == Err(Truncated)
expect S2Coder.get_u32([], 0) == Err(Truncated)
expect S2Coder.get_u64([255, 255, 255, 255, 255, 255, 255, 255], 0) == Ok(18446744073709551615)
expect S2Coder.get_u64([8, 7, 6, 5, 4, 3, 2, 1], 0) == Ok(0x0102030405060708)
expect S2Coder.get_u64([8, 7, 6, 5, 4, 3, 2, 1], 1) == Err(Truncated)
expect S2Coder.get_u64([8, 7, 6, 5, 4, 3, 2, 1], 18446744073709551615) == Err(Truncated)
expect S2Coder.get_f64([0, 0, 0, 0, 0, 0, 0xf0, 0x3f], 0) == Ok(1.0)
expect S2Coder.get_f64([0, 0, 0, 0, 0, 0, 0xf0, 0x3f], 1) == Err(Truncated)

# The bit patterns survive a round trip, the sign of zero and the subnormal
# numbers included. A NaN with a payload stays a NaN.
expect S2Coder.get_f64(S2Coder.put_f64([], -0.0), 0).map_ok(F64.to_bits) == Ok(F64.to_bits(-0.0))
expect S2Coder.get_f64(S2Coder.put_f64([], -0.0), 0).map_ok(F64.to_bits) != Ok(F64.to_bits(0.0))
expect S2Coder.get_f64(S2Coder.put_f64([], 4.9406564584124654e-324), 0) == Ok(4.9406564584124654e-324)
expect S2Coder.get_f64(S2Coder.put_f64([], 2.2250738585072009e-308), 0) == Ok(2.2250738585072009e-308)
expect S2Coder.get_f64(S2Coder.put_f64([], -F64.infinity), 0) == Ok(-F64.infinity)
expect S2Coder.get_f64(S2Coder.put_f64([], 0.1), 0) == Ok(0.1)
expect S2Coder.get_f64([1, 0, 0, 0, 0, 0, 0xf8, 0x7f], 0).map_ok(|x| x.is_nan()) == Ok(Bool.True)
expect S2Coder.get_f64([0, 0, 0, 0, 0, 0, 0xf8, 0x7f], 0).map_ok(|x| x.is_nan()) == Ok(Bool.True)
expect S2Coder.get_f64([0, 0, 0, 0, 0, 0, 0xf0, 0xff], 0) == Ok(-F64.infinity)

# Varints, against upstream's `put_varint32` and `put_varint64`.
expect S2Coder.put_varint32([], 0) == [0x00]
expect S2Coder.put_varint32([], 1) == [0x01]
expect S2Coder.put_varint32([], 127) == [0x7f]
expect S2Coder.put_varint32([], 128) == [0x80, 0x01]
expect S2Coder.put_varint32([], 255) == [0xff, 0x01]
expect S2Coder.put_varint32([], 300) == [0xac, 0x02]
expect S2Coder.put_varint32([], 16383) == [0xff, 0x7f]
expect S2Coder.put_varint32([], 16384) == [0x80, 0x80, 0x01]
expect S2Coder.put_varint32([], 2097151) == [0xff, 0xff, 0x7f]
expect S2Coder.put_varint32([], 2097152) == [0x80, 0x80, 0x80, 0x01]
expect S2Coder.put_varint32([], 268435455) == [0xff, 0xff, 0xff, 0x7f]
expect S2Coder.put_varint32([], 268435456) == [0x80, 0x80, 0x80, 0x80, 0x01]
expect S2Coder.put_varint32([], 4294967295) == [0xff, 0xff, 0xff, 0xff, 0x0f]
expect S2Coder.put_varint32([9], 300) == [9, 0xac, 0x02]
expect S2Coder.put_varint64([], 0) == [0x00]
expect S2Coder.put_varint64([], 127) == [0x7f]
expect S2Coder.put_varint64([], 128) == [0x80, 0x01]
expect S2Coder.put_varint64([], 268435456) == [0x80, 0x80, 0x80, 0x80, 0x01]
expect S2Coder.put_varint64([], 34359738367) == [0xff, 0xff, 0xff, 0xff, 0x7f]
expect S2Coder.put_varint64([], 34359738368) == [0x80, 0x80, 0x80, 0x80, 0x80, 0x01]
expect S2Coder.put_varint64([], 4398046511103) == [0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
expect S2Coder.put_varint64([], 281474976710656) == [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x40]
expect S2Coder.put_varint64([], 72057594037927936) == [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01]
expect S2Coder.put_varint64([], 9223372036854775808)
	== [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01]
expect S2Coder.put_varint64([], 18446744073709551615)
	== [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01]

# Varint decoding: the value and the position after it. Upstream accepts a
# varint that is longer than needed, such as `8000`, and refuses a fifth byte
# above 15 (32 bits) or a tenth byte above 1 (64 bits).
expect S2Coder.get_varint32([0x00], 0) == Ok((0, 1))
expect S2Coder.get_varint32([0x80, 0x00], 0) == Ok((0, 2))
expect S2Coder.get_varint32([0xac, 0x02], 0) == Ok((300, 2))
expect S2Coder.get_varint32([0xac, 0x02, 0xff], 0) == Ok((300, 2))
expect S2Coder.get_varint32([7, 0xac, 0x02], 1) == Ok((300, 3))
expect S2Coder.get_varint32([0xff, 0xff, 0xff, 0xff, 0x0f], 0) == Ok((4294967295, 5))
expect S2Coder.get_varint32([0xff, 0xff, 0xff, 0xff, 0x10], 0) == Err(BadVarint)
expect S2Coder.get_varint32([0xff, 0xff, 0xff, 0xff, 0xff], 0) == Err(BadVarint)
expect S2Coder.get_varint32([0xff, 0xff, 0xff, 0xff, 0x8f, 0x01], 0) == Err(BadVarint)
expect S2Coder.get_varint32([0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0) == Err(BadVarint)
expect S2Coder.get_varint32([0x80], 0) == Err(Truncated)
expect S2Coder.get_varint32([0xac], 0) == Err(Truncated)
expect S2Coder.get_varint32([], 0) == Err(Truncated)
expect S2Coder.get_varint32([0xac, 0x02], 2) == Err(Truncated)
expect S2Coder.get_varint64([0xac, 0x02], 0) == Ok((300, 2))
expect S2Coder.get_varint64([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], 0)
	== Ok((18446744073709551615, 10))
expect S2Coder.get_varint64([0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01], 0)
	== Ok((9223372036854775808, 10))
expect S2Coder.get_varint64([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02], 0) == Err(BadVarint)
expect S2Coder.get_varint64([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81], 0) == Err(BadVarint)
expect S2Coder.get_varint64([0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0)
	== Err(BadVarint)
expect S2Coder.get_varint64([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], 0) == Err(Truncated)
expect S2Coder.get_varint64([], 0) == Err(Truncated)

# Writing then reading gives the value back, at every width.
expect S2Coder.get_varint64(S2Coder.put_varint64([], 123456789012345), 0)
	== Ok((123456789012345, S2Coder.put_varint64([], 123456789012345).len()))
expect S2Coder.get_varint32(S2Coder.put_varint32([], 4000000000), 0) == Ok((4000000000, 5))

expect S2Coder.can_read([1, 2, 3], 0, 3)
expect S2Coder.can_read([1, 2, 3], 3, 0)
expect !S2Coder.can_read([1, 2, 3], 3, 1)
expect !S2Coder.can_read([1, 2, 3], 4, 0)
expect !S2Coder.can_read([1, 2, 3], 1, 18446744073709551615)

expect S2Coder.to_hex([0, 1, 171, 255]) == "0001abff"
expect S2Coder.to_hex([]) == ""
expect S2Coder.from_hex("0001abFF") == [0, 1, 171, 255]
expect S2Coder.from_hex("abc") == [171]
expect S2Coder.from_hex("") == []

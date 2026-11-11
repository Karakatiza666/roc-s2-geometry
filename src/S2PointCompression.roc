import S2Coords
import S2Point
import Internal/S2Coder

## The compressed encoding of a list of points that are mostly the centres of
## cells at one level, which the compressed formats of `S2Polyline` and
## `S2Polygon` use. Upstream's `s2point_compression.h`.
##
## A point at the centre of a cell at the given level is written as the
## position of that cell on its face. The faces are run-length encoded. The
## positions are written as their second differences, which are small for a
## chain of nearby points, as varints with the two coordinates' bits
## interleaved. Every other point is written in full after them, with its
## index, so the encoding is lossless. Leaf cells take about 4 bytes per point
## after the first.
S2PointCompression := [].{

	## A point with its face, its `(si, ti)` coordinates, and the level of
	## the cell whose centre it is, as `S2Coords.xyz_to_face_si_ti` gives
	## them. Upstream's `S2XYZFaceSiTi`.
	S2XYZFaceSiTi : { xyz : S2Point, face : U64, si : U64, ti : U64, cell_level : Try(U64, [NotCellCenter]) }

	## The point in the form that `encode_points_compressed` takes.
	xyz_face_si_ti : S2Point -> S2XYZFaceSiTi
	xyz_face_si_ti = |p| {
		parts = S2Coords.xyz_to_face_si_ti(p)
		{ xyz: p, face: parts.face, si: parts.si, ti: parts.ti, cell_level: parts.level }
	}

	## The bytes that upstream's `S2EncodePointsCompressed` writes for the
	## points, with `level` as the level of the cells whose centres are
	## written in the short form. `level` must be at most 30.
	##
	## The bytes are the face runs, each as the varint `6 * count + face`;
	## the first point in `2 * ceil(level / 8)` bytes; each other point as a
	## varint; the number of points that are not centres of cells at `level`
	## as a varint; and then each of those as its index and its three
	## coordinates.
	encode_points_compressed : List(S2XYZFaceSiTi), U64 -> List(U8)
	encode_points_compressed = |points, level| {
		var $out = []
		for (face, count) in face_runs(points) {
			$out = S2Coder.put_varint64($out, 6 * count + face)
		}
		var $pi_coder = new_coder()
		var $qi_coder = new_coder()
		var $index = 0.U64
		var $off_center = []
		for p in points {
			(pi_coder, pi) = encode_step($pi_coder, si_ti_to_pi_qi(p.si, level))
			(qi_coder, qi) = encode_step($qi_coder, si_ti_to_pi_qi(p.ti, level))
			$pi_coder = pi_coder
			$qi_coder = qi_coder
			if $index == 0 {
				# The first point is not a difference and cannot be negative,
				# so it is written in a fixed width rather than as a varint.
				interleaved = interleave(pi, qi)
				width = (level + 7) // 8 * 2
				for k in 0..<width {
					$out = $out.append(interleaved.shr_zf_wrap((8 * k).to_u8_wrap()).bitwise_and(255).to_u8_wrap())
				}
			} else {
				$out = S2Coder.put_varint64($out, interleave(zig_zag(pi), zig_zag(qi)))
			}
			if p.cell_level != Ok(level) {
				$off_center = $off_center.append(($index, p.xyz))
			}
			$index = $index + 1
		}
		$out = S2Coder.put_varint32($out, $off_center.len())
		for (index, xyz) in $off_center {
			$out = S2Coder.put_varint32($out, index)
			$out = $out.concat(xyz.encode())
		}
		$out
	}

	## The `count` points that `encode_points_compressed` wrote with the same
	## `level`, read from the start of `bytes`, and the number of bytes they
	## take. Upstream's `S2DecodePointsCompressed`. Bytes after the points
	## are ignored.
	##
	## A point written in the short form is decoded as the centre of its cell.
	## Bytes that end too soon are `Truncated`, and a varint that is too long
	## is `BadVarint`. A face run of no points or of `2^31` or more, more
	## points written in full than `count`, and an index of such a point that
	## is not below `count` are `InvalidEncoding`, as upstream refuses them.
	decode_points_compressed : List(U8), U64, U64 -> Try({ points : List(S2Point), size : U64 }, [Truncated, BadVarint, InvalidEncoding])
	decode_points_compressed = |bytes, count, level| {
		var $pos = 0
		var $runs = []
		var $parsed = 0.U64
		while $parsed < count {
			(face_and_count, next) = S2Coder.get_varint64(bytes, $pos)?
			$pos = next
			run = face_and_count // 6
			if run == 0 or run > 2147483647 {
				return Err(InvalidEncoding)
			}
			$runs = $runs.append((face_and_count % 6, run))
			$parsed = $parsed + run
		}

		var $points = []
		var $pi_coder = new_coder()
		var $qi_coder = new_coder()
		var $run_index = 0.U64
		var $used = 0.U64
		for i in 0..<count {
			(pi_raw, qi_raw) =
				if i == 0 {
					width = (level + 7) // 8 * 2
					if !S2Coder.can_read(bytes, $pos, width) {
						return Err(Truncated)
					}
					var $value = 0.U64
					for k in 0..<width {
						byte = bytes.get($pos + k) ?? 0
						$value = $value.bitwise_or(byte.to_u64().shl_wrap((8 * k).to_u8_wrap()))
					}
					$pos = $pos + width
					deinterleave($value)
				} else {
					(value, next) = S2Coder.get_varint64(bytes, $pos)?
					$pos = next
					(pi_zz, qi_zz) = deinterleave(value)
					(zig_zag_decode(pi_zz), zig_zag_decode(qi_zz))
				}
			(pi_coder, pi) = decode_step($pi_coder, pi_raw)
			(qi_coder, qi) = decode_step($qi_coder, qi_raw)
			$pi_coder = pi_coder
			$qi_coder = qi_coder
			# The next face from the runs.
			if $used == (($runs.get($run_index) ?? (0, 0)).1) {
				$run_index = $run_index + 1
				$used = 0
			}
			$used = $used + 1
			face = ($runs.get($run_index) ?? (0, 0)).0
			$points = $points.append(face_pi_qi_to_xyz(face, pi, qi, level))
		}

		(num_off_center, after_count) = S2Coder.get_varint32(bytes, $pos)?
		$pos = after_count
		if num_off_center > count {
			return Err(InvalidEncoding)
		}
		for _ in 0..<num_off_center {
			(index, after_index) = S2Coder.get_varint32(bytes, $pos)?
			$pos = after_index
			if index >= count {
				return Err(InvalidEncoding)
			}
			if !S2Coder.can_read(bytes, $pos, 24) {
				return Err(Truncated)
			}
			xyz = S2Point.decode(bytes.drop_first($pos))?
			$pos = $pos + 24
			$points = $points.set(index, xyz) ?? $points
		}
		Ok({ points: $points, size: $pos })
	}
}

## The runs of equal faces in the list, as `(face, count)` pairs.
face_runs : List(S2PointCompression.S2XYZFaceSiTi) -> List((U64, U64))
face_runs = |points|
	points.fold(
		[],
		|runs, p| match runs.last() {
			Ok((face, count)) if face == p.face => runs.set(runs.len() - 1, (face, count + 1)) ?? runs
			_ => runs.append((p.face, 1))
		},
	)

## The position of the cell at `level` along one axis, from the `si` or `ti`
## coordinate of a point: the coordinate with the bits below the level
## dropped. `si = 2^31` is not a cell centre, so it is first clamped to the
## largest position.
si_ti_to_pi_qi : U64, U64 -> U32
si_ti_to_pi_qi = |si, level| si.min(2147483647).shr_zf_wrap((31 - level).to_u8_wrap()).to_u32_wrap()

## The centre of the cell at `level` with the positions `pi` and `qi` on
## `face`, which are signed integers in two's complement.
face_pi_qi_to_xyz : U64, U32, U32, U64 -> S2Point
face_pi_qi_to_xyz = |face, pi, qi, level| {
	cells = (1.U64).shl_wrap(level.to_u8_wrap()).to_f64()
	s = (pi.to_i32_wrap().to_f64() + 0.5) / cells
	t = (qi.to_i32_wrap().to_f64() + 0.5) / cells
	S2Coords.face_uv_to_xyz(face, S2Coords.st_to_uv(s), S2Coords.st_to_uv(t)).normalize()
}

## The state of upstream's `NthDerivativeCoder` of order 2: how many values it
## has seen, up to 2, and the last value of the sequence and of its first
## difference. The arithmetic wraps, as on 32-bit integers.
Coder : { seen : U64, m0 : U32, m1 : U32 }

new_coder : () -> Coder
new_coder = || { seen: 0, m0: 0, m1: 0 }

## The next value to write for `k`: `k` itself, then its first difference,
## then its second differences.
encode_step : Coder, U32 -> (Coder, U32)
encode_step = |coder, k|
	if coder.seen == 0 {
		({ seen: 1, m0: k, m1: 0 }, k)
	} else if coder.seen == 1 {
		d1 = k.minus_wrap(coder.m0)
		({ seen: 2, m0: k, m1: d1 }, d1)
	} else {
		d1 = k.minus_wrap(coder.m0)
		d2 = d1.minus_wrap(coder.m1)
		({ seen: 2, m0: k, m1: d1 }, d2)
	}

## The value of the sequence for the written value `k`, undoing
## `encode_step`.
decode_step : Coder, U32 -> (Coder, U32)
decode_step = |coder, k|
	if coder.seen == 0 {
		({ seen: 1, m0: k, m1: 0 }, k)
	} else if coder.seen == 1 {
		m0 = coder.m0.plus_wrap(k)
		({ seen: 2, m0: m0, m1: k }, m0)
	} else {
		m1 = coder.m1.plus_wrap(k)
		m0 = coder.m0.plus_wrap(m1)
		({ seen: 2, m0: m0, m1: m1 }, m0)
	}

## The zig-zag code of a signed 32-bit integer given as its bits: 0, -1, 1,
## -2, ... become 0, 1, 2, 3, ..., so that small values of either sign make
## short varints.
zig_zag : U32 -> U32
zig_zag = |n| {
	sign = if (n.shr_zf_wrap(31) == 1) 0xffffffff else 0
	n.shl_wrap(1).bitwise_xor(sign)
}

## The inverse of `zig_zag`.
zig_zag_decode : U32 -> U32
zig_zag_decode = |n| {
	sign = if (n.bitwise_and(1) == 1) 0xffffffff else 0
	n.shr_zf_wrap(1).bitwise_xor(sign)
}

## The bits of `a` in the even positions and the bits of `b` in the odd
## positions of one 64-bit integer.
interleave : U32, U32 -> U64
interleave = |a, b| {
	var $out = 0.U64
	for i in 0..<32.U64 {
		shift = i.to_u8_wrap()
		bit_a = a.to_u64().shr_zf_wrap(shift).bitwise_and(1)
		bit_b = b.to_u64().shr_zf_wrap(shift).bitwise_and(1)
		$out = $out.bitwise_or(bit_a.shl_wrap(2 * shift)).bitwise_or(bit_b.shl_wrap(2 * shift + 1))
	}
	$out
}

## The two integers that `interleave` combined.
deinterleave : U64 -> (U32, U32)
deinterleave = |v| {
	var $a = 0.U64
	var $b = 0.U64
	for i in 0..<32.U64 {
		shift = i.to_u8_wrap()
		$a = $a.bitwise_or(v.shr_zf_wrap(2 * shift).bitwise_and(1).shl_wrap(shift))
		$b = $b.bitwise_or(v.shr_zf_wrap(2 * shift + 1).bitwise_and(1).shl_wrap(shift))
	}
	($a.to_u32_wrap(), $b.to_u32_wrap())
}

# The values below were printed by upstream's S2EncodePointsCompressed and
# S2DecodePointsCompressed at v0.14.0 through tools/s2_oracle.cc. The cases
# are fixtures of upstream's S2PointCompressionTest; tests/CodingCorpus.roc
# holds the others.
expect S2PointCompression.xyz_face_si_ti(S2Point.new(0.054299323861222645, -0.70606358900180299, 0.70606358900180299))
	== {
		xyz: S2Point.new(0.054299323861222645, -0.70606358900180299, 0.70606358900180299),
		face: 2,
		si: 956301312,
		ti: 2147483648,
		cell_level: Err(NotCellCenter),
	}
expect S2PointCompression.xyz_face_si_ti(S2Point.new(0.056482651436986935, -0.70781701406865505, 0.70413406726388494)).cell_level == Ok(8)

# RoundtripsEmpty: only the count of points written in full.
expect S2PointCompression.encode_points_compressed([], 30) == [0]
expect S2PointCompression.decode_points_compressed([0], 0, 30) == Ok({ points: [], size: 1 })
expect S2PointCompression.decode_points_compressed([], 0, 30) == Err(Truncated)

# FourVertexLoopSize: four points snapped to level 30 take 39 bytes.
expect {
	points = [
		S2Point.new(0.57734393300693709, 0.57736308472952325, 0.57734378961905419),
		S2Point.new(0.57733912906337814, 0.5773503520180171, 0.57736132627412085),
		S2Point.new(0.57735660468139538, 0.57733745388770297, 0.57735674878642884),
		S2Point.new(0.5773614094408831, 0.57735018568768981, 0.57733921222694307),
	]
	hex = "070e06fa2c9aa5aaaaaa0aca86a99ca2d5aad52adddb8186acd5aad52ac08f92fa8ad5aad56a00"
	encoded = S2PointCompression.encode_points_compressed(points.map(S2PointCompression.xyz_face_si_ti), 30)
	S2Coder.to_hex(encoded) == hex
		and S2PointCompression.decode_points_compressed(S2Coder.from_hex(hex), 4, 30) == Ok({ points: points, size: 39 })
}

# FirstPointOnFaceEdge: the first point has ti = 2^31, which is clamped, and
# it is not a cell centre, so it is written in full.
expect {
	points = [
		S2Point.new(0.054299323861222645, -0.70606358900180299, 0.70606358900180299),
		S2Point.new(0.056482651436986935, -0.70781701406865505, 0.70413406726388494),
	]
	hex = "080aaebf87f803010006945bf81ecdab3f9617f5aa1298e6bf9617f5aa1298e63f"
	encoded = S2PointCompression.encode_points_compressed(points.map(S2PointCompression.xyz_face_si_ti), 8)
	S2Coder.to_hex(encoded) == hex
		and S2PointCompression.decode_points_compressed(S2Coder.from_hex(hex), 2, 8) == Ok({ points: points, size: 33 })
}

# A face run of no points, and an index of a point written in full that is
# not below the count, are refused.
expect S2PointCompression.decode_points_compressed(S2Coder.from_hex("000000"), 1, 0) == Err(InvalidEncoding)
expect S2PointCompression.decode_points_compressed(S2Coder.from_hex("060101000000000000000000000000000000000000000000000000"), 1, 0) == Err(InvalidEncoding)

import s2.R1Interval
import s2.S1ChordAngle
import s2.S1Interval
import s2.S2Cap
import s2.S2Cell
import s2.S2CellId
import s2.S2CellUnion
import s2.S2LatLng
import s2.S2LatLngRect
import s2.S2Loop
import s2.S2Point
import s2.S2PointRegion
import s2.S2Polygon
import s2.S2Polyline
import CodingCorpus

## Checks the binary encodings against the bytes that upstream's `Encode`
## writes, and the decoders against what upstream's `Decode` accepts.
##
## `CodingCorpus` carries the bytes as hex, with the numbers they hold. For each
## type the value is built from those numbers, and its `encode` must give the
## same bytes, and `decode` of the bytes must give the same value back. Then
## the bytes that are not a plain encoding go through `decode` and `encode`
## again, and must match what upstream gives. Last, every truncation of one
## sample of each type must be refused.
S2CodingTest := [].{

	digits : List(Str)
	digits = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"]

	## The bytes as lowercase hex, or `-` for no bytes.
	hex_of : List(U8) -> Str
	hex_of = |bytes| if bytes.is_empty() {
		"-"
	} else {
		bytes.fold(
			"",
			|acc, byte| acc
				.concat(S2CodingTest.digits.get(byte.shr_zf_wrap(4).to_u64()) ?? "?")
				.concat(S2CodingTest.digits.get(byte.bitwise_and(15).to_u64()) ?? "?"),
		)
	}

	nibble : U8 -> U8
	nibble = |c| if (c >= 97) c - 87 else c - 48

	## The bytes of a hex string, where `-` stands for no bytes.
	bytes_of : Str -> List(U8)
	bytes_of = |hex| {
		chars = hex.to_utf8()
		var $out = []
		if hex != "-" {
			for i in 0..<(chars.len() // 2) {
				high = S2CodingTest.nibble(chars.get(2 * i) ?? 48)
				low = S2CodingTest.nibble(chars.get(2 * i + 1) ?? 48)
				$out = $out.append(high.shl_wrap(4).bitwise_or(low))
			}
		}
		$out
	}

	## The loop through the vertices, with the bound that upstream computed.
	##
	## The port computes a bound too, and it is close to upstream's but can
	## differ in the last digit, because the port's `atan2` is not the C
	## library's. `bound_is_close` checks that. A loop built here carries
	## upstream's bound, so that the bytes can be compared exactly.
	loop_of : List((F64, F64, F64)), (F64, F64, F64, F64) -> S2Loop
	loop_of = |vertices, (lat_lo, lat_hi, lng_lo, lng_hi)| {
		built = S2Loop.from_points(vertices.map(S2CodingTest.point_of))
		{
			vertices: built.vertices(),
			origin_inside: built.origin_inside,
			bound: S2LatLngRect.new(R1Interval.new(lat_lo, lat_hi), S1Interval.new(lng_lo, lng_hi)),
		}
	}

	## True when the bound of the loop that the port computes is within 1e-14 of
	## the bound upstream computed.
	bound_is_close : List((F64, F64, F64)), (F64, F64, F64, F64) -> Bool
	bound_is_close = |vertices, (lat_lo, lat_hi, lng_lo, lng_hi)| {
		bound = S2Loop.from_points(vertices.map(S2CodingTest.point_of)).rect_bound()
		close = |a, b| (a - b).abs() < 1e-14
		close(bound.lat().lo(), lat_lo)
			and close(bound.lat().hi(), lat_hi)
			and close(bound.lng().lo(), lng_lo)
			and close(bound.lng().hi(), lng_hi)
	}

	point_of : (F64, F64, F64) -> S2Point
	point_of = |(x, y, z)| S2Point.new(x, y, z)

	## The number of cases for which the check fails.
	failures : List(a), (a -> Bool) -> U64
	failures = |cases, check| cases.fold(0, |acc, case| if (check(case)) acc else acc + 1)

	## The encoding is the bytes, and decoding them gives the value back.
	round_trips : Str, a, (a -> List(U8)), (List(U8) -> Try(a, _)) -> Bool where [a.is_eq : a, a -> Bool]
	round_trips = |hex, value, encode, decode|
		S2CodingTest.hex_of(encode(value)) == hex and decode(S2CodingTest.bytes_of(hex)) == Ok(value)

	## What `decode` and `encode` make of the bytes, with the error shown.
	decoded : Str, List(U8) -> Try(Str, Str)
	decoded = |kind, bytes| match kind {
		"point" => S2Point.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"latlng" => S2LatLng.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"cap" => S2Cap.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"rect" => S2LatLngRect.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"cellid" => S2CellId.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"cell" => S2Cell.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"union" => S2CellUnion.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"pointregion" => S2PointRegion.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"loop" => S2Loop.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"line" => S2Polyline.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		"poly" => S2Polygon.decode(bytes).map_ok(|v| S2CodingTest.hex_of(v.encode())).map_err(Str.inspect)
		_ => Err("unknown kind")
	}

	## True when `decode` and `encode` agree with upstream's verdict.
	verdict_holds : { kind : Str, name : Str, hex : Str, verdict : Str } -> Bool
	verdict_holds = |case| match S2CodingTest.decoded(case.kind, S2CodingTest.bytes_of(case.hex)) {
		Ok(hex) => hex == case.verdict
		Err(error) => if case.verdict == "-" {
			Bool.True
		} else if case.verdict == "compressed" {
			error == "UnsupportedCompressedEncoding"
		} else if case.verdict == "invalid" {
			error == "InvalidCellId"
		} else {
			Bool.False
		}
	}

	## True when every proper prefix of the bytes is refused.
	truncations_refused : { kind : Str, hex : Str } -> Bool
	truncations_refused = |case| {
		bytes = S2CodingTest.bytes_of(case.hex)
		var $refused = Bool.True
		for n in 0..<bytes.len() {
			if S2CodingTest.decoded(case.kind, bytes.sublist({ start: 0, len: n })).is_ok() {
				$refused = Bool.False
			}
		}
		$refused
	}
}

expect S2CodingTest.hex_of([0, 1, 171, 255]) == "0001abff"
expect S2CodingTest.hex_of([]) == "-"
expect S2CodingTest.bytes_of("0001abff") == [0, 1, 171, 255]
expect S2CodingTest.bytes_of("-") == []

expect S2CodingTest.failures(
	CodingCorpus.points,
	|c| S2CodingTest.round_trips(c.hex, S2CodingTest.point_of(c.xyz), S2Point.encode, S2Point.decode),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.latlngs,
	|c| S2CodingTest.round_trips(c.hex, S2LatLng.from_radians(c.lat, c.lng), S2LatLng.encode, S2LatLng.decode),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.caps,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2Cap.from_center_chord_angle(S2CodingTest.point_of(c.center), S1ChordAngle.from_length2(c.length2)),
		S2Cap.encode,
		S2Cap.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.rects,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2LatLngRect.new(R1Interval.new(c.lat_lo, c.lat_hi), S1Interval.new(c.lng_lo, c.lng_hi)),
		S2LatLngRect.encode,
		S2LatLngRect.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.cell_ids,
	|c| S2CodingTest.round_trips(c.hex, S2CellId.from_id(c.id), S2CellId.encode, S2CellId.decode),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.cells,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2Cell.from_cell_id(S2CellId.from_id(c.id)),
		S2Cell.encode,
		S2Cell.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.unions,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2CellUnion.from_verbatim(c.ids.map(S2CellId.from_id)),
		S2CellUnion.encode,
		S2CellUnion.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.point_regions,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2PointRegion.new(S2CodingTest.point_of(c.xyz)),
		S2PointRegion.encode,
		S2PointRegion.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.loops,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2CodingTest.loop_of(c.vertices, c.bound),
		S2Loop.encode,
		S2Loop.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.loops,
	|c| S2CodingTest.bound_is_close(c.vertices, c.bound),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.lines,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2Polyline.from_points(c.vertices.map(S2CodingTest.point_of)),
		S2Polyline.encode,
		S2Polyline.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.polygons,
	|c| S2CodingTest.round_trips(
		c.hex,
		S2Polygon.from_loops(c.loops.map(|l| S2CodingTest.loop_of(l.vertices, l.bound))),
		S2Polygon.encode,
		S2Polygon.decode,
	),
)
	== 0
expect S2CodingTest.failures(
	CodingCorpus.polygons,
	|c| c.loops.all(|l| S2CodingTest.bound_is_close(l.vertices, l.bound)),
)
	== 0

# Bytes that are not a plain encoding: wrong versions, trailing bytes, fields
# that upstream does not check, limits, and the compressed formats.
expect S2CodingTest.failures(CodingCorpus.verdicts, S2CodingTest.verdict_holds) == 0

# Every truncation is refused, and none crashes.
expect S2CodingTest.failures(CodingCorpus.truncation_samples, S2CodingTest.truncations_refused) == 0

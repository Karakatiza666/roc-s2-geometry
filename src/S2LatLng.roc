import S1Angle
import Internal/S2Math
import S2Point

## A point on the sphere in latitude-longitude coordinates, both in radians.
##
## Latitude runs from -pi/2 at the south pole to pi/2 at the north pole, and
## longitude from -pi to pi. Nothing enforces those ranges on construction;
## `is_valid` reports whether they hold and `normalized` restores them.
S2LatLng := { lat : F64, lng : F64 }.{

	## The position with latitude `lat` and longitude `lng`, both in radians.
	## The values are not checked or normalized.
	from_radians : F64, F64 -> S2LatLng
	from_radians = |lat, lng| { lat: lat, lng: lng }

	## The position with latitude `lat` and longitude `lng`, both in degrees.
	## The values are not checked or normalized.
	from_degrees : F64, F64 -> S2LatLng
	from_degrees = |lat, lng| {
		lat: S1Angle.from_degrees(lat).radians(),
		lng: S1Angle.from_degrees(lng).radians(),
	}

	## The position with the given latitude and longitude angles. The values
	## are not checked or normalized.
	from_angles : S1Angle, S1Angle -> S2LatLng
	from_angles = |lat, lng| { lat: lat.radians(), lng: lng.radians() }

	## From degrees scaled by 1e5, the unit many geodata formats use.
	from_e5 : I64, I64 -> S2LatLng
	from_e5 = |lat, lng| S2LatLng.from_degrees(lat.to_f64() * 1e-5, lng.to_f64() * 1e-5)

	## The position from latitude and longitude in degrees scaled by 1e6.
	from_e6 : I64, I64 -> S2LatLng
	from_e6 = |lat, lng| S2LatLng.from_degrees(lat.to_f64() * 1e-6, lng.to_f64() * 1e-6)

	## The position from latitude and longitude in degrees scaled by 1e7.
	from_e7 : I64, I64 -> S2LatLng
	from_e7 = |lat, lng| S2LatLng.from_degrees(lat.to_f64() * 1e-7, lng.to_f64() * 1e-7)

	## The position from latitude and longitude in degrees scaled by 1e6, where
	## each value is read as a signed 32-bit number.
	##
	## Use this for coordinates stored as unsigned 32-bit values. See
	## `S1Angle.from_unsigned_e6`.
	from_unsigned_e6 : U32, U32 -> S2LatLng
	from_unsigned_e6 = |lat, lng|
		S2LatLng.from_angles(S1Angle.from_unsigned_e6(lat), S1Angle.from_unsigned_e6(lng))

	## The position from latitude and longitude in degrees scaled by 1e7, where
	## each value is read as a signed 32-bit number. See `from_unsigned_e6`.
	from_unsigned_e7 : U32, U32 -> S2LatLng
	from_unsigned_e7 = |lat, lng|
		S2LatLng.from_angles(S1Angle.from_unsigned_e7(lat), S1Angle.from_unsigned_e7(lng))

	## The latitude and longitude of a point on the sphere. The point need not
	## be unit length.
	from_point : S2Point -> S2LatLng
	from_point = |p| {
		lat: S2LatLng.latitude(p).radians(),
		lng: S2LatLng.longitude(p).radians(),
	}

	## The origin, `(0, 0)`.
	default : () -> S2LatLng
	default = || { lat: 0.0, lng: 0.0 }

	## A value outside the valid range, used as a "no position" sentinel.
	invalid : () -> S2LatLng
	invalid = || { lat: F64.pi, lng: 2.0 * F64.pi }

	## The latitude of a point, computed so that it stays accurate near the
	## poles. A coordinate of negative zero counts as a positive zero, so
	## that points which compare equal give identical positions, as upstream
	## does with its `+ 0.0`.
	latitude : S2Point -> S1Angle
	latitude = |p|
		S1Angle.from_radians(S2Math.atan2(p.z() + 0.0, (p.x() * p.x() + p.y() * p.y()).sqrt()))

	## The longitude of a point. The poles report a longitude of zero. A
	## coordinate of negative zero counts as a positive zero, as for
	## `latitude`.
	longitude : S2Point -> S1Angle
	longitude = |p| S1Angle.from_radians(S2Math.atan2(p.y() + 0.0, p.x() + 0.0))

	## The latitude as an angle.
	lat : S2LatLng -> S1Angle
	lat = |ll| S1Angle.from_radians(ll.lat)

	## The longitude as an angle.
	lng : S2LatLng -> S1Angle
	lng = |ll| S1Angle.from_radians(ll.lng)

	## The latitude in radians.
	lat_radians : S2LatLng -> F64
	lat_radians = |ll| ll.lat

	## The longitude in radians.
	lng_radians : S2LatLng -> F64
	lng_radians = |ll| ll.lng

	## The latitude in degrees.
	lat_degrees : S2LatLng -> F64
	lat_degrees = |ll| S1Angle.from_radians(ll.lat).degrees()

	## The longitude in degrees.
	lng_degrees : S2LatLng -> F64
	lng_degrees = |ll| S1Angle.from_radians(ll.lng).degrees()

	## True when latitude is within `[-pi/2, pi/2]` and longitude within
	## `[-pi, pi]`.
	is_valid : S2LatLng -> Bool
	is_valid = |ll| ll.lat.abs() <= 0.5 * F64.pi and ll.lng.abs() <= F64.pi

	## Latitude clamped to the poles and longitude wrapped into `[-pi, pi]`.
	##
	## A position with an infinite or NaN coordinate stays invalid: the result
	## is `invalid`.
	normalized : S2LatLng -> S2LatLng
	normalized = |ll|
		if !ll.lat.is_finite() or !ll.lng.is_finite() {
			S2LatLng.invalid()
		} else {
			{
				lat: S2Math.clamp(ll.lat, -0.5 * F64.pi, 0.5 * F64.pi),
				lng: S2Math.remainder(ll.lng, 2.0 * F64.pi),
			}
		}

	## The normalized position as text: latitude and longitude in degrees with
	## six digits after the point, separated by a comma, as `"37.774900,-122.419400"`.
	##
	## The text is that of C's `"%f,%f"`, so the last digit is correctly
	## rounded, with ties going to the even digit, and a small negative value
	## keeps its sign, as `-0.000000`. The position is normalized first as
	## upstream does it: the latitude is clamped to the poles and the longitude
	## is wrapped into `[-pi, pi]`. A NaN coordinate gives `nan`. The sign
	## of a NaN is not kept.
	to_string_in_degrees : S2LatLng -> Str
	to_string_in_degrees = |ll| {
		clamped_lat = if (ll.lat.is_nan()) ll.lat else S2Math.clamp(ll.lat, -0.5 * F64.pi, 0.5 * F64.pi)
		wrapped_lng = S2Math.remainder(ll.lng, 2.0 * F64.pi)
		"${fixed6(S1Angle.from_radians(clamped_lat).degrees())},${fixed6(S1Angle.from_radians(wrapped_lng).degrees())}"
	}

	## The corresponding unit vector. Requires a valid position.
	to_point : S2LatLng -> S2Point
	to_point = |ll| {
		cos_lat = ll.lat.cos()
		S2Point.new(ll.lng.cos() * cos_lat, ll.lng.sin() * cos_lat, ll.lat.sin())
	}

	## The great-circle distance to another position.
	##
	## Uses the haversine form, which stays accurate for small distances where
	## the law of cosines loses most of its significant digits.
	distance_to : S2LatLng, S2LatLng -> S1Angle
	distance_to = |a, b| {
		dlat = (0.5 * (b.lat - a.lat)).sin()
		dlng = (0.5 * (b.lng - a.lng)).sin()
		x = dlat * dlat + dlng * dlng * a.lat.cos() * b.lat.cos()
		S1Angle.from_radians(2.0 * S2Math.atan2(x.sqrt(), (1.0 - x).max(0.0).sqrt()))
	}

	## Adds the latitudes and the longitudes. The result is not normalized.
	## Written `a + b`.
	plus : S2LatLng, S2LatLng -> S2LatLng
	plus = |a, b| { lat: a.lat + b.lat, lng: a.lng + b.lng }

	## Subtracts the latitude and longitude of `b` from those of `a`. The
	## result is not normalized. Written `a - b`.
	minus : S2LatLng, S2LatLng -> S2LatLng
	minus = |a, b| { lat: a.lat - b.lat, lng: a.lng - b.lng }

	## Multiplies the latitude and the longitude by `k`. The result is not
	## normalized. Written `ll * k`.
	times : S2LatLng, F64 -> S2LatLng
	times = |ll, k| { lat: ll.lat * k, lng: ll.lng * k }

	is_eq : S2LatLng, S2LatLng -> Bool
	is_eq = |a, b| a.lat == b.lat and a.lng == b.lng

	## True when both coordinates agree to within `max_error` radians.
	approx_eq : S2LatLng, S2LatLng, F64 -> Bool
	approx_eq = |a, b, max_error|
		(a.lat - b.lat).abs() < max_error and (a.lng - b.lng).abs() < max_error

	to_hash : S2LatLng, Hasher -> Hasher
	to_hash = |ll, hasher| hasher.write_u64(ll.lat.to_bits()).write_u64(ll.lng.to_bits())

	to_inspect : S2LatLng -> Str
	to_inspect = |ll| "S2LatLng(${ll.lat_degrees().to_str()}, ${ll.lng_degrees().to_str()})"
}

## The text that C's `"%f"` gives for `x`: the correctly rounded value with
## six digits after the point.
##
## The value is `m * 2^e` with `m` below `2^53`, so `m * 10^6` fits in 128
## bits and the rounding is done on integers. Callers pass a normalized
## angle in degrees, so `e` is negative; a value below `2^-100 * 2^53` is far
## below half a unit in the last place and gives zero.
fixed6 : F64 -> Str
fixed6 = |x| {
	if x.is_nan() {
		return "nan"
	}
	bits = x.to_bits()
	sign = if (bits.shr_zf_wrap(63) == 1) "-" else ""
	if !x.is_finite() {
		return "${sign}inf"
	}
	exponent_field = bits.shr_zf_wrap(52).bitwise_and(0x7ff)
	fraction = bits.bitwise_and(0xfffffffffffff)
	mantissa = if (exponent_field == 0) fraction else fraction.bitwise_or(0x10000000000000)
	exponent = if (exponent_field == 0) -1074 else exponent_field.to_i64_wrap() - 1075
	units =
		if exponent >= 0 {
			# Not reached for a normalized angle: it needs |x| >= 2^52.
			mantissa.to_u128() * 1000000
		} else if exponent < -100 {
			0
		} else {
			product = mantissa.to_u128() * 1000000
			divisor = (1.U128).shl_wrap((-exponent).to_u8_wrap())
			quotient = product // divisor
			remainder = product % divisor
			half = divisor // 2
			if remainder > half or (remainder == half and quotient % 2 == 1) {
				quotient + 1
			} else {
				quotient
			}
		}
	whole = units // 1000000
	fraction_digits = (units % 1000000).to_str()
	padding = Str.repeat("0", 6 - fraction_digits.count_utf8_bytes())
	"${sign}${whole.to_str()}.${padding}${fraction_digits}"
}

expect S2LatLng.from_degrees(90.0, 0.0).lat_radians() == 0.5 * F64.pi
expect S2LatLng.from_degrees(45.0, -90.0).lng_degrees() == -90.0
expect (S2LatLng.from_e7(377749000, -1224194000).lat_degrees() - 37.7749).abs() < 1e-12
expect S2LatLng.default().is_valid()
expect !S2LatLng.invalid().is_valid()
expect !S2LatLng.from_degrees(91.0, 0.0).is_valid()
expect S2LatLng.from_degrees(91.0, 0.0).normalized().lat_degrees() == 90.0
expect (S2LatLng.from_degrees(0.0, 270.0).normalized().lng_degrees() - -90.0).abs() < 1e-13
expect !S2LatLng.from_radians(F64.infinity, 0.0).normalized().is_valid()
expect S2LatLng.from_radians(0.0, -F64.infinity).normalized() == S2LatLng.invalid()
expect S2LatLng.from_degrees(0.0, 0.0).to_point().approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2LatLng.from_degrees(90.0, 0.0).to_point().approx_eq(S2Point.new(0.0, 0.0, 1.0), 1e-15)
expect S2LatLng.from_degrees(0.0, 90.0).to_point().approx_eq(S2Point.new(0.0, 1.0, 0.0), 1e-15)
expect {
	ll = S2LatLng.from_degrees(37.7749, -122.4194)
	S2LatLng.from_point(ll.to_point()).approx_eq(ll, 1e-14)
}
expect S2LatLng.latitude(S2Point.new(0.0, 0.0, 1.0)).degrees() == 90.0
expect S2LatLng.longitude(S2Point.new(0.0, 1.0, 0.0)).degrees() == 90.0
expect {
	d = S2LatLng.from_degrees(0.0, 0.0).distance_to(S2LatLng.from_degrees(0.0, 90.0))
	(d.degrees() - 90.0).abs() < 1e-13
}
expect {
	d = S2LatLng.from_degrees(0.0, 0.0).distance_to(S2LatLng.from_degrees(0.0, 0.0))
	d.radians() == 0.0
}
expect S2LatLng.from_degrees(10.0, 20.0) + S2LatLng.from_degrees(5.0, 5.0)
	== S2LatLng.from_degrees(15.0, 25.0)
expect S2LatLng.from_degrees(10.0, 20.0) * 2.0
	== S2LatLng.from_degrees(20.0, 40.0)

# The values below were printed by upstream's S2LatLng at v0.14.0 through
# tools/s2_oracle.cc.
expect S2LatLng.from_radians(0.6584, -2.1359).to_string_in_degrees() == "37.723541,-122.378055"
expect S2LatLng.from_radians(0.0, 0.0).to_string_in_degrees() == "0.000000,0.000000"
expect S2LatLng.from_radians(-0.0, 0.0).to_string_in_degrees() == "-0.000000,0.000000"
expect S2LatLng.from_radians(1.0e-8, -1.0e-8).to_string_in_degrees() == "0.000001,-0.000001"
expect S2LatLng.from_radians(-1.0e-9, 5.0).to_string_in_degrees() == "-0.000000,-73.521102"
expect S2LatLng.from_radians(1.0e-8, 1.0e-8).to_string_in_degrees() == "0.000001,0.000001"
expect S2LatLng.from_radians(8.726646259971648e-9, 0.0001).to_string_in_degrees() == "0.000000,0.005730"
expect S2LatLng.from_radians(0.0000087266462599716478, 0.0).to_string_in_degrees() == "0.000500,0.000000"
expect S2LatLng.from_radians(0.123456789, 0.0000087).to_string_in_degrees() == "7.073553,0.000498"
# The position is normalized: the latitude stops at the poles, and the
# longitude wraps.
expect S2LatLng.from_radians(2.0, 7.0).to_string_in_degrees() == "90.000000,41.070457"
expect S2LatLng.from_radians(-2.0, -7.0).to_string_in_degrees() == "-90.000000,-41.070457"
expect S2LatLng.from_radians(1.5707963267948966, 1.0e20).to_string_in_degrees() == "90.000000,108.609302"
expect S2LatLng.from_radians(0.5, 3.141592653589793).to_string_in_degrees() == "28.647890,180.000000"
expect S2LatLng.from_radians(0.5, -3.141592653589793).to_string_in_degrees() == "28.647890,-180.000000"
# A value exactly halfway between two six-digit numbers goes to the even
# digit, as the C library does.
expect fixed6(0.0078125) == "0.007812"
expect fixed6(0.0234375) == "0.023438"
expect fixed6(-0.0078125) == "-0.007812"
expect fixed6(1.0e-300) == "0.000000"
expect fixed6(5.0e-324) == "0.000000"
expect fixed6(179.99999999999997) == "180.000000"
expect fixed6(F64.nan) == "nan"
expect fixed6(-F64.infinity) == "-inf"
expect S2LatLng.from_radians(F64.nan, 0.0).to_string_in_degrees() == "nan,0.000000"
expect S2LatLng.from_unsigned_e6(4294967295, 2147483648)
	== S2LatLng.from_angles(S1Angle.from_radians(-1.7453292519943295e-08), S1Angle.from_radians(-37.480660290338939))
expect S2LatLng.from_unsigned_e7(3000000000, 450000000)
	== S2LatLng.from_angles(S1Angle.from_radians(-2.2601443020847993), S1Angle.from_radians(0.78539816339744828))
expect S2LatLng.from_unsigned_e7(0, 0) == S2LatLng.default()

# A coordinate of negative zero gives the same position as a positive zero.
expect S2LatLng.latitude(S2Point.new(1.0, 0.0, -0.0)).radians().to_bits() == 0
expect S2LatLng.longitude(S2Point.new(1.0, -0.0, 0.0)).radians().to_bits() == 0
expect S2LatLng.longitude(S2Point.new(-1.0, -0.0, 0.0)).radians() == F64.pi
expect S2LatLng.longitude(S2Point.new(-1.0, 0.0, 0.0)).radians() == F64.pi

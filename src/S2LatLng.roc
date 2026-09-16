import S1Angle
import Internal/S2Math
import S2Point

## A point on the sphere in latitude-longitude coordinates, both in radians.
##
## Latitude runs from -pi/2 at the south pole to pi/2 at the north pole, and
## longitude from -pi to pi. Nothing enforces those ranges on construction;
## `is_valid` reports whether they hold and `normalized` restores them.
S2LatLng := { lat : F64, lng : F64 }.{

	from_radians : F64, F64 -> S2LatLng
	from_radians = |lat, lng| { lat: lat, lng: lng }

	from_degrees : F64, F64 -> S2LatLng
	from_degrees = |lat, lng| {
		lat: S1Angle.from_degrees(lat).radians(),
		lng: S1Angle.from_degrees(lng).radians(),
	}

	from_angles : S1Angle, S1Angle -> S2LatLng
	from_angles = |lat, lng| { lat: lat.radians(), lng: lng.radians() }

	## From degrees scaled by 1e5, the unit many geodata formats use.
	from_e5 : I64, I64 -> S2LatLng
	from_e5 = |lat, lng| S2LatLng.from_degrees(lat.to_f64() * 1e-5, lng.to_f64() * 1e-5)

	from_e6 : I64, I64 -> S2LatLng
	from_e6 = |lat, lng| S2LatLng.from_degrees(lat.to_f64() * 1e-6, lng.to_f64() * 1e-6)

	from_e7 : I64, I64 -> S2LatLng
	from_e7 = |lat, lng| S2LatLng.from_degrees(lat.to_f64() * 1e-7, lng.to_f64() * 1e-7)

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
	## poles.
	latitude : S2Point -> S1Angle
	latitude = |p|
		S1Angle.from_radians(S2Math.atan2(p.z(), (p.x() * p.x() + p.y() * p.y()).sqrt()))

	## The longitude of a point. The poles report a longitude of zero.
	longitude : S2Point -> S1Angle
	longitude = |p| S1Angle.from_radians(S2Math.atan2(p.y(), p.x()))

	lat : S2LatLng -> S1Angle
	lat = |ll| S1Angle.from_radians(ll.lat)

	lng : S2LatLng -> S1Angle
	lng = |ll| S1Angle.from_radians(ll.lng)

	lat_radians : S2LatLng -> F64
	lat_radians = |ll| ll.lat

	lng_radians : S2LatLng -> F64
	lng_radians = |ll| ll.lng

	lat_degrees : S2LatLng -> F64
	lat_degrees = |ll| S1Angle.from_radians(ll.lat).degrees()

	lng_degrees : S2LatLng -> F64
	lng_degrees = |ll| S1Angle.from_radians(ll.lng).degrees()

	## True when latitude is within `[-pi/2, pi/2]` and longitude within
	## `[-pi, pi]`.
	is_valid : S2LatLng -> Bool
	is_valid = |ll| ll.lat.abs() <= 0.5 * F64.pi and ll.lng.abs() <= F64.pi

	## Latitude clamped to the poles and longitude wrapped into `[-pi, pi]`.
	normalized : S2LatLng -> S2LatLng
	normalized = |ll| {
		lat: S2Math.clamp(ll.lat, -0.5 * F64.pi, 0.5 * F64.pi),
		lng: S2Math.remainder(ll.lng, 2.0 * F64.pi),
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

	plus : S2LatLng, S2LatLng -> S2LatLng
	plus = |a, b| { lat: a.lat + b.lat, lng: a.lng + b.lng }

	minus : S2LatLng, S2LatLng -> S2LatLng
	minus = |a, b| { lat: a.lat - b.lat, lng: a.lng - b.lng }

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

expect S2LatLng.from_degrees(90.0, 0.0).lat_radians() == 0.5 * F64.pi
expect S2LatLng.from_degrees(45.0, -90.0).lng_degrees() == -90.0
expect (S2LatLng.from_e7(377749000, -1224194000).lat_degrees() - 37.7749).abs() < 1e-12
expect S2LatLng.default().is_valid()
expect !S2LatLng.invalid().is_valid()
expect !S2LatLng.from_degrees(91.0, 0.0).is_valid()
expect S2LatLng.from_degrees(91.0, 0.0).normalized().lat_degrees() == 90.0
expect (S2LatLng.from_degrees(0.0, 270.0).normalized().lng_degrees() - -90.0).abs() < 1e-13
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

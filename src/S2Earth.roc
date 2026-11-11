import S1Angle
import S1ChordAngle
import S2LatLng

## Converts between angles on the unit sphere and distances on the Earth.
##
## Every other type in this package works on a unit sphere, where distance is
## an angle. This is the one place that fixes a radius, so it is the only place
## that has to change to model a different body.
##
## The radius used is the IUGG mean radius, 6371.01 km. Distances are therefore
## great-circle distances on a sphere, and differ from geodesic distances on the
## WGS 84 ellipsoid by up to about 0.5%.
S2Earth := [].{

	## The IUGG mean radius of the Earth, in metres.
	radius_meters : F64
	radius_meters = 6371010.0

	## The IUGG mean radius of the Earth, in kilometres.
	radius_km : F64
	radius_km = 6371.01

	## The altitude of the lowest known point on Earth, the Challenger Deep,
	## in metres above the surface of the spherical Earth.
	lowest_altitude_meters : F64
	lowest_altitude_meters = -10898.0

	## The altitude of the highest known point on Earth, Mount Everest, in
	## metres above the surface of the spherical Earth.
	highest_altitude_meters : F64
	highest_altitude_meters = 8846.0

	## The distance along the surface subtended by an angle, in metres.
	to_meters : S1Angle -> F64
	to_meters = |angle| angle.radians() * S2Earth.radius_meters

	## The distance along the surface subtended by an angle, in kilometres.
	to_km : S1Angle -> F64
	to_km = |angle| angle.radians() * S2Earth.radius_km

	## The angle subtended by a distance in metres.
	from_meters : F64 -> S1Angle
	from_meters = |meters| S1Angle.from_radians(meters / S2Earth.radius_meters)

	## The angle subtended by a distance in kilometres.
	from_km : F64 -> S1Angle
	from_km = |km| S1Angle.from_radians(km / S2Earth.radius_km)

	## The chord angle subtended by a distance in metres.
	meters_to_chord_angle : F64 -> S1ChordAngle
	meters_to_chord_angle = |meters| S1ChordAngle.from_angle(S2Earth.from_meters(meters))

	## The chord angle subtended by a distance in kilometres.
	km_to_chord_angle : F64 -> S1ChordAngle
	km_to_chord_angle = |km| S1ChordAngle.from_angle(S2Earth.from_km(km))

	## The distance a chord angle subtends, in metres.
	chord_to_meters : S1ChordAngle -> F64
	chord_to_meters = |chord| S2Earth.to_meters(chord.to_angle())

	## The distance a chord angle subtends, in kilometres.
	chord_to_km : S1ChordAngle -> F64
	chord_to_km = |chord| S2Earth.to_km(chord.to_angle())

	## The great-circle distance between two positions, in metres.
	distance_meters : S2LatLng, S2LatLng -> F64
	distance_meters = |a, b| S2Earth.to_meters(a.distance_to(b))

	## The great-circle distance between two positions, in kilometres.
	distance_km : S2LatLng, S2LatLng -> F64
	distance_km = |a, b| S2Earth.to_km(a.distance_to(b))

	## The area on the surface subtended by a solid angle in steradians, in
	## square metres.
	steradians_to_square_meters : F64 -> F64
	steradians_to_square_meters = |steradians|
		steradians * S2Earth.radius_meters * S2Earth.radius_meters

	## The area on the surface subtended by a solid angle in steradians, in
	## square kilometres.
	steradians_to_square_km : F64 -> F64
	steradians_to_square_km = |steradians| steradians * S2Earth.radius_km * S2Earth.radius_km

	## The solid angle in steradians subtended by an area in square
	## kilometres.
	square_km_to_steradians : F64 -> F64
	square_km_to_steradians = |area| area / (S2Earth.radius_km * S2Earth.radius_km)

	## The solid angle in steradians subtended by an area in square metres.
	square_meters_to_steradians : F64 -> F64
	square_meters_to_steradians = |area| area / (S2Earth.radius_meters * S2Earth.radius_meters)
}

expect S2Earth.to_meters(S1Angle.from_radians(1.0)) == S2Earth.radius_meters
expect S2Earth.from_meters(S2Earth.radius_meters).radians() == 1.0
expect (S2Earth.to_km(S1Angle.from_degrees(1.0)) - 111.19510117748393).abs() < 1e-9
expect (S2Earth.from_km(S2Earth.radius_km).degrees() - 57.29577951308232).abs() < 1e-12
expect {
	# A quarter of the way around the Earth.
	d = S2Earth.distance_km(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0))
	(d - 0.25 * 2.0 * F64.pi * S2Earth.radius_km).abs() < 1e-9
}
expect {
	# San Francisco to New York, about 4130 km.
	d = S2Earth.distance_km(
		S2LatLng.from_degrees(37.7749, -122.4194),
		S2LatLng.from_degrees(40.7128, -74.0060),
	)
	d > 4120.0 and d < 4140.0
}
expect S2Earth.distance_meters(S2LatLng.from_degrees(1.0, 2.0), S2LatLng.from_degrees(1.0, 2.0)) == 0.0
expect (S2Earth.chord_to_km(S1ChordAngle.from_angle(S1Angle.from_degrees(1.0))) - 111.19510117748393).abs() < 1e-8
expect {
	# The whole sphere is about 510 million square kilometres.
	total = S2Earth.steradians_to_square_km(4.0 * F64.pi)
	total > 5.0e8 and total < 5.2e8
}
expect (S2Earth.square_meters_to_steradians(S2Earth.steradians_to_square_meters(0.5)) - 0.5).abs() < 1e-15
expect S2Earth.lowest_altitude_meters == -10898.0
expect S2Earth.highest_altitude_meters == 8846.0
expect (S2Earth.meters_to_chord_angle(S2Earth.radius_meters).to_angle().radians() - 1.0).abs() < 1e-15
expect (S2Earth.km_to_chord_angle(S2Earth.radius_km).to_angle().radians() - 1.0).abs() < 1e-15
expect S2Earth.km_to_chord_angle(1.0e9).length2() == 4.0
expect (S2Earth.square_km_to_steradians(S2Earth.radius_km * S2Earth.radius_km) - 1.0).abs() < 1e-15

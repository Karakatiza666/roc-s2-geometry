import Internal/S2Math
import R2Point
import S2LatLng
import S2Point

## A map projection: a function between points on the sphere and points in
## the plane. Upstream's `S2::Projection` and its two implementations,
## `PlateCarreeProjection` and `MercatorProjection`.
##
## A projection also says how the plane's coordinates wrap around. With a
## wrapping x axis, the points `(x, y)` and `(x + 360, y)` are the same point
## on the sphere, and `wrap_destination` picks the one nearest to a point you
## give.
##
##     proj = S2Projection.plate_carree(180.0)
##     proj.project(S2LatLng.from_degrees(10.0, 20.0).to_point())
##
## Upstream's `Projection` is a base class that a user can derive from. Roc
## has no classes, so this type is a union of the two projections upstream
## has. The edge tessellator therefore needs no type parameter. A projection
## of your own cannot be added to it.
##
## The Mercator projection calls `exp` and `log`, which here are fdlibm's, so
## its results can differ from upstream's by one unit in the last place.
S2Projection :: [
	PlateCarree({ x_wrap : F64, to_radians : F64, from_radians : F64 }),
	Mercator({ x_wrap : F64, to_radians : F64, from_radians : F64 }),
].{

	## The plate carree projection, which maps a point to its longitude and
	## latitude. The x coordinates span `[-x_scale, x_scale]` and the y
	## coordinates span `[-x_scale / 2, x_scale / 2]`. With an `x_scale` of
	## 180, the coordinates are degrees. Upstream's default is `pi`, which
	## gives radians.
	plate_carree : F64 -> S2Projection
	plate_carree = |x_scale|
		PlateCarree({
			x_wrap: 2.0 * x_scale,
			to_radians: F64.pi / x_scale,
			from_radians: x_scale / F64.pi,
		})

	## The spherical Mercator projection. The x coordinates span
	## `[-max_x, max_x]` and wrap, and the y coordinates can be any number.
	## The poles have infinite y coordinates, so do not tessellate an edge
	## with a pole as an endpoint. Clip it first so that y is at most about
	## `5 * max_x`.
	mercator : F64 -> S2Projection
	mercator = |max_x|
		Mercator({
			x_wrap: 2.0 * max_x,
			to_radians: F64.pi / max_x,
			from_radians: max_x / F64.pi,
		})

	## The plane point of a point on the sphere.
	project : S2Projection, S2Point -> R2Point
	project = |proj, p| proj.from_lat_lng(S2LatLng.from_point(p))

	## The point on the sphere of a plane point. When an axis wraps, any
	## number is allowed for its coordinate.
	unproject : S2Projection, R2Point -> S2Point
	unproject = |proj, p| proj.to_lat_lng(p).to_point()

	## The plane point of a position. This is `project` of its point, but
	## cheaper.
	from_lat_lng : S2Projection, S2LatLng -> R2Point
	from_lat_lng = |proj, ll|
		match proj {
			PlateCarree(c) => R2Point.new(c.from_radians * ll.lng_radians(), c.from_radians * ll.lat_radians())
			Mercator(c) => {
				sin_phi = ll.lat_radians().sin()
				y = 0.5 * S2Math.log((1.0 + sin_phi) / (1.0 - sin_phi))
				R2Point.new(c.from_radians * ll.lng_radians(), c.from_radians * y)
			}
		}

	## The position of a plane point. This is the position of `unproject`,
	## but cheaper.
	to_lat_lng : S2Projection, R2Point -> S2LatLng
	to_lat_lng = |proj, p|
		match proj {
			PlateCarree(c) =>
				S2LatLng.from_radians(c.to_radians * p.y(), c.to_radians * S2Math.remainder(p.x(), c.x_wrap))
			Mercator(c) => {
				x = c.to_radians * S2Math.remainder(p.x(), c.x_wrap)
				k = S2Math.exp(2.0 * c.to_radians * p.y())
				y = if (k.is_infinite()) 0.5 * F64.pi else ((k - 1.0) / (k + 1.0)).asin()
				S2LatLng.from_radians(y, x)
			}
		}

	## The plane point that is the given fraction of the way along the
	## straight line from `a` to `b`. A fraction below 0 or above 1 gives a
	## point beyond the ends. Upstream's default `Interpolate`; edges are
	## straight lines in the plane.
	interpolate : S2Projection, F64, R2Point, R2Point -> R2Point
	interpolate = |_proj, f, a, b| R2Point.new((1.0 - f) * a.x() + f * b.x(), (1.0 - f) * a.y() + f * b.y())

	## How far the coordinates wrap along each axis, or 0 for an axis that
	## does not wrap. For both projections, x wraps at twice the scale and y
	## does not wrap.
	wrap_distance : S2Projection -> R2Point
	wrap_distance = |proj|
		match proj {
			PlateCarree(c) => R2Point.new(c.x_wrap, 0.0)
			Mercator(c) => R2Point.new(c.x_wrap, 0.0)
		}

	## The point `b`, moved by a multiple of the wrap distance to be as close
	## as possible to `a`. For `a = [170, 20]` and `b = [-170, 20]` with an x
	## wrap of 360, it gives `[190, 20]`. A coordinate is not changed unless
	## it is more than half the wrap distance away.
	wrap_destination : S2Projection, R2Point, R2Point -> R2Point
	wrap_destination = |proj, a, b| {
		wrap = proj.wrap_distance()
		x =
			if wrap.x() > 0.0 and (b.x() - a.x()).abs() > 0.5 * wrap.x() {
				b.x() - S2Math.round((b.x() - a.x()) / wrap.x()) * wrap.x()
			} else {
				b.x()
			}
		y =
			if wrap.y() > 0.0 and (b.y() - a.y()).abs() > 0.5 * wrap.y() {
				b.y() - S2Math.round((b.y() - a.y()) / wrap.y()) * wrap.y()
			} else {
				b.y()
			}
		R2Point.new(x, y)
	}
}

# Upstream's s2projections_test.cc, and more, through tools/s2_oracle.cc:
# PlateCarreeProjection.Interpolate (the 0.25, -2, 0 and 1 cases),
# PlateCarreeProjection.ProjectUnproject and MercatorProjection.ProjectUnproject
# (the six axis points, the infinite y values and the point at latitude 1
# radian). Mercator results can differ from upstream by an ulp, so the
# comparisons that go through exp or log are the ones to check first.
expect S2Projection.plate_carree(180.0).project(S2LatLng.from_degrees(0.0, 0.0).to_point()) == R2Point.new(0.0, 0.0)
expect S2Projection.plate_carree(180.0).project(S2LatLng.from_degrees(10.0, 20.0).to_point()) == R2Point.new(20.0, 10.0)
expect S2Projection.plate_carree(180.0).project(S2LatLng.from_degrees(-33.5, 151.2).to_point()) == R2Point.new(151.19999999999999, -33.499999999999993)
expect S2Projection.plate_carree(180.0).project(S2LatLng.from_degrees(60.0, -170.0).to_point()) == R2Point.new(-170.0, 59.999999999999993)
expect S2Projection.plate_carree(180.0).project(S2LatLng.from_degrees(89.9, 45.0).to_point()) == R2Point.new(45.0, 89.900000000000006)
expect S2Projection.plate_carree(180.0).project(S2Point.new(1.0, 0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.plate_carree(180.0).project(S2Point.new(-1.0, 0.0, 0.0)) == R2Point.new(180.0, 0.0)
expect S2Projection.plate_carree(180.0).project(S2Point.new(0.0, 1.0, 0.0)) == R2Point.new(90.0, 0.0)
expect S2Projection.plate_carree(180.0).project(S2Point.new(0.0, -1.0, 0.0)) == R2Point.new(-90.0, 0.0)
expect S2Projection.plate_carree(180.0).project(S2Point.new(0.0, 0.0, 1.0)) == R2Point.new(0.0, 90.0)
expect S2Projection.plate_carree(180.0).project(S2Point.new(0.0, 0.0, -1.0)) == R2Point.new(0.0, -90.0)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(0.0, 0.0)).approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, 0.0)) == S2LatLng.from_radians(0.0, 0.0)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(180.0, 0.0)).approx_eq(S2Point.new(-1.0, 1.2246467991473532e-16, 0.0), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(180.0, 0.0)) == S2LatLng.from_radians(0.0, 3.1415926535897931)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(90.0, 0.0)).approx_eq(S2Point.new(6.123233995736766e-17, 1.0, 0.0), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(90.0, 0.0)) == S2LatLng.from_radians(0.0, 1.5707963267948966)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(-90.0, 0.0)).approx_eq(S2Point.new(6.123233995736766e-17, -1.0, 0.0), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(-90.0, 0.0)) == S2LatLng.from_radians(0.0, -1.5707963267948966)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(0.0, 90.0)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, 90.0)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(0.0, -90.0)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, -1.0), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, -90.0)) == S2LatLng.from_radians(-1.5707963267948966, 0.0)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(0.0, 70.25557896783025)).approx_eq(S2Point.new(0.33782507281529445, 0.0, 0.94120891420414254), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, 70.25557896783025)) == S2LatLng.from_radians(1.2261911708835171, 0.0)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(0.0, 1.0e300)).approx_eq(S2Point.new(-0.66554742494619035, -0.0, -0.74635556214681953), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, 1.0e300)) == S2LatLng.from_radians(1.7453292519943297e298, 0.0)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, F64.infinity)) == S2LatLng.from_radians(F64.infinity, 0.0)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(0.0, -F64.infinity)) == S2LatLng.from_radians(-F64.infinity, 0.0)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(190.0, 20.0)).approx_eq(S2Point.new(-0.92541657839832336, -0.16317591116653477, 0.34202014332566871), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(190.0, 20.0)) == S2LatLng.from_radians(0.3490658503988659, -2.9670597283903604)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(-540.0, -5.0)).approx_eq(S2Point.new(-0.99619469809174555, 1.2199866483456202e-16, -0.087155742747658166), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(-540.0, -5.0)) == S2LatLng.from_radians(-0.087266462599716474, 3.1415926535897931)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(1000000.0, 3.0)).approx_eq(S2Point.new(0.17341019887450629, -0.9834581082132785, 0.052335956242943835), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(1000000.0, 3.0)) == S2LatLng.from_radians(0.05235987755982989, -1.3962634015954636)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(123.456, -45.5)).approx_eq(S2Point.new(-0.38640878517533139, 0.58477521110310648, -0.71325044915418156), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(123.456, -45.5)) == S2LatLng.from_radians(-0.79412480965741994, 2.1547136813421197)
expect S2Projection.plate_carree(180.0).unproject(R2Point.new(90.0, 45.0)).approx_eq(S2Point.new(4.329780281177467e-17, 0.70710678118654757, 0.70710678118654746), 1e-15)
expect S2Projection.plate_carree(180.0).to_lat_lng(R2Point.new(90.0, 45.0)) == S2LatLng.from_radians(0.78539816339744828, 1.5707963267948966)
expect S2Projection.plate_carree(180.0).from_lat_lng(S2LatLng.from_radians(0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.plate_carree(180.0).from_lat_lng(S2LatLng.from_radians(0.5, -1.2)) == R2Point.new(-68.754935415698782, 28.647889756541161)
expect S2Projection.plate_carree(180.0).from_lat_lng(S2LatLng.from_radians(1.0, 0.0)) == R2Point.new(0.0, 57.295779513082323)
expect S2Projection.plate_carree(180.0).from_lat_lng(S2LatLng.from_radians(-0.3, 3.0)) == R2Point.new(171.88733853924697, -17.188733853924695)
expect S2Projection.plate_carree(180.0).from_lat_lng(S2LatLng.from_radians(1.5707963267948966, 0.1)) == R2Point.new(5.729577951308233, 90.0)
expect S2Projection.plate_carree(180.0).from_lat_lng(S2LatLng.from_radians(-1.5707963267948966, 0.1)) == R2Point.new(5.729577951308233, -90.0)
expect S2Projection.plate_carree(180.0).wrap_distance() == R2Point.new(360.0, 0.0)
expect S2Projection.plate_carree(180.0).interpolate(0.25, R2Point.new(1.0, 5.0), R2Point.new(3.0, 9.0)) == R2Point.new(1.5, 6.0)
expect S2Projection.plate_carree(180.0).interpolate(-2.0, R2Point.new(1.0, 0.0), R2Point.new(3.0, 0.0)) == R2Point.new(-3.0, 0.0)
expect S2Projection.plate_carree(180.0).interpolate(0.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(1.234, -5.4559999999999998e-20)
expect S2Projection.plate_carree(180.0).interpolate(1.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(2.1234e-20, 7.4560000000000004)
expect S2Projection.plate_carree(180.0).interpolate(0.5, R2Point.new(-170.0, 10.0), R2Point.new(170.0, 20.0)) == R2Point.new(0.0, 15.0)
expect S2Projection.plate_carree(180.0).interpolate(0.3125, R2Point.new(0.1, 0.2), R2Point.new(0.7, -0.9)) == R2Point.new(0.28749999999999998, -0.14374999999999999)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(170.0, 20.0), R2Point.new(-170.0, 20.0)) == R2Point.new(190.0, 20.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(-170.0, 20.0), R2Point.new(170.0, 20.0)) == R2Point.new(-190.0, 20.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.0, 0.0)) == R2Point.new(180.0, 0.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(181.0, 0.0)) == R2Point.new(-179.0, 0.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-181.0, 5.0)) == R2Point.new(179.0, 5.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(540.0, 0.0)) == R2Point.new(-180.0, 0.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(179.9, 0.0)) == R2Point.new(179.90000000000001, 0.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(100.0, 0.0), R2Point.new(-100.0, 0.0)) == R2Point.new(260.0, 0.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(0.0, 500.0)) == R2Point.new(0.0, 500.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(10.0, 10.0), R2Point.new(10.0, 10.0)) == R2Point.new(10.0, 10.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-180.0, 0.0)) == R2Point.new(-180.0, 0.0)
expect S2Projection.plate_carree(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.5, 0.0)) == R2Point.new(-179.5, 0.0)
expect S2Projection.plate_carree(3.141592653589793).project(S2LatLng.from_degrees(0.0, 0.0).to_point()) == R2Point.new(0.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).project(S2LatLng.from_degrees(10.0, 20.0).to_point()) == R2Point.new(0.3490658503988659, 0.17453292519943295)
expect S2Projection.plate_carree(3.141592653589793).project(S2LatLng.from_degrees(-33.5, 151.2).to_point()) == R2Point.new(2.638937829015426, -0.58468529941810032)
expect S2Projection.plate_carree(3.141592653589793).project(S2LatLng.from_degrees(60.0, -170.0).to_point()) == R2Point.new(-2.9670597283903604, 1.0471975511965976)
expect S2Projection.plate_carree(3.141592653589793).project(S2LatLng.from_degrees(89.9, 45.0).to_point()) == R2Point.new(0.78539816339744828, 1.5690509975429023)
expect S2Projection.plate_carree(3.141592653589793).project(S2Point.new(1.0, 0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).project(S2Point.new(-1.0, 0.0, 0.0)) == R2Point.new(3.1415926535897931, 0.0)
expect S2Projection.plate_carree(3.141592653589793).project(S2Point.new(0.0, 1.0, 0.0)) == R2Point.new(1.5707963267948966, 0.0)
expect S2Projection.plate_carree(3.141592653589793).project(S2Point.new(0.0, -1.0, 0.0)) == R2Point.new(-1.5707963267948966, 0.0)
expect S2Projection.plate_carree(3.141592653589793).project(S2Point.new(0.0, 0.0, 1.0)) == R2Point.new(0.0, 1.5707963267948966)
expect S2Projection.plate_carree(3.141592653589793).project(S2Point.new(0.0, 0.0, -1.0)) == R2Point.new(0.0, -1.5707963267948966)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(0.0, 0.0)).approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, 0.0)) == S2LatLng.from_radians(0.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(180.0, 0.0)).approx_eq(S2Point.new(-0.59846006905785243, -0.80115263573383477, 0.0), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(180.0, 0.0)) == S2LatLng.from_radians(0.0, -2.2123739082080007)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(90.0, 0.0)).approx_eq(S2Point.new(-0.44807361612917324, 0.89399666360055641, 0.0), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(90.0, 0.0)) == S2LatLng.from_radians(0.0, 2.0354056994857928)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(-90.0, 0.0)).approx_eq(S2Point.new(-0.44807361612917324, -0.89399666360055641, 0.0), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(-90.0, 0.0)) == S2LatLng.from_radians(0.0, -2.0354056994857928)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(0.0, 90.0)).approx_eq(S2Point.new(-0.44807361612917018, -0.0, 0.89399666360055785), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, 90.0)) == S2LatLng.from_radians(90.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(0.0, -90.0)).approx_eq(S2Point.new(-0.44807361612917018, -0.0, -0.89399666360055785), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, -90.0)) == S2LatLng.from_radians(-90.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(0.0, 70.25557896783025)).approx_eq(S2Point.new(0.41710324582305197, 0.0, 0.90885911027170474), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, 70.25557896783025)) == S2LatLng.from_radians(70.255578967830246, 0.0)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(0.0, 1.0e300)).approx_eq(S2Point.new(-0.57538611195754907, -0.0, -0.81788191211590855), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, 1.0e300)) == S2LatLng.from_radians(1.0000000000000001e300, 0.0)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, F64.infinity)) == S2LatLng.from_radians(F64.infinity, 0.0)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(0.0, -F64.infinity)) == S2LatLng.from_radians(-F64.infinity, 0.0)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(190.0, 20.0)).approx_eq(S2Point.new(0.027058639468531872, 0.40718398691989482, 0.91294525072762767), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(190.0, 20.0)) == S2LatLng.from_radians(20.0, 1.504440784612413)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(-540.0, -5.0)).approx_eq(S2Point.new(0.26607956912513192, 0.098315300721494484, 0.95892427466313845), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(-540.0, -5.0)) == S2LatLng.from_radians(-5.0, 0.35393641744441595)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(1000000.0, 3.0)).approx_eq(S2Point.new(-0.92737757744582372, 0.34649094097234096, 0.14112000805986721), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(1000000.0, 3.0)) == S2LatLng.from_radians(3.0, -0.35756416704675331)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(123.456, -45.5)).approx_eq(S2Point.new(-0.031560599911890308, -0.042663779357914676, -0.99859087241177047), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(123.456, -45.5)) == S2LatLng.from_radians(-45.5, -2.2077061435917216)
expect S2Projection.plate_carree(3.141592653589793).unproject(R2Point.new(1.5707963267948966, 0.7853981633974483)).approx_eq(S2Point.new(4.329780281177467e-17, 0.70710678118654757, 0.70710678118654746), 1e-15)
expect S2Projection.plate_carree(3.141592653589793).to_lat_lng(R2Point.new(1.5707963267948966, 0.7853981633974483)) == S2LatLng.from_radians(0.78539816339744828, 1.5707963267948966)
expect S2Projection.plate_carree(3.141592653589793).from_lat_lng(S2LatLng.from_radians(0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).from_lat_lng(S2LatLng.from_radians(0.5, -1.2)) == R2Point.new(-1.2, 0.5)
expect S2Projection.plate_carree(3.141592653589793).from_lat_lng(S2LatLng.from_radians(1.0, 0.0)) == R2Point.new(0.0, 1.0)
expect S2Projection.plate_carree(3.141592653589793).from_lat_lng(S2LatLng.from_radians(-0.3, 3.0)) == R2Point.new(3.0, -0.29999999999999999)
expect S2Projection.plate_carree(3.141592653589793).from_lat_lng(S2LatLng.from_radians(1.5707963267948966, 0.1)) == R2Point.new(0.10000000000000001, 1.5707963267948966)
expect S2Projection.plate_carree(3.141592653589793).from_lat_lng(S2LatLng.from_radians(-1.5707963267948966, 0.1)) == R2Point.new(0.10000000000000001, -1.5707963267948966)
expect S2Projection.plate_carree(3.141592653589793).wrap_distance() == R2Point.new(6.2831853071795862, 0.0)
expect S2Projection.plate_carree(3.141592653589793).interpolate(0.25, R2Point.new(1.0, 5.0), R2Point.new(3.0, 9.0)) == R2Point.new(1.5, 6.0)
expect S2Projection.plate_carree(3.141592653589793).interpolate(-2.0, R2Point.new(1.0, 0.0), R2Point.new(3.0, 0.0)) == R2Point.new(-3.0, 0.0)
expect S2Projection.plate_carree(3.141592653589793).interpolate(0.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(1.234, -5.4559999999999998e-20)
expect S2Projection.plate_carree(3.141592653589793).interpolate(1.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(2.1234e-20, 7.4560000000000004)
expect S2Projection.plate_carree(3.141592653589793).interpolate(0.5, R2Point.new(-170.0, 10.0), R2Point.new(170.0, 20.0)) == R2Point.new(0.0, 15.0)
expect S2Projection.plate_carree(3.141592653589793).interpolate(0.3125, R2Point.new(0.1, 0.2), R2Point.new(0.7, -0.9)) == R2Point.new(0.28749999999999998, -0.14374999999999999)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(170.0, 20.0), R2Point.new(-170.0, 20.0)) == R2Point.new(169.29200658769764, 20.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(-170.0, 20.0), R2Point.new(170.0, 20.0)) == R2Point.new(-169.29200658769764, 20.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.0, 0.0)) == R2Point.new(-2.2123739082080078, 0.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(181.0, 0.0)) == R2Point.new(-1.2123739082080078, 0.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-181.0, 5.0)) == R2Point.new(1.2123739082080078, 5.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(540.0, 0.0)) == R2Point.new(-0.35393641744440174, 0.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(179.9, 0.0)) == R2Point.new(-2.3123739082080021, 0.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(100.0, 0.0), R2Point.new(-100.0, 0.0)) == R2Point.new(101.06192982974676, 0.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(0.0, 500.0)) == R2Point.new(0.0, 500.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(10.0, 10.0), R2Point.new(10.0, 10.0)) == R2Point.new(10.0, 10.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-180.0, 0.0)) == R2Point.new(2.2123739082080078, 0.0)
expect S2Projection.plate_carree(3.141592653589793).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.5, 0.0)) == R2Point.new(-1.7123739082080078, 0.0)
expect S2Projection.mercator(180.0).project(S2LatLng.from_degrees(0.0, 0.0).to_point()) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(180.0).project(S2LatLng.from_degrees(10.0, 20.0).to_point()) == R2Point.new(20.0, 10.051159656630118)
expect S2Projection.mercator(180.0).project(S2LatLng.from_degrees(-33.5, 151.2).to_point()) == R2Point.new(151.19999999999999, -35.589995868766046)
expect S2Projection.mercator(180.0).project(S2LatLng.from_degrees(60.0, -170.0).to_point()) == R2Point.new(-170.0, 75.456129290216893)
expect S2Projection.mercator(180.0).project(S2LatLng.from_degrees(89.9, 45.0).to_point()) == R2Point.new(45.0, 403.58912088913962)
expect S2Projection.mercator(180.0).project(S2Point.new(1.0, 0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(180.0).project(S2Point.new(-1.0, 0.0, 0.0)) == R2Point.new(180.0, 0.0)
expect S2Projection.mercator(180.0).project(S2Point.new(0.0, 1.0, 0.0)) == R2Point.new(90.0, 0.0)
expect S2Projection.mercator(180.0).project(S2Point.new(0.0, -1.0, 0.0)) == R2Point.new(-90.0, 0.0)
expect S2Projection.mercator(180.0).project(S2Point.new(0.0, 0.0, 1.0)) == R2Point.new(0.0, F64.infinity)
expect S2Projection.mercator(180.0).project(S2Point.new(0.0, 0.0, -1.0)) == R2Point.new(0.0, -F64.infinity)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, 0.0)).approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, 0.0)) == S2LatLng.from_radians(0.0, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(180.0, 0.0)).approx_eq(S2Point.new(-1.0, 1.2246467991473532e-16, 0.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(180.0, 0.0)) == S2LatLng.from_radians(0.0, 3.1415926535897931)
expect S2Projection.mercator(180.0).unproject(R2Point.new(90.0, 0.0)).approx_eq(S2Point.new(6.123233995736766e-17, 1.0, 0.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(90.0, 0.0)) == S2LatLng.from_radians(0.0, 1.5707963267948966)
expect S2Projection.mercator(180.0).unproject(R2Point.new(-90.0, 0.0)).approx_eq(S2Point.new(6.123233995736766e-17, -1.0, 0.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(-90.0, 0.0)) == S2LatLng.from_radians(0.0, -1.5707963267948966)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, 90.0)).approx_eq(S2Point.new(0.39853681533838664, 0.0, 0.91715233566727439), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, 90.0)) == S2LatLng.from_radians(1.1608753909688045, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, -90.0)).approx_eq(S2Point.new(0.39853681533838681, 0.0, -0.91715233566727428), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, -90.0)) == S2LatLng.from_radians(-1.1608753909688043, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, 70.25557896783025)).approx_eq(S2Point.new(0.54030230586813977, 0.0, 0.8414709848078965), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, 70.25557896783025)) == S2LatLng.from_radians(1.0, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, 1.0e300)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, 1.0e300)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, F64.infinity)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, F64.infinity)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(0.0, -F64.infinity)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, -1.0), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(0.0, -F64.infinity)) == S2LatLng.from_radians(-1.5707963267948966, 0.0)
expect S2Projection.mercator(180.0).unproject(R2Point.new(190.0, 20.0)).approx_eq(S2Point.new(-0.92771207185079529, -0.16358066859624518, 0.33554683220663883), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(190.0, 20.0)) == S2LatLng.from_radians(0.34218565691729641, -2.9670597283903604)
expect S2Projection.mercator(180.0).unproject(R2Point.new(-540.0, -5.0)).approx_eq(S2Point.new(-0.99620432721179419, 1.2199984406166663e-16, -0.087045611287970143), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(-540.0, -5.0)) == S2LatLng.from_radians(-0.08715591099014712, 3.1415926535897931)
expect S2Projection.mercator(180.0).unproject(R2Point.new(1000000.0, 3.0)).approx_eq(S2Point.new(0.17341041610381064, -0.98345934018188297, 0.052312080781770125), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(1000000.0, 3.0)) == S2LatLng.from_radians(0.052335969348238524, -1.3962634015954636)
expect S2Projection.mercator(180.0).unproject(R2Point.new(123.456, -45.5)).approx_eq(S2Point.new(-0.41381159436534515, 0.62624549890113723, -0.66073938846936975), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(123.456, -45.5)) == S2LatLng.from_radians(-0.72180337738254596, 2.1547136813421197)
expect S2Projection.mercator(180.0).unproject(R2Point.new(90.0, 45.0)).approx_eq(S2Point.new(4.6226724891299804e-17, 0.7549397087141313, 0.65579420263267241), 1e-15)
expect S2Projection.mercator(180.0).to_lat_lng(R2Point.new(90.0, 45.0)) == S2LatLng.from_radians(0.71523414844653965, 1.5707963267948966)
expect S2Projection.mercator(180.0).from_lat_lng(S2LatLng.from_radians(0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(180.0).from_lat_lng(S2LatLng.from_radians(0.5, -1.2)) == R2Point.new(-68.754935415698782, 29.922039218771832)
expect S2Projection.mercator(180.0).from_lat_lng(S2LatLng.from_radians(1.0, 0.0)) == R2Point.new(0.0, 70.255578967830246)
expect S2Projection.mercator(180.0).from_lat_lng(S2LatLng.from_radians(-0.3, 3.0)) == R2Point.new(171.88733853924697, -17.452522156128609)
expect S2Projection.mercator(180.0).from_lat_lng(S2LatLng.from_radians(1.5707963267948966, 0.1)) == R2Point.new(5.729577951308233, F64.infinity)
expect S2Projection.mercator(180.0).from_lat_lng(S2LatLng.from_radians(-1.5707963267948966, 0.1)) == R2Point.new(5.729577951308233, -F64.infinity)
expect S2Projection.mercator(180.0).wrap_distance() == R2Point.new(360.0, 0.0)
expect S2Projection.mercator(180.0).interpolate(0.25, R2Point.new(1.0, 5.0), R2Point.new(3.0, 9.0)) == R2Point.new(1.5, 6.0)
expect S2Projection.mercator(180.0).interpolate(-2.0, R2Point.new(1.0, 0.0), R2Point.new(3.0, 0.0)) == R2Point.new(-3.0, 0.0)
expect S2Projection.mercator(180.0).interpolate(0.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(1.234, -5.4559999999999998e-20)
expect S2Projection.mercator(180.0).interpolate(1.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(2.1234e-20, 7.4560000000000004)
expect S2Projection.mercator(180.0).interpolate(0.5, R2Point.new(-170.0, 10.0), R2Point.new(170.0, 20.0)) == R2Point.new(0.0, 15.0)
expect S2Projection.mercator(180.0).interpolate(0.3125, R2Point.new(0.1, 0.2), R2Point.new(0.7, -0.9)) == R2Point.new(0.28749999999999998, -0.14374999999999999)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(170.0, 20.0), R2Point.new(-170.0, 20.0)) == R2Point.new(190.0, 20.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(-170.0, 20.0), R2Point.new(170.0, 20.0)) == R2Point.new(-190.0, 20.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.0, 0.0)) == R2Point.new(180.0, 0.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(181.0, 0.0)) == R2Point.new(-179.0, 0.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-181.0, 5.0)) == R2Point.new(179.0, 5.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(540.0, 0.0)) == R2Point.new(-180.0, 0.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(179.9, 0.0)) == R2Point.new(179.90000000000001, 0.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(100.0, 0.0), R2Point.new(-100.0, 0.0)) == R2Point.new(260.0, 0.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(0.0, 500.0)) == R2Point.new(0.0, 500.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(10.0, 10.0), R2Point.new(10.0, 10.0)) == R2Point.new(10.0, 10.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-180.0, 0.0)) == R2Point.new(-180.0, 0.0)
expect S2Projection.mercator(180.0).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.5, 0.0)) == R2Point.new(-179.5, 0.0)
expect S2Projection.mercator(0.5).project(S2LatLng.from_degrees(0.0, 0.0).to_point()) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).project(S2LatLng.from_degrees(10.0, 20.0).to_point()) == R2Point.new(0.055555555555555552, 0.027919887935083661)
# This one is one unit in the last place away from upstream's value.
expect S2Projection.mercator(0.5).project(S2LatLng.from_degrees(-33.5, 151.2).to_point()).approx_eq(R2Point.new(0.41999999999999998, -0.098861099635461233), 1e-15)
expect S2Projection.mercator(0.5).project(S2LatLng.from_degrees(60.0, -170.0).to_point()) == R2Point.new(-0.47222222222222227, 0.20960035913949135)
expect S2Projection.mercator(0.5).project(S2LatLng.from_degrees(89.9, 45.0).to_point()) == R2Point.new(0.125, 1.1210808913587211)
expect S2Projection.mercator(0.5).project(S2Point.new(1.0, 0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).project(S2Point.new(-1.0, 0.0, 0.0)) == R2Point.new(0.5, 0.0)
expect S2Projection.mercator(0.5).project(S2Point.new(0.0, 1.0, 0.0)) == R2Point.new(0.25, 0.0)
expect S2Projection.mercator(0.5).project(S2Point.new(0.0, -1.0, 0.0)) == R2Point.new(-0.25, 0.0)
expect S2Projection.mercator(0.5).project(S2Point.new(0.0, 0.0, 1.0)) == R2Point.new(0.0, F64.infinity)
expect S2Projection.mercator(0.5).project(S2Point.new(0.0, 0.0, -1.0)) == R2Point.new(0.0, -F64.infinity)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, 0.0)).approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, 0.0)) == S2LatLng.from_radians(0.0, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(180.0, 0.0)).approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(180.0, 0.0)) == S2LatLng.from_radians(0.0, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(90.0, 0.0)).approx_eq(S2Point.new(1.0, 0.0, 0.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(90.0, 0.0)) == S2LatLng.from_radians(0.0, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(-90.0, 0.0)).approx_eq(S2Point.new(1.0, -0.0, 0.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(-90.0, 0.0)) == S2LatLng.from_radians(0.0, -0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, 90.0)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, 90.0)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, -90.0)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, -1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, -90.0)) == S2LatLng.from_radians(-1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, 70.25557896783025)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, 70.25557896783025)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, 1.0e300)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, 1.0e300)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, F64.infinity)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, F64.infinity)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.0, -F64.infinity)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, -1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.0, -F64.infinity)) == S2LatLng.from_radians(-1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(190.0, 20.0)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(190.0, 20.0)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(-540.0, -5.0)).approx_eq(S2Point.new(6.123233995736766e-17, -0.0, -1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(-540.0, -5.0)) == S2LatLng.from_radians(-1.5707963267948966, -0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(1000000.0, 3.0)).approx_eq(S2Point.new(6.123233995736766e-17, 0.0, 1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(1000000.0, 3.0)) == S2LatLng.from_radians(1.5707963267948966, 0.0)
expect S2Projection.mercator(0.5).unproject(R2Point.new(123.456, -45.5)).approx_eq(S2Point.new(-5.8907205434954388e-17, 1.671348570761722e-17, -1.0), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(123.456, -45.5)) == S2LatLng.from_radians(-1.5707963267948966, 2.8651325000739107)
expect S2Projection.mercator(0.5).unproject(R2Point.new(0.25, 0.125)).approx_eq(S2Point.new(4.6226724891299804e-17, 0.7549397087141313, 0.65579420263267241), 1e-15)
expect S2Projection.mercator(0.5).to_lat_lng(R2Point.new(0.25, 0.125)) == S2LatLng.from_radians(0.71523414844653965, 1.5707963267948966)
expect S2Projection.mercator(0.5).from_lat_lng(S2LatLng.from_radians(0.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).from_lat_lng(S2LatLng.from_radians(0.5, -1.2)) == R2Point.new(-0.19098593171027442, 0.083116775607699533)
expect S2Projection.mercator(0.5).from_lat_lng(S2LatLng.from_radians(1.0, 0.0)) == R2Point.new(0.0, 0.1951543860217507)
expect S2Projection.mercator(0.5).from_lat_lng(S2LatLng.from_radians(-0.3, 3.0)) == R2Point.new(0.47746482927568601, -0.048479228211468356)
expect S2Projection.mercator(0.5).from_lat_lng(S2LatLng.from_radians(1.5707963267948966, 0.1)) == R2Point.new(0.015915494309189534, F64.infinity)
expect S2Projection.mercator(0.5).from_lat_lng(S2LatLng.from_radians(-1.5707963267948966, 0.1)) == R2Point.new(0.015915494309189534, -F64.infinity)
expect S2Projection.mercator(0.5).wrap_distance() == R2Point.new(1.0, 0.0)
expect S2Projection.mercator(0.5).interpolate(0.25, R2Point.new(1.0, 5.0), R2Point.new(3.0, 9.0)) == R2Point.new(1.5, 6.0)
expect S2Projection.mercator(0.5).interpolate(-2.0, R2Point.new(1.0, 0.0), R2Point.new(3.0, 0.0)) == R2Point.new(-3.0, 0.0)
expect S2Projection.mercator(0.5).interpolate(0.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(1.234, -5.4559999999999998e-20)
expect S2Projection.mercator(0.5).interpolate(1.0, R2Point.new(1.234, -5.456e-20), R2Point.new(2.1234e-20, 7.456)) == R2Point.new(2.1234e-20, 7.4560000000000004)
expect S2Projection.mercator(0.5).interpolate(0.5, R2Point.new(-170.0, 10.0), R2Point.new(170.0, 20.0)) == R2Point.new(0.0, 15.0)
expect S2Projection.mercator(0.5).interpolate(0.3125, R2Point.new(0.1, 0.2), R2Point.new(0.7, -0.9)) == R2Point.new(0.28749999999999998, -0.14374999999999999)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(170.0, 20.0), R2Point.new(-170.0, 20.0)) == R2Point.new(170.0, 20.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(-170.0, 20.0), R2Point.new(170.0, 20.0)) == R2Point.new(-170.0, 20.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(181.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-181.0, 5.0)) == R2Point.new(0.0, 5.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(540.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(179.9, 0.0)) == R2Point.new(-0.099999999999994316, 0.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(100.0, 0.0), R2Point.new(-100.0, 0.0)) == R2Point.new(100.0, 0.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(0.0, 500.0)) == R2Point.new(0.0, 500.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(10.0, 10.0), R2Point.new(10.0, 10.0)) == R2Point.new(10.0, 10.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(-180.0, 0.0)) == R2Point.new(0.0, 0.0)
expect S2Projection.mercator(0.5).wrap_destination(R2Point.new(0.0, 0.0), R2Point.new(180.5, 0.0)) == R2Point.new(-0.5, 0.0)

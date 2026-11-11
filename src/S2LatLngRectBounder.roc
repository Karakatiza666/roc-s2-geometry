import R1Interval
import S1Interval
import S2LatLng
import S2LatLngRect
import Internal/S2Math
import S2Point

## Builds the bounding rectangle of a chain of geodesic edges, one vertex at
## a time.
##
## A geodesic edge bulges towards a pole between its endpoints, so the
## rectangle of the vertices alone is too small. This accounts for each edge,
## with error bounds, and the result contains every point of every edge.
## `S2Loop` and `S2Polyline` compute their bounds with it.
##
## Upstream's bounder is a mutable object. Here it is a value, and
## `add_point` returns the extended bounder:
##
## ```
## bound =
##     [a, b, c]
##     .fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p))
##     .bound()
## ```
S2LatLngRectBounder := { rect : S2LatLngRect, a : S2Point, a_lat_lng : S2LatLng }.{

	## A bounder with no vertices yet, whose bound is empty.
	new : () -> S2LatLngRectBounder
	new = || {
		rect: S2LatLngRect.empty(),
		a: S2Point.zero(),
		a_lat_lng: S2LatLng.from_radians(0.0, 0.0),
	}

	## The bounder extended by the edge from the previous vertex to `b`, or
	## started at `b` when there is no previous vertex. `b` must be unit
	## length.
	add_point : S2LatLngRectBounder, S2Point -> S2LatLngRectBounder
	add_point = |bounder, b| add_internal(bounder, b, S2LatLng.from_point(b))

	## `add_point` for a vertex given in latitude and longitude.
	add_lat_lng : S2LatLngRectBounder, S2LatLng -> S2LatLngRectBounder
	add_lat_lng = |bounder, b_lat_lng| add_internal(bounder, b_lat_lng.to_point(), b_lat_lng)

	## A rectangle that contains every point of the edges added so far.
	##
	## It is grown by `2 * epsilon` in latitude against rounding, and it
	## takes every longitude where it touches a pole. It need not be the
	## smallest such rectangle: the latitude can exceed the true bound by
	## `max_error_for_tests().lat()` and the longitude by its `lng()`.
	bound : S2LatLngRectBounder -> S2LatLngRect
	bound = |bounder|
		bounder.rect
			.expanded(S2LatLng.from_radians(2.0 * f64_epsilon, 0.0))
			.polar_closure()

	## A rectangle that contains the bound of every region contained by a
	## region whose bound is `bound`.
	##
	## Rectangles of regions do not nest exactly: a region inside another can
	## have a bound that reaches a little beyond the outer bound, because
	## each bound is computed with rounding. This grows `bound` by enough to
	## cover that, and gives the full rectangle when the region might wrap
	## around the sphere.
	expand_for_subregions : S2LatLngRect -> S2LatLngRect
	expand_for_subregions = |rect| {
		if rect.is_empty() {
			return rect
		}
		# How far the longitude interval is from covering a full half turn.
		lng_gap = (F64.pi - rect.lng().length() - 2.5 * f64_epsilon).max(0.0)
		# The smallest absolute latitude of a point in the rectangle, which
		# is negative when the rectangle crosses the equator.
		min_abs_lat = rect.lat().lo().max(-rect.lat().hi())
		lat_gap1 = 0.5 * F64.pi + rect.lat().lo()
		lat_gap2 = 0.5 * F64.pi - rect.lat().hi()
		# A subregion might contain a pair of antipodal points, whose bound
		# is the full rectangle.
		full =
			if min_abs_lat >= 0.0 {
				2.0 * min_abs_lat + lng_gap < 1.354e-15
			} else if lng_gap >= 0.5 * F64.pi {
				lat_gap1 + lat_gap2 < 1.687e-15
			} else {
				lat_gap1.max(lat_gap2) * lng_gap < 1.765e-15
			}
		if full {
			return S2LatLngRect.full()
		}
		lat_expansion = 9.0 * f64_epsilon
		lng_expansion = if (lng_gap <= 0.0) F64.pi else 0.0
		rect.expanded(S2LatLng.from_radians(lat_expansion, lng_expansion)).polar_closure()
	}

	## How far `bound` can exceed the true bounding rectangle: `10 * epsilon`
	## radians of latitude and `epsilon` of longitude.
	max_error_for_tests : () -> S2LatLng
	max_error_for_tests = || S2LatLng.from_radians(10.0 * f64_epsilon, f64_epsilon)
}

## `F64` machine epsilon.
f64_epsilon : F64
f64_epsilon = 2.220446049250313e-16

## Adds the vertex `b`, whose latitude and longitude are `b_lat_lng`.
add_internal : S2LatLngRectBounder, S2Point, S2LatLng -> S2LatLngRectBounder
add_internal = |bounder, b, b_lat_lng| {
	rect =
		if bounder.rect.is_empty() {
			bounder.rect.add_lat_lng(b_lat_lng)
		} else {
			edge_rect(bounder, b, b_lat_lng)
		}
	{ rect, a: b, a_lat_lng: b_lat_lng }
}

## The bound so far, extended by the edge from the previous vertex `a` to
## `b`.
##
## The edge's latitude range is that of its endpoints, unless the edge
## passes through the point of its great circle with the largest or the
## smallest latitude. That happens when `a` and `b` lie on opposite sides of
## the plane through the pole and the edge's normal.
edge_rect : S2LatLngRectBounder, S2Point, S2LatLng -> S2LatLngRect
edge_rect = |bounder, b, b_lat_lng| {
	a = bounder.a
	a_lat_lng = bounder.a_lat_lng
	# n = 2 * (a x b), computed so that it is accurate even when a and b are
	# nearly identical or nearly antipodal.
	n = (a - b).cross(a + b)
	n_norm = n.norm()
	if n_norm < 1.91346e-15 {
		# The points are nearly identical or nearly antipodal. For nearly
		# antipodal points the edge's direction is not known, so it could go
		# anywhere.
		return if a.dot(b) < 0.0 {
			S2LatLngRect.full()
		} else {
			bounder.rect.union(S2LatLngRect.from_point_pair(a_lat_lng, b_lat_lng))
		}
	}

	# The longitude range of an edge whose endpoints are nearly opposite in
	# longitude can be either way round, so it takes every longitude.
	lng_ab0 = S1Interval.from_point_pair(a_lat_lng.lng_radians(), b_lat_lng.lng_radians())
	lng_ab = if (lng_ab0.length() >= F64.pi - 2.0 * f64_epsilon) S1Interval.full() else lng_ab0

	lat_ab0 = R1Interval.from_point_pair(a_lat_lng.lat_radians(), b_lat_lng.lat_radians())

	# m is the normal of the plane through n and the pole. The signs of
	# m.a and m.b tell whether the edge passes the extreme latitude of its
	# great circle.
	m = n.cross(S2Point.new(0.0, 0.0, 1.0))
	m_a = m.dot(a)
	m_b = m.dot(b)
	m_error = 6.06638e-16 * n_norm + 6.83174e-31
	lat_ab =
		if m_a * m_b < 0.0 or m_a.abs() <= m_error or m_b.abs() <= m_error {
			# The extreme latitude of the great circle, padded for rounding.
			max_lat = (S2Math.atan2((n.x() * n.x() + n.y() * n.y()).sqrt(), n.z().abs()) + 3.0 * f64_epsilon).min(0.5 * F64.pi)
			# The latitude can change by at most the length of the edge, which
			# bounds how far the edge can go beyond its endpoints. That keeps
			# short edges from getting large bounds where max_lat is not
			# accurate.
			lat_budget_z = 0.5 * (a - b).norm() * max_lat.sin()
			lat_budget = 2.0 * ((1.0 + 4.0 * f64_epsilon) * lat_budget_z).min(1.0).asin()
			max_delta = 0.5 * (lat_budget - lat_ab0.length()) + f64_epsilon
			hi =
				if m_a <= m_error and m_b >= -m_error {
					max_lat.min(lat_ab0.hi() + max_delta)
				} else {
					lat_ab0.hi()
				}
			lo =
				if m_b <= m_error and m_a >= -m_error {
					(-max_lat).max(lat_ab0.lo() - max_delta)
				} else {
					lat_ab0.lo()
				}
			R1Interval.new(lo, hi)
		} else {
			lat_ab0
		}
	bounder.rect.union(S2LatLngRect.new(lat_ab, lng_ab))
}

# Bounds of chains of edges, against upstream's S2LatLngRectBounder. The
# fifth is the chain of upstream's AccuracyBug test, and the seventh has
# nearly antipodal endpoints.
expect {
	chain = [S2LatLng.from_degrees(10.0, -20.0).to_point(), S2LatLng.from_degrees(10.0, 20.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(0.1745329251994325, 0.18548633474659962), S1Interval.new(-0.3490658503988659, 0.3490658503988659))
}
expect {
	chain = [S2LatLng.from_degrees(-10.0, -20.0).to_point(), S2LatLng.from_degrees(-10.0, 20.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.18548633474659962, -0.1745329251994325), S1Interval.new(-0.3490658503988659, 0.3490658503988659))
}
expect {
	chain = [S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 90.0).to_point(), S2LatLng.from_degrees(45.0, 180.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-1.1102230246251565e-15, 0.7853981633974494), S1Interval.new(0.0, 3.141592653589793))
}
expect {
	chain = [S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 1.0).normalize()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(0.6154797086703869, 0.7853981633974494), S1Interval.new(-0.7853981633974483, 0.7853981633974483))
}
expect {
	chain = [S2Point.new(-0.9999999999999845, -1.2247195409833338e-16, 1.756190424895897e-07), S2Point.new(7.902057138966553e-08, -6.640712084290601e-10, 0.9999999999999969), S2Point.new(0.9999999999999768, -1.2246467991472876e-16, -5.911890857568904e-08)]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-5.911890901977955e-08, 1.5707963261308264), S1Interval.new(3.141592653589793, -1.224646799147316e-16))
}
expect {
	chain = [S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 4.440892098500626e-16), S1Interval.new(0.0, 0.0))
}
expect {
	chain = [S2Point.new(1.0, 0.0, 0.0).normalize(), S2Point.new(-1.0, 1.0e-16, 0.0).normalize()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
}
expect {
	# S2LatLng.from_point gives the latitude of the first point one unit in
	# the last place below upstream's, so the comparison allows for that.
	chain = [S2LatLng.from_degrees(30.0, 10.0).to_point(), S2LatLng.from_degrees(-40.0, -170.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound()
		|> S2LatLngRect.approx_eq(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 0.5235987755982993), S1Interval.new(-3.141592653589793, 3.141592653589793)), 1e-15)
}
expect {
	chain = [S2LatLng.from_degrees(89.0, 0.0).to_point(), S2LatLng.from_degrees(89.0, 180.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(1.5533430342749528, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
}
expect {
	chain = [S2LatLng.from_degrees(0.0, -179.0).to_point(), S2LatLng.from_degrees(0.0, 179.0).to_point()]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-6.777594528521669e-16, 6.777594528521669e-16), S1Interval.new(3.12413936106985, -3.12413936106985))
}
expect {
	chain = [S2LatLng.from_radians(0.1, 0.2), S2LatLng.from_radians(0.3, -0.4), S2LatLng.from_radians(-1.0, 2.0)]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_lat_lng(p)).bound() == S2LatLngRect.new(R1Interval.new(-1.1055744747094993, 0.30000000000000043), S1Interval.new(-0.4, 2.0))
}
expect {
	chain = [S2LatLng.from_radians(1.5, 0.0), S2LatLng.from_radians(1.5, 3.0)]
	chain.fold(S2LatLngRectBounder.new(), |acc, p| acc.add_lat_lng(p)).bound() == S2LatLngRect.new(R1Interval.new(1.4999999999999996, 1.5657800512275326), S1Interval.new(0.0, 3.0))
}
expect S2LatLngRectBounder.new().bound().is_empty()
# expand_for_subregions on the rectangles of upstream's ExpandForSubregions
# test.
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(3.0e-16, 1.0e-14), S1Interval.new(0.0, 3.141592653589793))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(9.0e-16, 1.0e-14), S1Interval.new(0.0, 3.141592653589793))) == S2LatLngRect.new(R1Interval.new(-1.0984014443252817e-15, 1.1998401444325282e-14), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(1.0e-16, 1.0e-14), S1Interval.new(7.0e-16, 3.141592653589793))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(3.0e-16, 1.0e-14), S1Interval.new(1.4e-15, 3.141592653589793))) == S2LatLngRect.new(R1Interval.new(-1.6984014443252818e-15, 1.1998401444325282e-14), S1Interval.new(1.4e-15, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(1.0e-100, 1.0e-14), S1Interval.new(1.4e-15, 3.141592653589793))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(1.0e-100, 1.0e-14), S1Interval.new(2.2e-15, 3.141592653589793))) == S2LatLngRect.new(R1Interval.new(-1.9984014443252818e-15, 1.1998401444325282e-14), S1Interval.new(2.2e-15, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.570796326794896), S1Interval.new(-1.0e-15, 0.0))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948934), S1Interval.new(-1.0e-15, 0.0))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948954), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948961, 1.5707963267948963), S1Interval.new(0.0, 1.0e-07))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948934, 1.5707963267948966), S1Interval.new(0.0, 1.0e-07))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948954, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948961, 1.5707963267948961), S1Interval.new(0.0, 1.5707963267948966))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948934), S1Interval.new(0.0, 1.5707963267948966))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948954), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963167948966), S1Interval.new(0.0, 3.1415925535897933))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707962267948965), S1Interval.new(0.0, 3.1415925535897933))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707962267948985), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267938965, 1.5707963267948966), S1Interval.new(-3.141492653589793, 0.0))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267848966, 1.5707963267948966), S1Interval.new(-3.141492653589793, 0.0))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(1.5, 1.5), S1Interval.new(-1.5707963267948966, 1.5707963267948963))) == S2LatLngRect.new(R1Interval.new(1.499999999999998, 1.500000000000002), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(1.5, 1.5), S1Interval.new(-1.5707963267948966, 1.570796326794896))) == S2LatLngRect.new(R1Interval.new(1.499999999999998, 1.500000000000002), S1Interval.new(-1.5707963267948966, 1.570796326794896))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(-1.5707963267948954, -1.5707963267948954), S1Interval.new(0.0, 0.0))) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, -1.5707963267948934), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.new(R1Interval.new(1.5707963267948954, 1.5707963267948954), S1Interval.new(0.0, 0.0))) == S2LatLngRect.new(R1Interval.new(1.5707963267948934, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.full()).is_full()
expect S2LatLngRectBounder.expand_for_subregions(S2LatLngRect.empty()).is_empty()
expect S2LatLngRectBounder.max_error_for_tests() == S2LatLng.from_radians(2.220446049250313e-15, 2.220446049250313e-16)

# The edges of upstream's MaxLatitudeSimple test: the extreme latitude at a
# vertex, inside the edge, and at a pole.
expect [S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, -1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.6154797086703878, 0.6154797086703878), S1Interval.new(-0.7853981633974483, 0.7853981633974483))
expect [S2Point.new(1.0, -1.0, 1.0).normalize(), S2Point.new(1.0, 1.0, -1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.6154797086703878, 0.6154797086703878), S1Interval.new(-0.7853981633974483, 0.7853981633974483))
expect [S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(0.6154797086703869, 0.7853981633974494), S1Interval.new(-0.7853981633974483, 0.7853981633974483))
expect [S2Point.new(1.0, -1.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(0.6154797086703869, 0.7853981633974494), S1Interval.new(-0.7853981633974483, 0.7853981633974483))
expect [S2Point.new(1.0, -1.0, -1.0).normalize(), S2Point.new(-1.0, -1.0, -1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.7853981633974494, -0.6154797086703869), S1Interval.new(-2.356194490192345, -0.7853981633974483))
expect [S2Point.new(-1.0, 1.0, -1.0).normalize(), S2Point.new(-1.0, -1.0, -1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.7853981633974494, -0.6154797086703869), S1Interval.new(2.356194490192345, -2.356194490192345))
expect [S2Point.new(0.3, 0.4, 1.0).normalize(), S2Point.new(-0.3, -0.4, 1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(1.10714871779409, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect [S2Point.new(0.3, 0.4, -1.0).normalize(), S2Point.new(-0.3, -0.4, -1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, -1.10714871779409), S1Interval.new(-3.141592653589793, 3.141592653589793))

# Edges whose extreme latitude is at an endpoint, where rounding decides
# whether the edge seems to pass it.
expect [S2LatLng.from_degrees(45.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 90.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 0.7853981633974494), S1Interval.new(0.0, 1.5707963267948966))
expect [S2LatLng.from_degrees(0.0, 90.0).to_point(), S2LatLng.from_degrees(45.0, 0.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 0.7853981633974494), S1Interval.new(0.0, 1.5707963267948966))
expect [S2LatLng.from_degrees(-45.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 90.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.7853981633974494, 4.440892098500626e-16), S1Interval.new(0.0, 1.5707963267948966))
expect [S2LatLng.from_degrees(0.0, -90.0).to_point(), S2LatLng.from_degrees(-45.0, 0.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.7853981633974494, 4.440892098500626e-16), S1Interval.new(-1.5707963267948966, 0.0))
# S2LatLng.from_point can differ from upstream by one unit in the last place
# here, so the comparison allows for that.
expect [S2LatLng.from_degrees(30.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, -90.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() |> S2LatLngRect.approx_eq(S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 0.5235987755982999), S1Interval.new(-1.5707963267948966, 0.0)), 1e-15)
# S2LatLng.from_point can differ from upstream by one unit in the last place
# here, so the comparison allows for that.
expect [S2LatLng.from_degrees(60.0, 10.0).to_point(), S2LatLng.from_degrees(0.0, 100.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() |> S2LatLngRect.approx_eq(S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 1.0471975511965987), S1Interval.new(0.17453292519943295, 1.7453292519943295)), 1e-15)
expect [S2LatLng.from_degrees(-20.0, -50.0).to_point(), S2LatLng.from_degrees(0.0, 40.0).to_point()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.34906585039886695, 4.440892098500626e-16), S1Interval.new(-0.8726646259971648, 0.6981317007977318))
expect [S2Point.new(1.0, 0.0, 1.0).normalize(), S2Point.new(0.0, 1.0, 0.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 0.7853981633974494), S1Interval.new(0.0, 1.5707963267948966))
expect [S2Point.new(0.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-4.440892098500626e-16, 0.7853981633974494), S1Interval.new(0.0, 1.5707963267948966))
expect [S2Point.new(1.0, 0.0, -1.0).normalize(), S2Point.new(0.0, -1.0, 0.0).normalize()].fold(S2LatLngRectBounder.new(), |acc, p| acc.add_point(p)).bound() == S2LatLngRect.new(R1Interval.new(-0.7853981633974494, 4.440892098500626e-16), S1Interval.new(-1.5707963267948966, 0.0))

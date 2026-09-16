import R1Interval
import S1Angle
import S1Interval
import S2Cap
import S2Cell
import S2CellId
import S2Coords
import S2Edge
import S2LatLng
import Internal/S2Math
import S2Point

## A rectangle in latitude-longitude space: a latitude interval crossed with a
## longitude interval.
##
## Longitude wraps, so the longitude interval may be inverted and the rectangle
## may span the antimeridian. Latitude does not wrap, and is clamped to the
## poles. A rectangle touching a pole covers every longitude there, which is
## what `polar_closure` makes explicit.
##
## This is the cheapest bound to compute and to test against, which is why it
## is the one S2 attaches to almost everything.
S2LatLngRect := { lat : R1Interval, lng : S1Interval }.{

	## The rectangle spanning the given latitude and longitude intervals, both
	## in radians.
	new : R1Interval, S1Interval -> S2LatLngRect
	new = |lat, lng| { lat: lat, lng: lng }

	## The rectangle with the given corners, which must satisfy `lo.lat <=
	## hi.lat`; longitude may wrap in either direction.
	from_bounds : S2LatLng, S2LatLng -> S2LatLngRect
	from_bounds = |lo, hi| {
		lat: R1Interval.new(lo.lat_radians(), hi.lat_radians()),
		lng: S1Interval.new(lo.lng_radians(), hi.lng_radians()),
	}

	## The smallest rectangle containing both positions.
	from_point_pair : S2LatLng, S2LatLng -> S2LatLngRect
	from_point_pair = |a, b| {
		lat: R1Interval.from_point_pair(a.lat_radians(), b.lat_radians()),
		lng: S1Interval.from_point_pair(a.lng_radians(), b.lng_radians()),
	}

	## The rectangle containing exactly one position.
	from_point : S2LatLng -> S2LatLngRect
	from_point = |p| {
		lat: R1Interval.from_point(p.lat_radians()),
		lng: S1Interval.from_point(p.lng_radians()),
	}

	## The rectangle of the given size centred on `center`.
	##
	## Latitude is clamped to the poles; a longitude size of 360 degrees or
	## more gives every longitude.
	from_center_size : S2LatLng, S2LatLng -> S2LatLngRect
	from_center_size = |center, size| S2LatLngRect.from_point(center).expanded(size * 0.5)

	empty : () -> S2LatLngRect
	empty = || { lat: R1Interval.empty(), lng: S1Interval.empty() }

	full : () -> S2LatLngRect
	full = || { lat: S2LatLngRect.full_lat(), lng: S1Interval.full() }

	## The full range of latitudes, pole to pole.
	full_lat : () -> R1Interval
	full_lat = || R1Interval.new(-0.5 * F64.pi, 0.5 * F64.pi)

	## The bounding rectangle of a cell.
	##
	## Tight to within about 2e-15 radians: the corners are computed exactly
	## and then padded by the worst-case error in the trigonometry.
	from_cell : S2Cell -> S2LatLngRect
	from_cell = |cell| {
		if cell.level() > 0 {
			uv = cell.bound_uv()
			u = uv.x().lo() + uv.x().hi()
			v = uv.y().lo() + uv.y().hi()

			# Pick the corner pair that spans the widest range of latitude.
			i = if S2Coords.u_axis(cell.face()).z() == 0.0 {
				if u < 0.0 {
					1
				} else {
					0
				}
			} else {
				if u > 0.0 {
					1
				} else {
					0
				}
			}
			j = if S2Coords.v_axis(cell.face()).z() == 0.0 {
				if v < 0.0 {
					1
				} else {
					0
				}
			} else {
				if v > 0.0 {
					1
				} else {
					0
				}
			}

			max_error = 4.440892098500626e-16
			cell_lat = R1Interval.from_point_pair(cell.latitude(i, j), cell.latitude(1 - i, 1 - j))
				.expanded(max_error)
				.intersection(S2LatLngRect.full_lat())
			if cell_lat.lo() == -0.5 * F64.pi or cell_lat.hi() == 0.5 * F64.pi {
				{ lat: cell_lat, lng: S1Interval.full() }
			} else {
				cell_lng = S1Interval.from_point_pair(
					cell.longitude(i, 1 - j),
					cell.longitude(1 - i, j),
				)
				{ lat: cell_lat, lng: cell_lng.expanded(max_error) }
			}
		} else {
			S2LatLngRect.face_rect(cell.face())
		}
	}

	## The bounding rectangle of a whole cube face, which is exact.
	face_rect : U64 -> S2LatLngRect
	face_rect = |face_index| {
		quarter = 0.25 * F64.pi
		third : F64
		third = 1.0 / 3.0
		pole_min_lat = third.sqrt().asin()
		if face_index == 0 {
			{ lat: R1Interval.new(-quarter, quarter), lng: S1Interval.new(-quarter, quarter) }
		} else if face_index == 1 {
			{
				lat: R1Interval.new(-quarter, quarter),
				lng: S1Interval.new(quarter, 3.0 * quarter),
			}
		} else if face_index == 2 {
			{ lat: R1Interval.new(pole_min_lat, 0.5 * F64.pi), lng: S1Interval.full() }
		} else if face_index == 3 {
			{
				lat: R1Interval.new(-quarter, quarter),
				lng: S1Interval.new(3.0 * quarter, -3.0 * quarter),
			}
		} else if face_index == 4 {
			{
				lat: R1Interval.new(-quarter, quarter),
				lng: S1Interval.new(-3.0 * quarter, -quarter),
			}
		} else {
			{ lat: R1Interval.new(-0.5 * F64.pi, -pole_min_lat), lng: S1Interval.full() }
		}
	}

	## The bounding rectangle of a cap.
	from_cap : S2Cap -> S2LatLngRect
	from_cap = |cap| {
		if cap.is_empty() {
			return S2LatLngRect.empty()
		}
		center = S2LatLng.from_point(cap.center())
		cap_angle = cap.radius_angle().radians()

		low = center.lat_radians() - cap_angle
		high = center.lat_radians() + cap_angle
		touches_south = low <= -0.5 * F64.pi
		touches_north = high >= 0.5 * F64.pi
		cap_lat = R1Interval.new(
			if touches_south {
				-0.5 * F64.pi
			} else {
				low
			},
			if touches_north {
				0.5 * F64.pi
			} else {
				high
			},
		)

		if touches_south or touches_north {
			return { lat: cap_lat, lng: S1Interval.full() }
		}

		# The law of sines for the right spherical triangle formed by the pole,
		# the cap centre, and the point where the cap touches a meridian.
		sin_a = cap.radius().sin()
		sin_c = center.lat_radians().cos()
		if sin_a > sin_c {
			{ lat: cap_lat, lng: S1Interval.full() }
		} else {
			angle_a = (sin_a / sin_c).asin()
			{
				lat: cap_lat,
				lng: S1Interval.new(
					S2Math.remainder(center.lng_radians() - angle_a, 2.0 * F64.pi),
					S2Math.remainder(center.lng_radians() + angle_a, 2.0 * F64.pi),
				),
			}
		}
	}

	lat : S2LatLngRect -> R1Interval
	lat = |r| r.lat

	lng : S2LatLngRect -> S1Interval
	lng = |r| r.lng

	lat_lo : S2LatLngRect -> S1Angle
	lat_lo = |r| S1Angle.from_radians(r.lat.lo())

	lat_hi : S2LatLngRect -> S1Angle
	lat_hi = |r| S1Angle.from_radians(r.lat.hi())

	lng_lo : S2LatLngRect -> S1Angle
	lng_lo = |r| S1Angle.from_radians(r.lng.lo())

	lng_hi : S2LatLngRect -> S1Angle
	lng_hi = |r| S1Angle.from_radians(r.lng.hi())

	## The south-west corner.
	lo : S2LatLngRect -> S2LatLng
	lo = |r| S2LatLng.from_radians(r.lat.lo(), r.lng.lo())

	## The north-east corner.
	hi : S2LatLngRect -> S2LatLng
	hi = |r| S2LatLng.from_radians(r.lat.hi(), r.lng.hi())

	## True when latitudes stay within the poles, longitudes stay normalized,
	## and the two intervals agree about being empty.
	is_valid : S2LatLngRect -> Bool
	is_valid = |r|
		r.lat.lo().abs() <= 0.5 * F64.pi
			and r.lat.hi().abs() <= 0.5 * F64.pi
				and r.lng.is_valid()
					and r.lat.is_empty() == r.lng.is_empty()

	is_empty : S2LatLngRect -> Bool
	is_empty = |r| r.lat.is_empty()

	is_full : S2LatLngRect -> Bool
	is_full = |r| r.lat == S2LatLngRect.full_lat() and r.lng.is_full()

	is_point : S2LatLngRect -> Bool
	is_point = |r| r.lat.lo() == r.lat.hi() and r.lng.lo() == r.lng.hi()

	center : S2LatLngRect -> S2LatLng
	center = |r| S2LatLng.from_radians(r.lat.center(), r.lng.center())

	## The rectangle's extent in latitude and longitude.
	size : S2LatLngRect -> S2LatLng
	size = |r| S2LatLng.from_radians(r.lat.length(), r.lng.length())

	## The `k`-th corner, counterclockwise from the south-west.
	vertex : S2LatLngRect, U64 -> S2LatLng
	vertex = |r, k| {
		i = k.shr_zf_wrap(1)
		S2LatLng.from_radians(r.lat.bound(i), r.lng.bound(i.bitwise_xor(k.bitwise_and(1))))
	}

	## The area of the rectangle in steradians.
	area : S2LatLngRect -> F64
	area = |r|
		if r.is_empty() {
			0.0
		} else {
			r.lng.length() * (r.lat.hi().sin() - r.lat.lo().sin())
		}

	contains_lat_lng : S2LatLngRect, S2LatLng -> Bool
	contains_lat_lng = |r, ll|
		r.lat.contains_point(ll.lat_radians()) and r.lng.contains_point(ll.lng_radians())

	contains_point : S2LatLngRect, S2Point -> Bool
	contains_point = |r, p| r.contains_lat_lng(S2LatLng.from_point(p))

	interior_contains_lat_lng : S2LatLngRect, S2LatLng -> Bool
	interior_contains_lat_lng = |r, ll|
		r.lat.interior_contains_point(ll.lat_radians())
			and r.lng.interior_contains_point(ll.lng_radians())

	interior_contains_point : S2LatLngRect, S2Point -> Bool
	interior_contains_point = |r, p| r.interior_contains_lat_lng(S2LatLng.from_point(p))

	contains_rect : S2LatLngRect, S2LatLngRect -> Bool
	contains_rect = |r, other|
		r.lat.contains_interval(other.lat) and r.lng.contains_interval(other.lng)

	interior_contains_rect : S2LatLngRect, S2LatLngRect -> Bool
	interior_contains_rect = |r, other|
		r.lat.interior_contains_interval(other.lat)
			and r.lng.interior_contains_interval(other.lng)

	intersects_rect : S2LatLngRect, S2LatLngRect -> Bool
	intersects_rect = |r, other| r.lat.intersects(other.lat) and r.lng.intersects(other.lng)

	interior_intersects_rect : S2LatLngRect, S2LatLngRect -> Bool
	interior_intersects_rect = |r, other|
		r.lat.interior_intersects(other.lat) and r.lng.interior_intersects(other.lng)

	union : S2LatLngRect, S2LatLngRect -> S2LatLngRect
	union = |r, other| { lat: r.lat.union(other.lat), lng: r.lng.union(other.lng) }

	intersection : S2LatLngRect, S2LatLngRect -> S2LatLngRect
	intersection = |r, other| {
		new_lat = r.lat.intersection(other.lat)
		new_lng = r.lng.intersection(other.lng)
		if new_lat.is_empty() or new_lng.is_empty() {
			S2LatLngRect.empty()
		} else {
			{ lat: new_lat, lng: new_lng }
		}
	}

	## The smallest rectangle containing this one and the position.
	add_lat_lng : S2LatLngRect, S2LatLng -> S2LatLngRect
	add_lat_lng = |r, ll| {
		lat: r.lat.add_point(ll.lat_radians()),
		lng: r.lng.add_point(ll.lng_radians()),
	}

	add_point : S2LatLngRect, S2Point -> S2LatLngRect
	add_point = |r, p| r.add_lat_lng(S2LatLng.from_point(p))

	## Widened by `margin.lat` in latitude and `margin.lng` in longitude.
	##
	## Latitude is clamped at the poles while longitude wraps. To grow by a
	## distance on the sphere rather than by coordinate ranges, use
	## `convolve_with_cap`.
	expanded : S2LatLngRect, S2LatLng -> S2LatLngRect
	expanded = |r, margin| {
		new_lat = r.lat.expanded(margin.lat_radians())
		new_lng = r.lng.expanded(margin.lng_radians())
		if new_lat.is_empty() or new_lng.is_empty() {
			S2LatLngRect.empty()
		} else {
			{ lat: new_lat.intersection(S2LatLngRect.full_lat()), lng: new_lng }
		}
	}

	## The rectangle with every longitude added if it touches a pole, since a
	## pole belongs to every meridian.
	polar_closure : S2LatLngRect -> S2LatLngRect
	polar_closure = |r|
		if r.lat.lo() == -0.5 * F64.pi or r.lat.hi() == 0.5 * F64.pi {
			{ lat: r.lat, lng: S1Interval.full() }
		} else {
			r
		}

	## The rectangle containing every point within `angle` of this one.
	##
	## This is the right way to grow a rectangle by a distance: unlike
	## `expanded`, the amount of longitude added grows towards the poles.
	convolve_with_cap : S2LatLngRect, S1Angle -> S2LatLngRect
	convolve_with_cap = |r, angle| {
		cap = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), angle)
		var $out = r
		for k in (0.U64).until(4) {
			vertex_cap = S2Cap.from_center_chord_angle(r.vertex(k).to_point(), cap.radius())
			$out = $out.union(S2LatLngRect.from_cap(vertex_cap))
		}
		$out
	}

	## The bounding cap of the rectangle.
	##
	## Picks whichever is smaller: a cap centred on the nearer pole, or one
	## centred on the rectangle's own centre.
	cap_bound : S2LatLngRect -> S2Cap
	cap_bound = |r| {
		if r.is_empty() {
			return S2Cap.empty()
		}
		(pole_z, pole_angle) =
			if r.lat.lo() + r.lat.hi() < 0.0 {
				(-1.0, 0.5 * F64.pi + r.lat.hi())
			} else {
				(1.0, 0.5 * F64.pi - r.lat.lo())
			}
		pole_cap = S2Cap.from_center_angle(
			S2Point.new(0.0, 0.0, pole_z),
			S1Angle.from_radians(pole_angle),
		)

		lng_span = r.lng.hi() - r.lng.lo()
		if S2Math.remainder(lng_span, 2.0 * F64.pi) >= 0.0 and lng_span < 2.0 * F64.pi {
			var $mid_cap = S2Cap.from_point(r.center().to_point())
			for k in (0.U64).until(4) {
				$mid_cap = $mid_cap.add_point(r.vertex(k).to_point())
			}
			if $mid_cap.height() < pole_cap.height() {
				$mid_cap
			} else {
				pole_cap
			}
		} else {
			pole_cap
		}
	}

	## True when the rectangle contains the whole cell.
	contains_cell : S2LatLngRect, S2Cell -> Bool
	contains_cell = |r, cell| r.contains_rect(S2LatLngRect.from_cell(cell))

	## True when the rectangle might meet the cell.
	##
	## Cheap but conservative: it compares bounding rectangles, so it can say
	## yes for a cell the rectangle misses. `intersects_cell` is exact.
	may_intersect_cell : S2LatLngRect, S2Cell -> Bool
	may_intersect_cell = |r, cell| r.intersects_rect(S2LatLngRect.from_cell(cell))

	## True when the rectangle and the cell really do share a point.
	intersects_cell : S2LatLngRect, S2Cell -> Bool
	intersects_cell = |r, cell| {
		if r.is_empty() {
			return Bool.False
		}
		if r.contains_point(cell.center_raw()) {
			return Bool.True
		}
		if cell.contains_point(r.center().to_point()) {
			return Bool.True
		}
		if !r.intersects_rect(S2LatLngRect.from_cell(cell)) {
			return Bool.False
		}

		cell_v = [cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3)]
		cell_ll = cell_v.map(S2LatLng.from_point)

		var $hit = Bool.False
		for i in (0.U64).until(4) {
			if r.contains_lat_lng(cell_ll.get(i) ?? S2LatLng.invalid()) {
				$hit = Bool.True
			}
			if cell.contains_point(r.vertex(i).to_point()) {
				$hit = Bool.True
			}
		}
		if $hit {
			return Bool.True
		}

		# The boundaries must cross, so test each cell edge against the four
		# sides of the rectangle.
		for i in (0.U64).until(4) {
			if !$hit {
				a = cell_v.get(i) ?? S2Point.zero()
				b = cell_v.get((i + 1) % 4) ?? S2Point.zero()
				a_ll = cell_ll.get(i) ?? S2LatLng.invalid()
				b_ll = cell_ll.get((i + 1) % 4) ?? S2LatLng.invalid()
				edge_lng = S1Interval.from_point_pair(a_ll.lng_radians(), b_ll.lng_radians())
				if r.lng.intersects(edge_lng) {
					if edge_lng.contains_point(r.lng.lo())
						and S2LatLngRect.intersects_lng_edge(a, b, r.lat, r.lng.lo()) {
						$hit = Bool.True
					}
					if edge_lng.contains_point(r.lng.hi())
						and S2LatLngRect.intersects_lng_edge(a, b, r.lat, r.lng.hi()) {
						$hit = Bool.True
					}
					if S2LatLngRect.intersects_lat_edge(a, b, r.lat.lo(), r.lng) {
						$hit = Bool.True
					}
					if S2LatLngRect.intersects_lat_edge(a, b, r.lat.hi(), r.lng) {
						$hit = Bool.True
					}
				}
			}
		}
		$hit
	}

	## True when the edge `ab` crosses the meridian segment at `lng` spanning
	## `lat`.
	intersects_lng_edge : S2Point, S2Point, R1Interval, F64 -> Bool
	intersects_lng_edge = |a, b, lat_span, meridian|
		S2Edge.simple_crossing(
			a,
			b,
			S2LatLng.from_radians(lat_span.lo(), meridian).to_point(),
			S2LatLng.from_radians(lat_span.hi(), meridian).to_point(),
		)

	## True when the edge `ab` crosses the parallel at `lat` spanning `lng`.
	intersects_lat_edge : S2Point, S2Point, F64, S1Interval -> Bool
	intersects_lat_edge = |a, b, parallel, lng_span| {
		# Build a frame whose z axis is normal to the edge's great circle, so
		# that the edge becomes an angle interval in that frame.
		z0 = a.robust_cross(b).normalize()
		z = if z0.z() < 0.0 {
			-z0
		} else {
			z0
		}
		y = z.robust_cross(S2Point.new(0.0, 0.0, 1.0)).normalize()
		x = y.cross(z)

		sin_lat = parallel.sin()
		if sin_lat.abs() >= x.z() {
			return Bool.False
		}
		cos_theta = sin_lat / x.z()
		sin_theta = (1.0 - cos_theta * cos_theta).sqrt()
		theta = S2Math.atan2(sin_theta, cos_theta)

		ab_theta = S1Interval.from_point_pair(
			S2Math.atan2(a.dot(y), a.dot(x)),
			S2Math.atan2(b.dot(y), b.dot(x)),
		)

		first =
			if ab_theta.contains_point(theta) {
				isect = x * cos_theta + y * sin_theta
				lng_span.contains_point(S2Math.atan2(isect.y(), isect.x()))
			} else {
				Bool.False
			}
		if first {
			return Bool.True
		}
		if ab_theta.contains_point(-theta) {
			isect = x * cos_theta - y * sin_theta
			lng_span.contains_point(S2Math.atan2(isect.y(), isect.x()))
		} else {
			Bool.False
		}
	}

	approx_eq : S2LatLngRect, S2LatLngRect, F64 -> Bool
	approx_eq = |r, other, max_error|
		r.lat.approx_eq(other.lat, max_error) and r.lng.approx_eq(other.lng, max_error)

	is_eq : S2LatLngRect, S2LatLngRect -> Bool
	is_eq = |a, b| a.lat == b.lat and a.lng == b.lng

	to_inspect : S2LatLngRect -> Str
	to_inspect = |r| "S2LatLngRect(${r.lo().to_inspect()}, ${r.hi().to_inspect()})"
}

expect S2LatLngRect.empty().is_empty()
expect S2LatLngRect.full().is_full()
expect S2LatLngRect.empty().is_valid()
expect S2LatLngRect.full().is_valid()
expect S2LatLngRect.empty().area() == 0.0
expect (S2LatLngRect.full().area() - 4.0 * F64.pi).abs() < 1e-14
expect S2LatLngRect.from_point(S2LatLng.from_degrees(10.0, 20.0)).is_point()
expect {
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, -20.0), S2LatLng.from_degrees(10.0, 20.0))
	r.center().approx_eq(S2LatLng.from_degrees(0.0, 0.0), 1e-15)
		and r.size().approx_eq(S2LatLng.from_degrees(20.0, 40.0), 1e-15)
}
expect {
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(10.0, 20.0))
	r.vertex(0) == S2LatLng.from_degrees(0.0, 0.0)
		and r.vertex(1) == S2LatLng.from_degrees(0.0, 20.0)
			and r.vertex(2) == S2LatLng.from_degrees(10.0, 20.0)
				and r.vertex(3) == S2LatLng.from_degrees(10.0, 0.0)
}
expect {
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, -20.0), S2LatLng.from_degrees(10.0, 20.0))
	r.contains_lat_lng(S2LatLng.from_degrees(0.0, 0.0))
		and !r.contains_lat_lng(S2LatLng.from_degrees(0.0, 30.0))
			and r.contains_point(S2LatLng.from_degrees(5.0, 5.0).to_point())
}
expect {
	# A rectangle spanning the antimeridian.
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, 170.0), S2LatLng.from_degrees(10.0, -170.0))
	r.contains_lat_lng(S2LatLng.from_degrees(0.0, 180.0))
		and r.contains_lat_lng(S2LatLng.from_degrees(0.0, -175.0))
			and !r.contains_lat_lng(S2LatLng.from_degrees(0.0, 0.0))
}
expect {
	a = S2LatLngRect.from_bounds(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(10.0, 10.0))
	b = S2LatLngRect.from_bounds(S2LatLng.from_degrees(5.0, 5.0), S2LatLng.from_degrees(15.0, 15.0))
	a.intersects_rect(b)
		and a.union(b) == S2LatLngRect.from_bounds(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(15.0, 15.0))
			and a.intersection(b) == S2LatLngRect.from_bounds(S2LatLng.from_degrees(5.0, 5.0), S2LatLng.from_degrees(10.0, 10.0))
}
expect {
	a = S2LatLngRect.from_bounds(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(10.0, 10.0))
	b = S2LatLngRect.from_bounds(S2LatLng.from_degrees(20.0, 20.0), S2LatLng.from_degrees(30.0, 30.0))
	!a.intersects_rect(b) and a.intersection(b).is_empty()
}
expect {
	r = S2LatLngRect.from_point(S2LatLng.from_degrees(0.0, 0.0))
	grown = r.expanded(S2LatLng.from_degrees(5.0, 5.0))
	grown.approx_eq(
		S2LatLngRect.from_bounds(S2LatLng.from_degrees(-5.0, -5.0), S2LatLng.from_degrees(5.0, 5.0)),
		1e-15,
	)
}
expect {
	# Expanding past a pole clamps rather than wrapping.
	r = S2LatLngRect.from_point(S2LatLng.from_degrees(85.0, 0.0))
	grown = r.expanded(S2LatLng.from_degrees(10.0, 10.0))
	grown.lat_hi().degrees() == 90.0
}
expect S2LatLngRect.from_center_size(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(20.0, 20.0))
	.approx_eq(
		S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, -10.0), S2LatLng.from_degrees(10.0, 10.0)),
		1e-15,
	)
expect {
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(80.0, 0.0), S2LatLng.from_degrees(90.0, 10.0))
	r.polar_closure().lng().is_full()
}
expect {
	# Every face rectangle bounds its own face cell.
	failures : U64
	failures = (0.U64).until(6).fold(
		0,
		|acc, f| {
			cell = S2Cell.from_face(f)
			rect = S2LatLngRect.from_cell(cell)
			if rect.contains_point(cell.center()) acc else acc + 1
		},
	)
	failures == 0
}
expect {
	# A cell's rectangle bound contains all four of its vertices.
	cell = S2Cell.from_cell_id(S2CellId.from_face(1).child(2).child(0).child(3))
	rect = S2LatLngRect.from_cell(cell)
	failures : U64
	failures = (0.U64).until(4).fold(
		0,
		|acc, k| if rect.contains_point(cell.vertex(k)) acc else acc + 1,
	)
	failures == 0
}
expect {
	cap = S2Cap.from_center_angle(S2Point.new(0.0, 0.0, 1.0), S1Angle.from_degrees(10.0))
	rect = S2LatLngRect.from_cap(cap)
	rect.lng().is_full() and (rect.lat_lo().degrees() - 80.0).abs() < 1e-12
}
expect {
	cap = S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(10.0))
	rect = S2LatLngRect.from_cap(cap)
	(rect.lat_hi().degrees() - 10.0).abs() < 1e-12 and (rect.lng_hi().degrees() - 10.0).abs() < 1e-12
}
expect S2LatLngRect.from_cap(S2Cap.empty()).is_empty()
expect {
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, -10.0), S2LatLng.from_degrees(10.0, 10.0))
	cap = r.cap_bound()
	failures : U64
	failures = (0.U64).until(4).fold(
		0,
		|acc, k| if cap.contains_point(r.vertex(k).to_point()) acc else acc + 1,
	)
	failures == 0
}
expect S2LatLngRect.empty().cap_bound().is_empty()
expect S2LatLngRect.full().contains_cell(S2Cell.from_face(0))
expect S2LatLngRect.full().may_intersect_cell(S2Cell.from_face(0))
expect S2LatLngRect.full().intersects_cell(S2Cell.from_face(0))
expect !S2LatLngRect.empty().intersects_cell(S2Cell.from_face(0))
expect {
	# A small rectangle near the centre of a face meets that face but not the
	# opposite one.
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-1.0, -1.0), S2LatLng.from_degrees(1.0, 1.0))
	r.intersects_cell(S2Cell.from_face(0)) and !r.intersects_cell(S2Cell.from_face(3))
}
expect {
	r = S2LatLngRect.from_point(S2LatLng.from_degrees(0.0, 0.0))
	grown = r.convolve_with_cap(S1Angle.from_degrees(5.0))
	grown.contains_lat_lng(S2LatLng.from_degrees(4.0, 0.0))
		and grown.contains_lat_lng(S2LatLng.from_degrees(0.0, 4.0))
}

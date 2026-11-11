import R1Interval
import S1Angle
import S1ChordAngle
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

	## The rectangle that contains no position.
	empty : () -> S2LatLngRect
	empty = || { lat: R1Interval.empty(), lng: S1Interval.empty() }

	## The rectangle that contains every position.
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
			cell_lat = R1Interval.from_point_pair(cell_latitude(cell, i, j), cell_latitude(cell, 1 - i, 1 - j))
				.expanded(max_error)
				.intersection(S2LatLngRect.full_lat())
			if cell_lat.lo() == -0.5 * F64.pi or cell_lat.hi() == 0.5 * F64.pi {
				{ lat: cell_lat, lng: S1Interval.full() }
			} else {
				cell_lng = S1Interval.from_point_pair(
					cell_longitude(cell, i, 1 - j),
					cell_longitude(cell, 1 - i, j),
				)
				{ lat: cell_lat, lng: cell_lng.expanded(max_error) }
			}
		} else {
			face_rect(cell.face())
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

	## The interval of latitudes, in radians.
	lat : S2LatLngRect -> R1Interval
	lat = |r| r.lat

	## The interval of longitudes, in radians. It wraps through +/-pi when it
	## is inverted.
	lng : S2LatLngRect -> S1Interval
	lng = |r| r.lng

	## The lowest latitude.
	lat_lo : S2LatLngRect -> S1Angle
	lat_lo = |r| S1Angle.from_radians(r.lat.lo())

	## The highest latitude.
	lat_hi : S2LatLngRect -> S1Angle
	lat_hi = |r| S1Angle.from_radians(r.lat.hi())

	## The longitude where the rectangle starts. It is greater than `lng_hi`
	## when the rectangle wraps through +/-pi.
	lng_lo : S2LatLngRect -> S1Angle
	lng_lo = |r| S1Angle.from_radians(r.lng.lo())

	## The longitude where the rectangle ends.
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

	## True when the rectangle contains no position.
	is_empty : S2LatLngRect -> Bool
	is_empty = |r| r.lat.is_empty()

	## True when the rectangle covers every latitude and every longitude.
	is_full : S2LatLngRect -> Bool
	is_full = |r| r.lat == S2LatLngRect.full_lat() and r.lng.is_full()

	## True when the rectangle is a single position.
	is_point : S2LatLngRect -> Bool
	is_point = |r| r.lat.lo() == r.lat.hi() and r.lng.lo() == r.lng.hi()

	## The center of the rectangle. Undefined for an empty rectangle.
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

	## True when the position is in the rectangle or on its boundary.
	contains_lat_lng : S2LatLngRect, S2LatLng -> Bool
	contains_lat_lng = |r, ll|
		r.lat.contains_point(ll.lat_radians()) and r.lng.contains_point(ll.lng_radians())

	## True when the point is in the rectangle or on its boundary.
	contains_point : S2LatLngRect, S2Point -> Bool
	contains_point = |r, p| r.contains_lat_lng(S2LatLng.from_point(p))

	## True when the position is strictly inside the rectangle.
	interior_contains_lat_lng : S2LatLngRect, S2LatLng -> Bool
	interior_contains_lat_lng = |r, ll|
		r.lat.interior_contains_point(ll.lat_radians())
			and r.lng.interior_contains_point(ll.lng_radians())

	## True when the point is strictly inside the rectangle.
	interior_contains_point : S2LatLngRect, S2Point -> Bool
	interior_contains_point = |r, p| r.interior_contains_lat_lng(S2LatLng.from_point(p))

	## True when every position of `other` is in this rectangle. Every
	## rectangle contains an empty rectangle.
	contains_rect : S2LatLngRect, S2LatLngRect -> Bool
	contains_rect = |r, other|
		r.lat.contains_interval(other.lat) and r.lng.contains_interval(other.lng)

	## True when every position of `other` is strictly inside this rectangle.
	## Every rectangle contains an empty rectangle.
	interior_contains_rect : S2LatLngRect, S2LatLngRect -> Bool
	interior_contains_rect = |r, other|
		r.lat.interior_contains_interval(other.lat)
			and r.lng.interior_contains_interval(other.lng)

	## True when the two rectangles share at least one position.
	intersects_rect : S2LatLngRect, S2LatLngRect -> Bool
	intersects_rect = |r, other| r.lat.intersects(other.lat) and r.lng.intersects(other.lng)

	## True when the interior of this rectangle shares at least one position
	## with `other`.
	interior_intersects_rect : S2LatLngRect, S2LatLngRect -> Bool
	interior_intersects_rect = |r, other|
		r.lat.interior_intersects(other.lat) and r.lng.interior_intersects(other.lng)

	## The smallest rectangle that contains both rectangles.
	union : S2LatLngRect, S2LatLngRect -> S2LatLngRect
	union = |r, other| { lat: r.lat.union(other.lat), lng: r.lng.union(other.lng) }

	## The largest rectangle in both rectangles. The result is empty when they
	## do not overlap.
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

	## The smallest rectangle that contains this rectangle and the point.
	add_point : S2LatLngRect, S2Point -> S2LatLngRect
	add_point = |r, p| r.add_lat_lng(S2LatLng.from_point(p))

	## Widened by `margin.lat` in latitude and `margin.lng` in longitude.
	##
	## Latitude is clamped at the poles while longitude wraps. To grow by a
	## distance on the sphere rather than by coordinate ranges, use
	## `expanded_by_distance`.
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
	##
	## A negative `angle` shrinks the rectangle instead, to the rectangle that
	## holds every point whose distance to the outside is at least `-angle`.
	## The result is empty when nothing is left. A rectangle with a full
	## longitude interval keeps the pole it touches, as that pole has no
	## boundary.
	expanded_by_distance : S2LatLngRect, S1Angle -> S2LatLngRect
	expanded_by_distance = |r, angle| {
		if angle.radians() >= 0.0 {
			# The union of the bounds of a cap around each vertex, and of the
			# rectangle itself, which matters for very large rectangles.
			radius = S1ChordAngle.from_angle(angle)
			var $out = r
			for k in (0.U64).until(4) {
				vertex_cap = S2Cap.from_center_chord_angle(r.vertex(k).to_point(), radius)
				$out = $out.union(S2LatLngRect.from_cap(vertex_cap))
			}
			$out
		} else {
			half_pi = 0.5 * F64.pi
			distance = angle.radians()
			lat_result = R1Interval.new(
				if r.lat.lo() <= -half_pi and r.lng.is_full() {
					-half_pi
				} else {
					r.lat.lo() - distance
				},
				if r.lat.hi() >= half_pi and r.lng.is_full() {
					half_pi
				} else {
					r.lat.hi() + distance
				},
			)
			if lat_result.is_empty() {
				return S2LatLngRect.empty()
			}
			# The cap occupies its largest longitude interval at the latitude of
			# greatest magnitude. The law of sines for spherical triangles gives
			# that interval, and a cap that reaches the pole spans a quarter turn.
			max_abs_lat = (-lat_result.lo()).max(lat_result.hi())
			sin_a = (-distance).sin()
			sin_c = max_abs_lat.cos()
			max_lng_margin = if (sin_a < sin_c) (sin_a / sin_c).asin() else half_pi
			lng_result = r.lng.expanded(-max_lng_margin)
			if lng_result.is_empty() {
				S2LatLngRect.empty()
			} else {
				{ lat: lat_result, lng: lng_result }
			}
		}
	}

	## True when the longitude interval wraps through 180 degrees, so that
	## `lng_lo > lng_hi`.
	is_inverted : S2LatLngRect -> Bool
	is_inverted = |r| r.lng.is_inverted()

	## The true centroid of the rectangle, multiplied by its area.
	##
	## The result is not unit length. Scaling by the area makes centroids
	## of several shapes add up to the centroid of their union. The empty
	## rectangle gives the zero vector.
	centroid : S2LatLngRect -> S2Point
	centroid = |r| {
		if r.is_empty() {
			return S2Point.zero()
		}
		# Slices of constant thickness have equal area, so z is the middle
		# of the z range. In each slice the arc's centroid is at distance
		# r * sin(alpha) / alpha from the z axis, where alpha is half the
		# longitude span. Integrating over z and scaling by the area
		# 2 * alpha * (z2 - z1) gives the formulas below.
		low = r.lat_lo().sin_cos()
		high = r.lat_hi().sin_cos()
		z1 = low.sin
		r1 = low.cos
		z2 = high.sin
		r2 = high.cos
		alpha = 0.5 * r.lng.length()
		radial = alpha.sin() * (r2 * z2 - r1 * z1 + r.lat.length())
		z = alpha * (z2 + z1) * (z2 - z1)
		mid = S1Angle.from_radians(r.lng.center()).sin_cos()
		S2Point.new(radial * mid.cos, radial * mid.sin, z)
	}

	## True when the edge from `v0` to `v1` crosses the boundary of the
	## rectangle, which is made of up to two meridian segments and two
	## parallels. A side that is a pole or that the full longitude interval
	## removes does not count.
	boundary_intersects : S2LatLngRect, S2Point, S2Point -> Bool
	boundary_intersects = |r, v0, v1| {
		if r.is_empty() {
			return Bool.False
		}
		meridians =
			!r.lng.is_full()
				and (intersects_lng_edge(v0, v1, r.lat, r.lng.lo()) or intersects_lng_edge(v0, v1, r.lat, r.lng.hi()))
		meridians
			or (r.lat.lo() != -0.5 * F64.pi and intersects_lat_edge(v0, v1, r.lat.lo(), r.lng))
			or (r.lat.hi() != 0.5 * F64.pi and intersects_lat_edge(v0, v1, r.lat.hi(), r.lng))
	}

	## The distance between the closest points of two rectangles, which is
	## zero when they meet. Both must be non-empty.
	distance_to_rect : S2LatLngRect, S2LatLngRect -> S1Angle
	distance_to_rect = |a, b| {
		if a.lng.intersects(b.lng) {
			if a.lat.intersects(b.lat) {
				return S1Angle.from_radians(0.0)
			}
			# The shortest path runs along a meridian, from the top of the
			# lower rectangle to the bottom of the higher one.
			return if a.lat.lo() > b.lat.hi() {
				a.lat_lo() - b.lat_hi()
			} else {
				b.lat_lo() - a.lat_hi()
			}
		}
		# Otherwise the closest points are on the pair of meridian sides that
		# are nearest in longitude, and at least one of them is an endpoint.
		lo_hi = S1Interval.from_point_pair(a.lng.lo(), b.lng.hi())
		hi_lo = S1Interval.from_point_pair(a.lng.hi(), b.lng.lo())
		(a_lng, b_lng) =
			if lo_hi.length() < hi_lo.length() {
				(a.lng.lo(), b.lng.hi())
			} else {
				(a.lng.hi(), b.lng.lo())
			}
		a_lo = S2LatLng.from_radians(a.lat.lo(), a_lng).to_point()
		a_hi = S2LatLng.from_radians(a.lat.hi(), a_lng).to_point()
		b_lo = S2LatLng.from_radians(b.lat.lo(), b_lng).to_point()
		b_hi = S2LatLng.from_radians(b.lat.hi(), b_lng).to_point()
		edge_angle(a_lo, b_lo, b_hi)
			.min(edge_angle(a_hi, b_lo, b_hi).min(edge_angle(b_lo, a_lo, a_hi).min(edge_angle(b_hi, a_lo, a_hi))))
	}

	## The distance from the point to the closest point of the rectangle,
	## which must be non-empty. Zero when the rectangle contains the point.
	distance_to_lat_lng : S2LatLngRect, S2LatLng -> S1Angle
	distance_to_lat_lng = |r, p| {
		if r.lng.contains_point(p.lng_radians()) {
			return S1Angle.from_radians((0.0).max((p.lat_radians() - r.lat.hi()).max(r.lat.lo() - p.lat_radians())))
		}
		# Otherwise the closest point is on the nearer meridian side.
		towards_hi = S1Interval.new(r.lng.hi(), r.lng.complement_center())
		side_lng = if (towards_hi.contains_point(p.lng_radians())) r.lng.hi() else r.lng.lo()
		side_lo = S2LatLng.from_radians(r.lat.lo(), side_lng).to_point()
		side_hi = S2LatLng.from_radians(r.lat.hi(), side_lng).to_point()
		edge_angle(p.to_point(), side_lo, side_hi)
	}

	## The directed Hausdorff distance from this rectangle to `other`: the
	## largest distance from a point of this rectangle to its closest point
	## of `other`.
	##
	## Zero when this rectangle is empty, and 180 degrees when only `other`
	## is.
	directed_hausdorff_distance : S2LatLngRect, S2LatLngRect -> S1Angle
	directed_hausdorff_distance = |r, other| {
		if r.is_empty() {
			S1Angle.from_radians(0.0)
		} else if other.is_empty() {
			S1Angle.from_radians(F64.pi)
		} else {
			lng_distance = r.lng.directed_hausdorff_distance(other.lng)
			directed_hausdorff_between_meridians(lng_distance, r.lat, other.lat)
		}
	}

	## The Hausdorff distance between the rectangles: the larger of the two
	## directed distances.
	hausdorff_distance : S2LatLngRect, S2LatLngRect -> S1Angle
	hausdorff_distance = |r, other|
		r.directed_hausdorff_distance(other).max(other.directed_hausdorff_distance(r))

	## The bounding cap of the rectangle.
	##
	## Picks whichever is smaller: a cap centred on the nearer pole, or one
	## centred on the rectangle's own centre. A rectangle wider than 180
	## degrees of longitude always gets the pole cap.
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
			S1Angle.from_radians((1.0 + 2.0 * 2.220446049250313e-16) * pole_angle),
		)

		# Up to 180 degrees of longitude, the cap is largest at one of the
		# vertices. A wider rectangle always gets the pole cap.
		if r.lng.length() <= F64.pi {
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
						and intersects_lng_edge(a, b, r.lat, r.lng.lo()) {
						$hit = Bool.True
					}
					if edge_lng.contains_point(r.lng.hi())
						and intersects_lng_edge(a, b, r.lat, r.lng.hi()) {
						$hit = Bool.True
					}
					if intersects_lat_edge(a, b, r.lat.lo(), r.lng) {
						$hit = Bool.True
					}
					if intersects_lat_edge(a, b, r.lat.hi(), r.lng) {
						$hit = Bool.True
					}
				}
			}
		}
		$hit
	}

	## True when the latitude and longitude intervals are each within
	## `max_error` of the other rectangle.
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
			if (rect.contains_point(cell.center())) acc else acc + 1
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
		|acc, k| if (rect.contains_point(cell.vertex(k))) acc else acc + 1,
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
		|acc, k| if (cap.contains_point(r.vertex(k).to_point())) acc else acc + 1,
	)
	failures == 0
}
expect S2LatLngRect.empty().cap_bound().is_empty()
expect {
	# A rectangle 190 degrees wide. The cap around its centre has a radius of
	# about 94.9 degrees and the pole cap one of 100 degrees, but a rectangle
	# wider than 180 degrees always gets the pole cap.
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, -95.0), S2LatLng.from_degrees(10.0, 95.0))
	r.cap_bound().center() == S2Point.new(0.0, 0.0, 1.0)
}
expect {
	# The pole cap is padded, so its radius exceeds the exact polar distance.
	r = S2LatLngRect.new(R1Interval.new(0.5, 1.0), S1Interval.full())
	r.cap_bound().radius_angle().radians() > 0.5 * F64.pi - 0.5
}
expect {
	# The level 0 polar bound is padded below the exact latitude by both the
	# constant adjustment and the final expansion, about 3.3e-16 in all.
	lo = S2LatLngRect.from_cell(S2Cell.from_face(2)).lat.lo()
	third : F64
	third = 1.0 / 3.0
	third.sqrt().asin() - lo > 3.0e-16
}
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
	grown = r.expanded_by_distance(S1Angle.from_degrees(5.0))
	grown.contains_lat_lng(S2LatLng.from_degrees(4.0, 0.0))
		and grown.contains_lat_lng(S2LatLng.from_degrees(0.0, 4.0))
}
expect {
	# A negative distance shrinks the rectangle. Latitude shrinks by exactly
	# the distance. Longitude shrinks by asin(sin(2 deg) / cos(8 deg)), the
	# half width of a 2 degree cap at the latitude of greatest magnitude.
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(-10.0, -10.0), S2LatLng.from_degrees(10.0, 10.0))
	shrunk = r.expanded_by_distance(S1Angle.from_degrees(-2.0))
	margin = 0.0352497734976641
	ten_degrees = 10.0 * (F64.pi / 180.0)
	(shrunk.lat().lo() + 8.0 * (F64.pi / 180.0)).abs() < 1e-15
		and (shrunk.lat().hi() - 8.0 * (F64.pi / 180.0)).abs() < 1e-15
		and (shrunk.lng().lo() - (margin - ten_degrees)).abs() < 1e-14
		and (shrunk.lng().hi() - (ten_degrees - margin)).abs() < 1e-14
}
expect {
	# Shrinking by more than half the height leaves nothing.
	r = S2LatLngRect.from_bounds(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.0, 10.0))
	r.expanded_by_distance(S1Angle.from_degrees(-1.0)).is_empty()
}
expect {
	# A rectangle with every longitude has no boundary at the pole it touches.
	r = S2LatLngRect.new(R1Interval.new(80.0 * (F64.pi / 180.0), 0.5 * F64.pi), S1Interval.full())
	shrunk = r.expanded_by_distance(S1Angle.from_degrees(-5.0))
	shrunk.lng().is_full()
		and shrunk.lat().hi() == 0.5 * F64.pi
		and (shrunk.lat().lo() - 85.0 * (F64.pi / 180.0)).abs() < 1e-15
}
expect {
	# The meridian segment at longitude 0 from the equator to latitude 45
	# degrees is crossed by an edge running east to west across latitude 20.
	a = S2LatLng.from_degrees(20.0, -5.0).to_point()
	b = S2LatLng.from_degrees(20.0, 5.0).to_point()
	lat_span = R1Interval.new(0.0, 0.25 * F64.pi)
	intersects_lng_edge(a, b, lat_span, 0.0)
		and !intersects_lng_edge(a, b, lat_span, 0.5)
}

## The bounding rectangle of a whole cube face, which is exact.
face_rect : U64 -> S2LatLngRect
face_rect = |face_index| {
	quarter = 0.25 * F64.pi
	third : F64
	third = 1.0 / 3.0
	# The error in this calculation is at most half an epsilon.
	pole_min_lat = third.sqrt().asin() - 0.5 * 2.220446049250313e-16
	bound = if face_index == 0 {
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
	# Allow for the error when a contained point is converted to latitude.
	S2LatLngRect.expanded(bound, S2LatLng.from_radians(2.220446049250313e-16, 0.0))
}

## True when the edge `ab` crosses the meridian segment at `lng` spanning
## `lat`.
intersects_lng_edge : S2Point, S2Point, R1Interval, F64 -> Bool
intersects_lng_edge = |a, b, lat_span, meridian|
	S2Edge.crossing_sign(
		a,
		b,
		S2LatLng.from_radians(lat_span.lo(), meridian).to_point(),
		S2LatLng.from_radians(lat_span.hi(), meridian).to_point(),
	) > 0

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

## The latitude in radians of the corner of `cell` at `(u_i, v_j)`.
cell_latitude : S2Cell, U64, U64 -> F64
cell_latitude = |cell, i, j|
	S2LatLng.latitude(
		S2Coords.face_uv_to_xyz(cell.face(), cell.bound_uv().x().bound(i), cell.bound_uv().y().bound(j)),
	)
		.radians()

## The longitude in radians of the corner of `cell` at `(u_i, v_j)`.
cell_longitude : S2Cell, U64, U64 -> F64
cell_longitude = |cell, i, j|
	S2LatLng.longitude(
		S2Coords.face_uv_to_xyz(cell.face(), cell.bound_uv().x().bound(i), cell.bound_uv().y().bound(j)),
	)
		.radians()

## The distance from `x` to the edge `ab`, as an angle.
edge_angle : S2Point, S2Point, S2Point -> S1Angle
edge_angle = |x, a, b| S2Edge.distance_to_edge(x, a, b).to_angle()

## The directed Hausdorff distance from a meridian segment spanning `a`
## to one spanning `b`, `lng_diff` radians of longitude away.
##
## By symmetry, `a` is at longitude 0 and `b` at `lng_diff`. The furthest
## point of `a` from `b` is an endpoint of `a`, or where `a` meets the
## equator (for `lng_diff` up to 90 degrees), or where `a` meets the
## bisector of `b`, or the point of `a` furthest from one endpoint of `b`.
directed_hausdorff_between_meridians : F64, R1Interval, R1Interval -> S1Angle
directed_hausdorff_between_meridians = |lng_diff, a, b| {
	if lng_diff == 0.0 {
		return S1Angle.from_radians(a.directed_hausdorff_distance(b))
	}
	b_lng = lng_diff
	b_lo = S2LatLng.from_radians(b.lo(), b_lng).to_point()
	b_hi = S2LatLng.from_radians(b.hi(), b_lng).to_point()
	a_lo = S2LatLng.from_radians(a.lo(), 0.0).to_point()
	a_hi = S2LatLng.from_radians(a.hi(), 0.0).to_point()
	endpoints = edge_angle(a_lo, b_lo, b_hi).max(edge_angle(a_hi, b_lo, b_hi))
	if lng_diff <= 0.5 * F64.pi {
		if a.contains_point(0.0) and b.contains_point(0.0) {
			endpoints.max(S1Angle.from_radians(lng_diff))
		} else {
			endpoints
		}
	} else {
		p = bisector_intersection(b, b_lng)
		p_lat = S2LatLng.latitude(p).radians()
		with_bisector = if (a.contains_point(p_lat)) endpoints.max(p.angle_to(b_lo)) else endpoints
		below =
			if p_lat > a.lo() {
				with_bisector.max(interior_max_distance(R1Interval.new(a.lo(), p_lat.min(a.hi())), b_lo))
			} else {
				with_bisector
			}
		if p_lat < a.hi() {
			below.max(interior_max_distance(R1Interval.new(p_lat.max(a.lo()), a.hi()), b_hi))
		} else {
			below
		}
	}
}

## Where longitude 0 meets the bisector of the meridian segment at `lng`
## spanning `lat`. Not unit length.
bisector_intersection : R1Interval, F64 -> S2Point
bisector_intersection = |lat, lng_signed| {
	lng = lng_signed.abs()
	lat_center = lat.center()
	# A vector orthogonal to the bisector of the segment.
	ortho_bisector =
		if lat_center >= 0.0 {
			S2LatLng.from_radians(lat_center - 0.5 * F64.pi, lng)
		} else {
			S2LatLng.from_radians(-lat_center - 0.5 * F64.pi, lng - F64.pi)
		}
	# (0, -1, 0) is orthogonal to longitude 0.
	S2Point.new(0.0, -1.0, 0.0).robust_cross(ortho_bisector.to_point())
}

## The largest distance from `b` to the segment of longitude 0 spanning
## `a_lat`, when that maximum is interior to the segment, and `-1` radians
## otherwise.
interior_max_distance : R1Interval, S2Point -> S1Angle
interior_max_distance = |a_lat, b| {
	# Longitude 0 is in the plane y = 0. With b.x >= 0 the maximum is not
	# interior.
	if a_lat.is_empty() or b.x() >= 0.0 {
		return S1Angle.from_radians(-1.0)
	}
	# The antipode of b projected onto that plane is the furthest point.
	furthest = S2Point.new(-b.x(), 0.0, -b.z()).normalize()
	if a_lat.interior_contains_point(S2LatLng.latitude(furthest).radians()) {
		b.angle_to(furthest)
	} else {
		S1Angle.from_radians(-1.0)
	}
}

# Centroids from upstream's S2LatLngRect::GetCentroid.
expect S2LatLngRect.new(R1Interval.new(0.0, 0.17453292519943295), S1Interval.new(0.0, 0.17453292519943295)).centroid() == S2Point.new(0.030001455855351272, 0.00262478727661669, 0.002631405826336722)
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793)).centroid() == S2Point.new(3.8473413874435795e-16, 0.0, 0.0)
expect S2LatLngRect.new(R1Interval.new(0.5235987755982988, 1.0471975511965976), S1Interval.new(2.9670597283903604, -2.9670597283903604)).centroid() == S2Point.new(-0.0909219732112805, 1.1134730346535606e-17, 0.08726646259971638)
expect S2LatLngRect.new(R1Interval.new(-0.17453292519943295, -0.08726646259971647), S1Interval.new(0.3490658503988659, 1.5707963267948966)).centroid() == S2Point.new(0.05640612773494667, 0.0805562988927052, -0.013779632996876751)
expect S2LatLngRect.new(R1Interval.new(1.3962634015954636, 1.5707963267948966), S1Interval.new(-0.17453292519943295, 0.17453292519943295)).centroid() == S2Point.new(0.0006117370968178508, 0.0, 0.005262811652673459)
expect S2LatLngRect.new(R1Interval.new(-0.7853981633974483, 0.7853981633974483), S1Interval.new(0.0, 0.0)).centroid() == S2Point.new(0.0, 0.0, 0.0)
expect S2LatLngRect.empty().centroid() == S2Point.zero()
# The cases of upstream's BoundaryIntersects tests.
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(1.7453292519943295, 2.0943951023931953)).boundary_intersects(S2LatLng.from_degrees(60.0, 60.0).to_point(), S2LatLng.from_degrees(90.0, 60.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(1.7453292519943295, 2.0943951023931953)).boundary_intersects(S2LatLng.from_degrees(-60.0, 110.0).to_point(), S2LatLng.from_degrees(60.0, 110.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(1.7453292519943295, 2.0943951023931953)).boundary_intersects(S2LatLng.from_degrees(-60.0, 95.0).to_point(), S2LatLng.from_degrees(60.0, 110.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(1.7453292519943295, 2.0943951023931953)).boundary_intersects(S2LatLng.from_degrees(60.0, 115.0).to_point(), S2LatLng.from_degrees(80.0, 125.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793)).boundary_intersects(S2LatLng.from_degrees(60.0, -180.0).to_point(), S2LatLng.from_degrees(90.0, -180.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793)).boundary_intersects(S2LatLng.from_degrees(60.0, -170.0).to_point(), S2LatLng.from_degrees(60.0, 170.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793)).boundary_intersects(S2LatLng.from_degrees(-10.0, -180.0).to_point(), S2LatLng.from_degrees(10.0, -180.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 0.0), S1Interval.new(-3.141592653589793, 3.141592653589793)).boundary_intersects(S2LatLng.from_degrees(-90.0, -180.0).to_point(), S2LatLng.from_degrees(-60.0, -180.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 0.0), S1Interval.new(-3.141592653589793, 3.141592653589793)).boundary_intersects(S2LatLng.from_degrees(-60.0, -170.0).to_point(), S2LatLng.from_degrees(-60.0, 170.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 0.0), S1Interval.new(-3.141592653589793, 3.141592653589793)).boundary_intersects(S2LatLng.from_degrees(-10.0, -180.0).to_point(), S2LatLng.from_degrees(10.0, -180.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(25.0, 160.0).to_point(), S2LatLng.from_degrees(25.0, 180.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(25.0, -160.0).to_point(), S2LatLng.from_degrees(25.0, -180.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(15.0, 175.0).to_point(), S2LatLng.from_degrees(30.0, 175.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(45.0, 175.0).to_point(), S2LatLng.from_degrees(30.0, 175.0).to_point()) == Bool.True
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(25.0, -20.0).to_point(), S2LatLng.from_degrees(25.0, 0.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(25.0, 20.0).to_point(), S2LatLng.from_degrees(25.0, 0.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(15.0, -5.0).to_point(), S2LatLng.from_degrees(30.0, -5.0).to_point()) == Bool.False
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).boundary_intersects(S2LatLng.from_degrees(45.0, -5.0).to_point(), S2LatLng.from_degrees(30.0, -5.0).to_point()) == Bool.False
expect !S2LatLngRect.empty().boundary_intersects(S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0))
expect !S2LatLngRect.full().boundary_intersects(S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0))
# The cases of upstream's ExpandedByDistance tests.
expect S2LatLngRect.new(R1Interval.new(0.0, 0.0), S1Interval.new(2.9670597283903604, -2.9670597283903604)).expanded_by_distance(S1Angle.from_radians(0.2617993877991494)) == S2LatLngRect.new(R1Interval.new(-0.2617993877991494, 0.2617993877991494), S1Interval.new(2.7052603405912112, -2.7052603405912112))
expect S2LatLngRect.new(R1Interval.new(1.0471975511965976, 1.3962634015954636), S1Interval.new(2.6179938779914944, 0.17453292519943295)).expanded_by_distance(S1Angle.from_radians(0.2617993877991494)) == S2LatLngRect.new(R1Interval.new(0.7853981633974483, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
# S2Cap.from_cap rounds one latitude one unit in the last place away from
# upstream here, so the comparison allows for that.
expect S2LatLngRect.new(R1Interval.new(0.0, 0.5235987755982988), S1Interval.new(0.0, 1.5707963267948966)).expanded_by_distance(S1Angle.from_radians(0.08726646259971647)) |> S2LatLngRect.approx_eq(S2LatLngRect.new(R1Interval.new(-0.08726646259971647, 0.6108652381980153), S1Interval.new(-0.10080944306377845, 1.671605769858675)), 1e-15)
expect S2LatLngRect.new(R1Interval.new(0.0, 0.5235987755982988), S1Interval.new(0.0, 1.5707963267948966)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(0.08726646259971647, 0.43633231299858233), S1Interval.new(0.09631456326785683, 1.4744817635270397))
expect S2LatLngRect.new(R1Interval.new(-0.5235987755982988, 0.0), S1Interval.new(-1.5707963267948966, 0.0)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(-0.43633231299858233, -0.08726646259971647), S1Interval.new(-1.4744817635270397, -0.09631456326785683))
expect S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(-1.5707963267948966, 3.141592653589793)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(0.08726646259971647, 1.4835298641951802), S1Interval.new(0.0, 1.5707963267948966))
expect S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(0.08726646259971647, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 0.0), S1Interval.new(-1.5707963267948966, 3.141592653589793)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(-1.4835298641951802, -0.08726646259971647), S1Interval.new(0.0, 1.5707963267948966))
expect S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 0.0), S1Interval.new(-3.141592653589793, 3.141592653589793)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(-1.5707963267948966, -0.08726646259971647), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRect.new(R1Interval.new(0.0, 0.5235987755982988), S1Interval.new(-3.141592653589793, 3.141592653589793)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(0.08726646259971647, 0.43633231299858233), S1Interval.new(-3.141592653589793, 3.141592653589793))
expect S2LatLngRect.new(R1Interval.new(0.0, 0.17278759594743864), S1Interval.new(0.0, 1.5707963267948966)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(1.0, 0.0), S1Interval.new(3.141592653589793, -3.141592653589793))
expect S2LatLngRect.new(R1Interval.new(0.0, 0.5235987755982988), S1Interval.new(0.0, 0.19198621771937624)).expanded_by_distance(S1Angle.from_radians(-0.08726646259971647)) == S2LatLngRect.new(R1Interval.new(1.0, 0.0), S1Interval.new(3.141592653589793, -3.141592653589793))
# Distances and Hausdorff distances between rectangles, from the cases of
# upstream's GetDistance and GetDirectedHausdorffDistance tests.
expect {
	a = S2LatLngRect.new(R1Interval.new(0.0, 0.03490658503988659), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(0.0, 0.0), S1Interval.new(0.0, 0.0))
	a.distance_to_rect(b).radians() == 0.0
		and a.directed_hausdorff_distance(b).radians() == 0.049360352393795104
		and a.hausdorff_distance(b).radians() == 0.049360352393795104
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.0, 0.03490658503988659), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(0.0, 0.03490658503988659), S1Interval.new(0.017453292519943295, 0.05235987755982989))
	a.distance_to_rect(b).radians() == 0.0
		and a.directed_hausdorff_distance(b).radians() == 0.017453292519943295
		and a.hausdorff_distance(b).radians() == 0.0174532925199433
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.017453292519943295, 0.03490658503988659), S1Interval.new(-0.017453292519943295, 0.017453292519943295))
	b = S2LatLngRect.new(R1Interval.new(-0.03490658503988659, -0.03490658503988659), S1Interval.new(-0.017453292519943295, -0.017453292519943295))
	a.distance_to_rect(b).radians() == 0.017453292519943295
		and a.directed_hausdorff_distance(b).radians() == 0.0780503264312706
		and a.hausdorff_distance(b).radians() == 0.0780503264312706
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.017453292519943295, 0.03490658503988659), S1Interval.new(-0.017453292519943295, 0.017453292519943295))
	b = S2LatLngRect.new(R1Interval.new(0.017453292519943295, 0.017453292519943295), S1Interval.new(0.03490658503988659, 0.03490658503988659))
	a.distance_to_rect(b).radians() == 0.017450634029070905
		and a.directed_hausdorff_distance(b).radians() == 0.06292652909176503
		and a.hausdorff_distance(b).radians() == 0.06292652909176503
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(1.5184364492350666, 1.5184364492350666), S1Interval.new(0.05235987755982989, 0.05235987755982989))
	a.distance_to_rect(b).radians() == 0.000913388506639147
		and a.directed_hausdorff_distance(b).radians() == 0.017737656209365297
		and a.hausdorff_distance(b).radians() == 0.017737656209365297
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(1.5533430342749532, 1.5533430342749532), S1Interval.new(3.1590459461097367, 3.1590459461097367))
	a.distance_to_rect(b).radians() == 0.05235810502254987
		and a.directed_hausdorff_distance(b).radians() == 0.08726646259971649
		and a.hausdorff_distance(b).radians() == 0.08726646259971649
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(1.4835298641951802, 1.4835298641951802), S1Interval.new(3.1590459461097367, 3.1590459461097367))
	a.distance_to_rect(b).radians() == 0.12216924626088659
		and a.directed_hausdorff_distance(b).radians() == 0.15707963267948957
		and a.hausdorff_distance(b).radians() == 0.15707963267948957
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(1.5707963267948966, 1.5707963267948966), S1Interval.new(0.0, 0.0))
	a.distance_to_rect(b).radians() == 0.03490658503988664
		and a.directed_hausdorff_distance(b).radians() == 0.06981317007977306
		and a.hausdorff_distance(b).radians() == 0.06981317007977306
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.53588974175501, 1.5707963267948966), S1Interval.new(0.0, 0.03490658503988659))
	b = S2LatLngRect.new(R1Interval.new(1.5533430342749532, 1.5533430342749532), S1Interval.new(1.5707963267948966, 1.5707963267948966))
	a.distance_to_rect(b).radians() == 0.01744265936699575
		and a.directed_hausdorff_distance(b).radians() == 0.039025163215635435
		and a.hausdorff_distance(b).radians() == 0.039025163215635435
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.5533430342749532, 1.5533430342749532), S1Interval.new(1.5707963267948966, 1.5707963267948966))
	b = S2LatLngRect.new(R1Interval.new(1.53588974175501, 1.5707963267948966), S1Interval.new(0.0, 0.03490658503988659))
	a.distance_to_rect(b).radians() == 0.01744265936699575
		and a.directed_hausdorff_distance(b).radians() == 0.01744265936699575
		and a.hausdorff_distance(b).radians() == 0.039025163215635435
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.017453292519943295, 0.03490658503988659), S1Interval.new(-0.017453292519943295, 0.017453292519943295))
	b = S2LatLngRect.new(R1Interval.new(0.0, 0.017453292519943295), S1Interval.new(0.03490658503988659, 0.05235987755982989))
	a.distance_to_rect(b).radians() == 0.017450634029070905
		and a.directed_hausdorff_distance(b).radians() == 0.05518963458845597
		and a.hausdorff_distance(b).radians() == 0.05518963458845597
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.017453292519943295, 0.03490658503988659), S1Interval.new(-0.017453292519943295, 0.017453292519943295))
	b = S2LatLngRect.new(R1Interval.new(-0.03490658503988659, -0.017453292519943295), S1Interval.new(-0.05235987755982989, -0.03490658503988659))
	a.distance_to_rect(b).radians() == 0.0174506340290709
		and a.directed_hausdorff_distance(b).radians() == 0.07404240835575013
		and a.hausdorff_distance(b).radians() == 0.07404240835575013
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5184364492350666, -1.4835298641951802), S1Interval.new(0.0, 0.05235987755982989))
	b = S2LatLngRect.new(R1Interval.new(-1.5533430342749532, -1.53588974175501), S1Interval.new(0.017453292519943295, 0.03490658503988659))
	a.distance_to_rect(b).radians() == 0.01745329251994332
		and a.directed_hausdorff_distance(b).radians() == 0.05236872855394031
		and a.hausdorff_distance(b).radians() == 0.05236872855394031
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5184364492350666, -1.4835298641951802), S1Interval.new(0.0, 0.05235987755982989))
	b = S2LatLngRect.new(R1Interval.new(-1.4660765716752369, -1.4486232791552935), S1Interval.new(0.017453292519943295, 0.03490658503988659))
	a.distance_to_rect(b).radians() == 0.01745329251994332
		and a.directed_hausdorff_distance(b).radians() == 0.052375795333734536
		and a.hausdorff_distance(b).radians() == 0.052375795333734536
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5184364492350666, -1.4835298641951802), S1Interval.new(0.0, 0.05235987755982989))
	b = S2LatLngRect.new(R1Interval.new(-1.53588974175501, -1.5009831567151235), S1Interval.new(1.5707963267948966, 1.5882496193148399))
	a.distance_to_rect(b).radians() == 0.061380830994909805
		and a.directed_hausdorff_distance(b).radians() == 0.09397239111751715
		and a.hausdorff_distance(b).radians() == 0.09397239111751715
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5184364492350666, -1.4835298641951802), S1Interval.new(0.0, 0.05235987755982989))
	b = S2LatLngRect.new(R1Interval.new(-1.4660765716752369, -1.4486232791552935), S1Interval.new(-1.5882496193148399, -1.5707963267948966))
	a.distance_to_rect(b).radians() == 0.1170374009302116
		and a.directed_hausdorff_distance(b).radians() == 0.13967966930929385
		and a.hausdorff_distance(b).radians() == 0.13967966930929385
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5184364492350666, -1.4835298641951802), S1Interval.new(0.0, 0.05235987755982989))
	b = S2LatLngRect.new(R1Interval.new(-1.5707963267948966, -1.5533430342749532), S1Interval.new(3.1590459461097367, 3.1764992386296798))
	a.distance_to_rect(b).radians() == 0.05235987755983009
		and a.directed_hausdorff_distance(b).radians() == 0.08726646259971649
		and a.hausdorff_distance(b).radians() == 0.08726646259971649
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5184364492350666, -1.4835298641951802), S1Interval.new(0.0, 0.05235987755982989))
	b = S2LatLngRect.new(R1Interval.new(-1.4660765716752369, -1.4486232791552935), S1Interval.new(3.1590459461097367, 3.1764992386296798))
	a.distance_to_rect(b).radians() == 0.15705832814102108
		and a.directed_hausdorff_distance(b).radians() == 0.19198439971153503
		and a.hausdorff_distance(b).radians() == 0.19198439971153503
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.17453292519943295, -0.08726646259971647), S1Interval.new(0.3490658503988659, 1.5707963267948966))
	b = S2LatLngRect.new(R1Interval.new(-0.19198621771937624, -0.06981317007977318), S1Interval.new(0.33161255787892263, 1.5882496193148399))
	a.distance_to_rect(b).radians() == 0.0
		and a.directed_hausdorff_distance(b).radians() == 0.0
		and a.hausdorff_distance(b).radians() == 0.024644508341014268
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.08726646259971647, 0.08726646259971647), S1Interval.new(0.13962634015954636, 0.13962634015954636))
	b = S2LatLngRect.new(R1Interval.new(-1.4835298641951802, -1.3962634015954636), S1Interval.new(-0.8726646259971648, 0.17453292519943295))
	a.distance_to_rect(b).radians() == 1.48352986419518
		and a.directed_hausdorff_distance(b).radians() == 1.48352986419518
		and a.hausdorff_distance(b).radians() == 1.6116219983433244
}
expect {
	a = S2LatLngRect.new(R1Interval.new(1.5707963267948966, 1.5707963267948966), S1Interval.new(0.17453292519943295, 0.17453292519943295))
	b = S2LatLngRect.new(R1Interval.new(0.06981317007977318, 1.3962634015954636), S1Interval.new(-0.17453292519943295, 0.17453292519943295))
	a.distance_to_rect(b).radians() == 0.17453292519943298
		and a.directed_hausdorff_distance(b).radians() == 0.17453292519943298
		and a.hausdorff_distance(b).radians() == 1.5009831567151233
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.017453292519943295, 0.17453292519943295), S1Interval.new(-0.13962634015954636, 0.3490658503988659))
	b = S2LatLngRect.new(R1Interval.new(-0.10471975511965978, -0.10471975511965978), S1Interval.new(-1.7453292519943295, -1.7453292519943295))
	a.distance_to_rect(b).radians() == 1.6073317549846824
		and a.directed_hausdorff_distance(b).radians() == 2.103492309003092
		and a.hausdorff_distance(b).radians() == 2.103492309003092
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.017453292519943295, 0.17453292519943295), S1Interval.new(-0.13962634015954636, 0.3490658503988659))
	b = S2LatLngRect.new(R1Interval.new(-1.5707963267948966, -1.5707963267948966), S1Interval.new(-0.3490658503988659, -0.3490658503988659))
	a.distance_to_rect(b).radians() == 1.5882496193148399
		and a.directed_hausdorff_distance(b).radians() == 1.7453292519943295
		and a.hausdorff_distance(b).radians() == 1.7453292519943295
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.017453292519943295, 0.17453292519943295), S1Interval.new(-0.13962634015954636, 0.3490658503988659))
	b = S2LatLngRect.new(R1Interval.new(1.5707963267948966, 1.5707963267948966), S1Interval.new(0.0, 0.0))
	a.distance_to_rect(b).radians() == 1.3962634015954636
		and a.directed_hausdorff_distance(b).radians() == 1.5533430342749532
		and a.hausdorff_distance(b).radians() == 1.5533430342749532
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(0.17453292519943295, 0.3490658503988659))
	b = S2LatLngRect.new(R1Interval.new(-0.06981317007977318, 0.06981317007977318), S1Interval.new(-0.17453292519943295, 0.0))
	a.distance_to_rect(b).radians() == 0.17410341778748667
		and a.directed_hausdorff_distance(b).radians() == 1.5009831567151233
		and a.hausdorff_distance(b).radians() == 1.5009831567151233
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.06981317007977318, 0.06981317007977318), S1Interval.new(-0.17453292519943295, 0.0))
	b = S2LatLngRect.new(R1Interval.new(0.0, 1.5707963267948966), S1Interval.new(0.17453292519943295, 0.3490658503988659))
	a.distance_to_rect(b).radians() == 0.17410341778748667
		and a.directed_hausdorff_distance(b).radians() == 0.3556981882615224
		and a.hausdorff_distance(b).radians() == 1.5009831567151233
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.8726646259971648, 0.8726646259971648), S1Interval.new(-0.17453292519943295, 0.17453292519943295))
	b = S2LatLngRect.new(R1Interval.new(0.5235987755982988, 1.0471975511965976), S1Interval.new(-0.17453292519943295, 0.17453292519943295))
	a.distance_to_rect(b).radians() == 0.0
		and a.directed_hausdorff_distance(b).radians() == 1.3962634015954636
		and a.hausdorff_distance(b).radians() == 1.3962634015954636
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.17453292519943295, 0.5235987755982988), S1Interval.new(2.9670597283903604, 3.141592653589793))
	b = S2LatLngRect.new(R1Interval.new(-0.8726646259971648, 0.8726646259971648), S1Interval.new(-0.17453292519943295, 0.17453292519943295))
	a.distance_to_rect(b).radians() == 1.711335351067482
		and a.directed_hausdorff_distance(b).radians() == 2.083325459694037
		and a.hausdorff_distance(b).radians() == 2.94892236548937
}
expect {
	a = S2LatLngRect.new(R1Interval.new(0.17453292519943295, 0.5235987755982988), S1Interval.new(-3.141592653589793, -2.9670597283903604))
	b = S2LatLngRect.new(R1Interval.new(-0.8726646259971648, 0.8726646259971648), S1Interval.new(-0.17453292519943295, 0.17453292519943295))
	a.distance_to_rect(b).radians() == 1.711335351067482
		and a.directed_hausdorff_distance(b).radians() == 2.083325459694037
		and a.hausdorff_distance(b).radians() == 2.94892236548937
}
# The trigonometry here can differ from the C library's by one unit in the
# last place, so this case allows for that.
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.5235987755982988, 0.5235987755982988), S1Interval.new(2.9670597283903604, 3.141592653589793))
	b = S2LatLngRect.new(R1Interval.new(-0.17453292519943295, 0.17453292519943295), S1Interval.new(-1.5707963267948966, 1.5707963267948966))
	(a.distance_to_rect(b).radians() - 1.3336568167613847).abs() <= 1e-15
		and (a.directed_hausdorff_distance(b).radians() - 1.5707963267948966).abs() <= 1e-15
		and (a.hausdorff_distance(b).radians() - 2.6114400527624055).abs() <= 1e-15
}
# The trigonometry here can differ from the C library's by one unit in the
# last place, so this case allows for that.
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.5235987755982988, 0.5235987755982988), S1Interval.new(-3.141592653589793, -2.9670597283903604))
	b = S2LatLngRect.new(R1Interval.new(-0.17453292519943295, 0.17453292519943295), S1Interval.new(-1.5707963267948966, 1.5707963267948966))
	(a.distance_to_rect(b).radians() - 1.3336568167613847).abs() <= 1e-15
		and (a.directed_hausdorff_distance(b).radians() - 1.5707963267948966).abs() <= 1e-15
		and (a.hausdorff_distance(b).radians() - 2.6114400527624055).abs() <= 1e-15
}
# The trigonometry here can differ from the C library's by one unit in the
# last place, so this case allows for that.
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.3490658503988659, 0.3490658503988659), S1Interval.new(1.8325957145940461, 1.9198621771937625))
	b = S2LatLngRect.new(R1Interval.new(-0.5235987755982988, 0.5235987755982988), S1Interval.new(0.08726646259971647, 0.2617993877991494))
	(a.distance_to_rect(b).radians() - 1.3989415754761576).abs() <= 1e-15
		and (a.directed_hausdorff_distance(b).radians() - 1.6463472670202026).abs() <= 1e-15
		and (a.hausdorff_distance(b).radians() - 1.7347051850363522).abs() <= 1e-15
}
# The trigonometry here can differ from the C library's by one unit in the
# last place, so this case allows for that.
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.3490658503988659, 0.3490658503988659), S1Interval.new(1.6580627893946132, 1.8325957145940461))
	b = S2LatLngRect.new(R1Interval.new(-0.5235987755982988, 0.5235987755982988), S1Interval.new(0.08726646259971647, 0.2617993877991494))
	(a.distance_to_rect(b).radians() - 1.253157311121183).abs() <= 1e-15
		and (a.directed_hausdorff_distance(b).radians() - 1.5707963267948968).abs() <= 1e-15
		and (a.hausdorff_distance(b).radians() - 1.5707963267948968).abs() <= 1e-15
}
expect S2LatLngRect.empty().directed_hausdorff_distance(S2LatLngRect.full()).radians() == 0.0
expect S2LatLngRect.full().directed_hausdorff_distance(S2LatLngRect.empty()).radians() == F64.pi
expect S2LatLngRect.new(R1Interval.new(-0.017453292519943295, 0.03490658503988659), S1Interval.new(-0.017453292519943295, 0.017453292519943295)).distance_to_lat_lng(S2LatLng.from_radians(-0.03490658503988659, -0.017453292519943295)).radians() == 0.017453292519943295
expect S2LatLngRect.new(R1Interval.new(-0.017453292519943295, 0.03490658503988659), S1Interval.new(-0.017453292519943295, 0.017453292519943295)).distance_to_lat_lng(S2LatLng.from_radians(0.017453292519943295, 0.03490658503988659)).radians() == 0.017450634029070905
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.5184364492350666, 0.05235987755982989)).radians() == 0.000913388506639147
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.5184364492350666, -0.017453292519943295)).radians() == 0.000913388506639147
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.5533430342749532, 0.017453292519943295)).radians() == 0.01745329251994332
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.5533430342749532, 3.1590459461097367)).radians() == 0.052358105022549874
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.4835298641951802, 0.017453292519943295)).radians() == 0.01745329251994332
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.4835298641951802, 3.1590459461097367)).radians() == 0.12216924626088659
expect S2LatLngRect.new(R1Interval.new(1.5009831567151235, 1.53588974175501), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(1.5707963267948966, 0.0)).radians() == 0.03490658503988664
expect S2LatLngRect.new(R1Interval.new(0.0, 0.03490658503988659), S1Interval.new(0.0, 0.03490658503988659)).distance_to_lat_lng(S2LatLng.from_radians(0.0, 0.0)).radians() == 0.0
expect S2LatLngRect.new(R1Interval.new(0.3490658503988659, 0.6981317007977318), S1Interval.new(2.9670597283903604, -2.9670597283903604)).distance_to_lat_lng(S2LatLng.from_radians(0.5235987755982988, -3.0543261909900767)).radians() == 0.0
expect S2LatLngRect.new(R1Interval.new(0.0, 1.0), S1Interval.new(3.0, -3.0)).is_inverted()
expect !S2LatLngRect.new(R1Interval.new(0.0, 1.0), S1Interval.new(-3.0, 3.0)).is_inverted()

# Directed Hausdorff distances where the second rectangle is more than 90
# degrees of longitude away, which uses the bisector of its side, north and
# south of the equator.
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.17453292519943295, 0.17453292519943295), S1Interval.new(0.0, 0.17453292519943295))
	b = S2LatLngRect.new(R1Interval.new(-1.0471975511965976, -0.3490658503988659), S1Interval.new(2.0943951023931953, 2.2689280275926285))
	a.distance_to_rect(b).radians() == 1.5888256147676947
		and a.directed_hausdorff_distance(b).radians() == 1.9785908499402132
		and a.hausdorff_distance(b).radians() == 1.9859353125078898
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.17453292519943295, 0.17453292519943295), S1Interval.new(0.0, 0.17453292519943295))
	b = S2LatLngRect.new(R1Interval.new(0.3490658503988659, 1.0471975511965976), S1Interval.new(2.0943951023931953, 2.2689280275926285))
	a.distance_to_rect(b).radians() == 1.5888256147676947
		and a.directed_hausdorff_distance(b).radians() == 1.9785908499402132
		and a.hausdorff_distance(b).radians() == 1.9859353125078898
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.3962634015954636, -1.2217304763960306), S1Interval.new(0.0, 0.17453292519943295))
	b = S2LatLngRect.new(R1Interval.new(-1.0471975511965976, -0.3490658503988659), S1Interval.new(2.6179938779914944, 2.792526803190927))
	a.distance_to_rect(b).radians() == 0.6659059765174941
		and a.directed_hausdorff_distance(b).radians() == 0.84236669505459
		and a.hausdorff_distance(b).radians() == 1.3740192710645267
}
# The trigonometry here can differ from the C library's by one unit in the
# last place, so this case allows for that.
expect {
	a = S2LatLngRect.new(R1Interval.new(-0.5235987755982988, 0.6981317007977318), S1Interval.new(0.0, 0.08726646259971647))
	b = S2LatLngRect.new(R1Interval.new(-0.8726646259971648, -0.8552113334772214), S1Interval.new(1.7453292519943295, 1.9198621771937625))
	(a.distance_to_rect(b).radians() - 1.2297161920770543).abs() <= 1e-15
		and a.directed_hausdorff_distance(b).radians() == 2.1802119714142494
		and a.hausdorff_distance(b).radians() == 2.1802119714142494
}
expect {
	a = S2LatLngRect.new(R1Interval.new(-1.5533430342749532, 1.5533430342749532), S1Interval.new(0.0, 0.017453292519943295))
	b = S2LatLngRect.new(R1Interval.new(-0.17453292519943295, -0.08726646259971647), S1Interval.new(2.9670597283903604, 2.9845130209103035))
	a.distance_to_rect(b).radians() == 1.4133969713264
		and a.directed_hausdorff_distance(b).radians() == 2.963160949125901
		and a.hausdorff_distance(b).radians() == 2.963160949125901
}

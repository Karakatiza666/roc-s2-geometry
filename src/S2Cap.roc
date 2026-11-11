import S1Angle
import S1ChordAngle
import S2Cell
import S2CellId
import S2Coords
import S2Edge
import S2Point

## A disc on the sphere: every point within a given angle of a centre.
##
## The radius is kept as an `S1ChordAngle`, so containment is a squared-distance
## comparison with no trigonometry. Two radii are special: a negative radius
## means the cap is empty, and a radius of 180 degrees means it is the whole
## sphere.
##
## A cap is the natural bound for "everything within 5 km of here", and is what
## a region coverer starts from.
S2Cap := { center : S2Point, radius : S1ChordAngle }.{

	## The cap of the given angular radius about `center`, which must be unit
	## length.
	##
	## A radius above pi, including an infinite one, gives the full cap. A
	## negative radius gives an empty cap.
	from_center_angle : S2Point, S1Angle -> S2Cap
	from_center_angle = |center, angle| {
		center: center,
		radius: S1ChordAngle.from_angle(angle.min(S1Angle.from_radians(F64.pi))),
	}

	## The cap of the given chord radius about `center`.
	from_center_chord_angle : S2Point, S1ChordAngle -> S2Cap
	from_center_chord_angle = |center, radius| { center: center, radius: radius }

	## The cap containing exactly one point.
	from_point : S2Point -> S2Cap
	from_point = |center| { center: center, radius: S1ChordAngle.zero() }

	## The cap whose flat top is `height` above the plane through the sphere's
	## centre, which is the parametrization that makes area linear.
	##
	## A negative height gives an empty cap and a height of 2 or more gives the
	## full cap.
	from_center_height : S2Point, F64 -> S2Cap
	from_center_height = |center, height| {
		center: center,
		radius: S1ChordAngle.from_length2(2.0 * height),
	}

	## The cap of the given area in steradians.
	##
	## A negative area gives an empty cap and an area of 4 pi or more gives the
	## full cap.
	from_center_area : S2Point, F64 -> S2Cap
	from_center_area = |center, area| {
		center: center,
		radius: S1ChordAngle.from_length2(area / F64.pi),
	}

	## The bounding cap of a cell.
	##
	## Centred on the cell's `(u, v)` midpoint, which is very close to the
	## cell centre and much cheaper to compute.
	from_cell : S2Cell -> S2Cap
	from_cell = |cell| {
		uv = cell.bound_uv()
		axis = S2Coords.face_uv_to_xyz(cell.face(), uv.x().center(), uv.y().center()).normalize()
		var $cap = S2Cap.from_point(axis)
		for k in (0.U64).until(4) {
			$cap = $cap.add_point(cell.vertex(k))
		}
		$cap
	}

	## The cap that contains no point.
	empty : () -> S2Cap
	empty = || { center: S2Point.new(1.0, 0.0, 0.0), radius: S1ChordAngle.negative() }

	## The cap that contains every point of the sphere.
	full : () -> S2Cap
	full = || { center: S2Point.new(1.0, 0.0, 0.0), radius: S1ChordAngle.straight() }

	## The center of the cap, a unit vector.
	center : S2Cap -> S2Point
	center = |cap| cap.center

	## The radius as a chord angle, which is how it is stored.
	radius : S2Cap -> S1ChordAngle
	radius = |cap| cap.radius

	## The radius as an angle. An empty cap reports -1 radian.
	radius_angle : S2Cap -> S1Angle
	radius_angle = |cap| cap.radius.to_angle()

	## The height of the cap above the plane through the sphere's centre.
	height : S2Cap -> F64
	height = |cap| 0.5 * cap.radius.length2()

	## The area of the cap in steradians.
	area : S2Cap -> F64
	area = |cap| 2.0 * F64.pi * cap.height().max(0.0)

	## True when the cap contains no point.
	is_empty : S2Cap -> Bool
	is_empty = |cap| cap.radius.is_negative()

	## True when the cap contains every point of the sphere.
	is_full : S2Cap -> Bool
	is_full = |cap| cap.radius.length2() == 4.0

	## True when the cap has any interior at all.
	has_interior : S2Cap -> Bool
	has_interior = |cap| cap.radius.length2() > 0.0

	## True when the center is a unit vector and the radius is at most 180
	## degrees.
	is_valid : S2Cap -> Bool
	is_valid = |cap| cap.center.is_unit_length() and cap.radius.length2() <= 4.0

	## Every point not in the cap's interior.
	##
	## The complement of a full cap is empty and the complement of an empty
	## cap is full.
	complement : S2Cap -> S2Cap
	complement = |cap|
		if cap.is_full() {
			S2Cap.empty()
		} else if cap.is_empty() {
			S2Cap.full()
		} else {
			{
				center: -cap.center,
				radius: S1ChordAngle.from_length2(4.0 - cap.radius.length2()),
			}
		}

	## True when the point is in the cap or on its boundary.
	contains_point : S2Cap, S2Point -> Bool
	contains_point = |cap, p| S1ChordAngle.from_points(cap.center, p) <= cap.radius

	## True when the point is strictly inside the cap. A full cap contains
	## every point.
	interior_contains_point : S2Cap, S2Point -> Bool
	interior_contains_point = |cap, p|
		cap.is_full() or S1ChordAngle.from_points(cap.center, p) < cap.radius

	## True when every point of `other` is in this cap. A full cap contains
	## every cap, and every cap contains an empty cap.
	contains_cap : S2Cap, S2Cap -> Bool
	contains_cap = |cap, other| {
		if cap.is_full() or other.is_empty() {
			return Bool.True
		}
		cap.radius >= S1ChordAngle.from_points(cap.center, other.center) + other.radius
	}

	## True when the two caps share at least one point. An empty cap shares no
	## point.
	intersects_cap : S2Cap, S2Cap -> Bool
	intersects_cap = |cap, other| {
		if cap.is_empty() or other.is_empty() {
			return Bool.False
		}
		cap.radius + other.radius >= S1ChordAngle.from_points(cap.center, other.center)
	}

	## True when the interior of this cap shares at least one point with
	## `other`. A cap with no interior, or an empty `other`, gives false.
	interior_intersects_cap : S2Cap, S2Cap -> Bool
	interior_intersects_cap = |cap, other| {
		if !cap.has_interior() or other.is_empty() {
			return Bool.False
		}
		cap.radius + other.radius > S1ChordAngle.from_points(cap.center, other.center)
	}

	## The smallest cap with the same centre that also contains the point.
	add_point : S2Cap, S2Point -> S2Cap
	add_point = |cap, p|
		if cap.is_empty() {
			{ center: p, radius: S1ChordAngle.zero() }
		} else {
			{ center: cap.center, radius: cap.radius.max(S1ChordAngle.from_points(cap.center, p)) }
		}

	## The smallest cap with the same centre that also contains `other`.
	add_cap : S2Cap, S2Cap -> S2Cap
	add_cap = |cap, other| {
		if cap.is_empty() {
			return other
		}
		if other.is_empty() {
			return cap
		}
		dist = S1ChordAngle.from_points(cap.center, other.center) + other.radius
		# Round the radius up so that the result really does contain `other`.
		rounded = dist.plus_error(2.220446049250313e-16 * dist.length2())
		{ center: cap.center, radius: cap.radius.max(rounded) }
	}

	## The cap grown by `distance` in every direction.
	expanded : S2Cap, S1Angle -> S2Cap
	expanded = |cap, distance|
		if cap.is_empty() {
			S2Cap.empty()
		} else {
			{ center: cap.center, radius: cap.radius + S1ChordAngle.from_angle(distance) }
		}

	## The smallest cap that contains both caps.
	##
	## Unlike `add_cap`, the centre of the result is not the centre of either
	## cap. It lies on the arc between the two centres, so that the result is
	## the same for either order of the caps.
	union : S2Cap, S2Cap -> S2Cap
	union = |cap, other|
		if cap.radius < other.radius {
			other.union(cap)
		} else if cap.is_full() or other.is_empty() {
			cap
		} else {
			this_radius = cap.radius_angle()
			other_radius = other.radius_angle()
			distance = cap.center.angle_to(other.center)
			if this_radius >= distance + other_radius {
				cap
			} else {
				result_radius = (distance + this_radius + other_radius) * 0.5
				result_center = S2Edge.point_on_line(
					cap.center,
					other.center,
					(distance - this_radius + other_radius) * 0.5,
				)
				S2Cap.from_center_angle(result_center, result_radius)
			}
		}

	## The cap itself, so that a cap can be used wherever a region is expected.
	cap_bound : S2Cap -> S2Cap
	cap_bound = |cap| cap

	## True when the cap contains the whole cell.
	contains_cell : S2Cap, S2Cell -> Bool
	contains_cell = |cap, cell| {
		# Checking the vertices first avoids taking the complement of a cap so
		# small that its complement rounds to the full sphere.
		var $all_inside = Bool.True
		for k in (0.U64).until(4) {
			if !cap.contains_point(cell.vertex(k)) {
				$all_inside = Bool.False
			}
		}
		if !$all_inside {
			return Bool.False
		}
		!intersects_cell_interior(cap.complement(), cell)
	}

	## True when the cap and the cell might share a point.
	##
	## Exact: this is not a conservative approximation.
	may_intersect_cell : S2Cap, S2Cell -> Bool
	may_intersect_cell = |cap, cell| {
		var $any_vertex_inside = Bool.False
		for k in (0.U64).until(4) {
			if cap.contains_point(cell.vertex(k)) {
				$any_vertex_inside = Bool.True
			}
		}
		if $any_vertex_inside {
			return Bool.True
		}
		intersects_cell_interior(cap, cell)
	}

	## True when the two caps agree to within `max_error`, treating empty and
	## full caps generously so that tiny numerical differences do not matter.
	approx_eq : S2Cap, S2Cap, F64 -> Bool
	approx_eq = |cap, other, max_error| {
		r1 = cap.radius.length2()
		r2 = other.radius.length2()
		(cap.center.angle_to(other.center).radians() <= max_error
			and (r1 - r2).abs() <= max_error)
			or (cap.is_empty() and r2 <= max_error)
			or (other.is_empty() and r1 <= max_error)
			or (cap.is_full() and r2 >= 4.0 - max_error)
			or (other.is_full() and r1 >= 4.0 - max_error)
	}

	is_eq : S2Cap, S2Cap -> Bool
	is_eq = |a, b|
		(a.center == b.center and a.radius == b.radius)
			or (a.is_empty() and b.is_empty())
			or (a.is_full() and b.is_full())

	to_inspect : S2Cap -> Str
	to_inspect = |cap|
		"S2Cap(${cap.center.to_inspect()}, ${cap.radius_angle().degrees().to_str()} deg)"
}

expect S2Cap.empty().is_empty()
expect S2Cap.full().is_full()
expect !S2Cap.empty().is_full()
expect !S2Cap.full().is_empty()
expect S2Cap.empty().is_valid()
expect S2Cap.full().is_valid()
expect (S2Cap.full().area() - 4.0 * F64.pi).abs() < 1e-15
expect S2Cap.empty().area() == 0.0
expect S2Cap.from_point(S2Point.new(1.0, 0.0, 0.0)).area() == 0.0
expect !S2Cap.from_point(S2Point.new(1.0, 0.0, 0.0)).has_interior()
expect {
	# A hemisphere has half the sphere's area.
	cap = S2Cap.from_center_angle(S2Point.new(0.0, 0.0, 1.0), S1Angle.from_degrees(90.0))
	(cap.area() - 2.0 * F64.pi).abs() < 1e-14
}
expect {
	cap = S2Cap.from_center_area(S2Point.new(0.0, 0.0, 1.0), 2.0 * F64.pi)
	(cap.radius_angle().degrees() - 90.0).abs() < 1e-13
}
expect {
	cap = S2Cap.from_center_height(S2Point.new(0.0, 0.0, 1.0), 1.0)
	(cap.radius_angle().degrees() - 90.0).abs() < 1e-13
}
expect S2Cap.full().complement().is_empty()
expect S2Cap.empty().complement().is_full()
expect {
	cap = S2Cap.from_center_angle(S2Point.new(0.0, 0.0, 1.0), S1Angle.from_degrees(60.0))
	complement = cap.complement()
	complement.center() == S2Point.new(0.0, 0.0, -1.0)
		and (complement.radius_angle().degrees() - 120.0).abs() < 1e-12
}
expect {
	cap = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(20.0))
	cap.contains_point(S2Point.new(1.0, 0.0, 0.0))
		and cap.interior_contains_point(S2Point.new(1.0, 0.0, 0.0))
		and !cap.contains_point(S2Point.new(0.0, 1.0, 0.0))
}
expect {
	# A zero-radius cap contains its centre but has no interior.
	cap = S2Cap.from_point(S2Point.new(1.0, 0.0, 0.0))
	cap.contains_point(S2Point.new(1.0, 0.0, 0.0))
		and !cap.interior_contains_point(S2Point.new(1.0, 0.0, 0.0))
}
expect {
	big = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(40.0))
	small = S2Cap.from_center_angle(S2Point.new(1.0, 0.1, 0.0).normalize(), S1Angle.from_degrees(5.0))
	big.contains_cap(small) and !small.contains_cap(big) and big.intersects_cap(small)
}
expect {
	a = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))
	b = S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.from_degrees(10.0))
	!a.intersects_cap(b) and !a.interior_intersects_cap(b)
}
expect S2Cap.full().contains_cap(S2Cap.empty())
expect !S2Cap.empty().intersects_cap(S2Cap.full())
expect {
	cap = S2Cap.empty().add_point(S2Point.new(1.0, 0.0, 0.0))
	cap.center() == S2Point.new(1.0, 0.0, 0.0) and cap.radius().is_zero()
}
expect {
	cap = S2Cap.from_point(S2Point.new(1.0, 0.0, 0.0)).add_point(S2Point.new(0.0, 1.0, 0.0))
	cap.contains_point(S2Point.new(0.0, 1.0, 0.0))
		and (cap.radius_angle().degrees() - 90.0).abs() < 1e-13
}
expect {
	a = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))
	b = S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.from_degrees(10.0))
	merged = a.add_cap(b)
	merged.contains_cap(b) and merged.contains_cap(a)
}
expect {
	cap = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))
	grown = cap.expanded(S1Angle.from_degrees(5.0))
	(grown.radius_angle().degrees() - 15.0).abs() < 1e-12
}
expect S2Cap.empty().expanded(S1Angle.from_degrees(5.0)).is_empty()
expect S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.infinity()).is_full()
expect S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.from_degrees(270.0)).is_full()
expect S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.from_degrees(-1.0)).is_empty()
expect S2Cap.from_center_height(S2Point.new(0.0, 1.0, 0.0), 3.0).is_full()
expect S2Cap.from_center_height(S2Point.new(0.0, 1.0, 0.0), -0.5).is_empty()
expect S2Cap.from_center_area(S2Point.new(0.0, 1.0, 0.0), 5.0 * F64.pi).is_full()
expect S2Cap.from_center_area(S2Point.new(0.0, 1.0, 0.0), -1.0).is_empty()
expect S2Cap.full().interior_contains_point(S2Point.new(-1.0, 0.0, 0.0))
expect S2Cap.full() == S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.from_radians(F64.pi))
expect {
	# Two 10 degree caps whose centres are 90 degrees apart are bounded by the
	# cap of radius (90 + 10 + 10) / 2 = 55 degrees, centred 45 degrees from
	# the first centre, whichever cap is taken first.
	a = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))
	b = S2Cap.from_center_angle(S2Point.new(0.0, 1.0, 0.0), S1Angle.from_degrees(10.0))
	mid = S2Point.new(1.0, 1.0, 0.0).normalize()
	ab = a.union(b)
	ba = b.union(a)
	(ab.radius_angle().degrees() - 55.0).abs() < 1e-12
		and ab.center().approx_eq(mid, 1e-14)
		and (ba.radius_angle().degrees() - 55.0).abs() < 1e-12
		and ba.center().approx_eq(mid, 1e-14)
}
expect {
	# A cap that already holds the other is the union.
	big = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(40.0))
	small = S2Cap.from_center_angle(S2Point.new(1.0, 0.1, 0.0).normalize(), S1Angle.from_degrees(5.0))
	big.union(small) == big and small.union(big) == big
}
expect S2Cap.full().union(S2Cap.from_point(S2Point.new(0.0, 1.0, 0.0))).is_full()
expect {
	a = S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))
	S2Cap.empty().union(a) == a and a.union(S2Cap.empty()) == a
}
expect {
	cell = S2Cell.from_face(0)
	cap = S2Cap.from_cell(cell)
	failures : U64
	failures = (0.U64).until(4).fold(0, |acc, k| if (cap.contains_point(cell.vertex(k))) acc else acc + 1)
	failures == 0 and cap.contains_point(cell.center())
}
expect {
	# The whole sphere contains every cell.
	S2Cap.full().contains_cell(S2Cell.from_face(3))
		and S2Cap.full().may_intersect_cell(S2Cell.from_face(3))
}
expect {
	# An empty cap contains and meets nothing.
	!S2Cap.empty().contains_cell(S2Cell.from_face(0))
		and !S2Cap.empty().may_intersect_cell(S2Cell.from_face(0))
}
expect {
	# A cap around a cell's centre that is smaller than the cell meets it but
	# does not contain it.
	cell = S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(5))
	cap = S2Cap.from_center_angle(cell.center(), S1Angle.from_degrees(0.1))
	cap.may_intersect_cell(cell) and !cap.contains_cell(cell)
}
expect {
	# A cap far from a cell does not meet it.
	cell = S2Cell.from_face(0)
	cap = S2Cap.from_center_angle(S2Point.new(-1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))
	!cap.may_intersect_cell(cell)
}
expect {
	# A cap containing a whole face contains that face cell.
	cell = S2Cell.from_face(2)
	cap = S2Cap.from_center_angle(S2Point.new(0.0, 0.0, 1.0), S1Angle.from_degrees(80.0))
	cap.contains_cell(cell) and cap.may_intersect_cell(cell)
}
expect S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0)).cap_bound()
	== S2Cap.from_center_angle(S2Point.new(1.0, 0.0, 0.0), S1Angle.from_degrees(10.0))

## True when the cap meets the cell somewhere other than at a cell vertex.
##
## Assumes the vertices have already been tested, which is what lets it
## look only at the four edges.
intersects_cell_interior : S2Cap, S2Cell -> Bool
intersects_cell_interior = |cap, cell| {
	# A cap of a hemisphere or more has a convex complement, so with no
	# vertex contained no interior point can be either.
	if cap.radius >= S1ChordAngle.right() {
		return Bool.False
	}
	if cap.is_empty() {
		return Bool.False
	}
	if cell.contains_point(cap.center) {
		return Bool.True
	}

	sin2_angle = cap.radius.sin2()
	var $found = Bool.False
	var $ruled_out = Bool.False
	for k in (0.U64).until(4) {
		if !$found and !$ruled_out {
			edge = cell.edge_raw(k)
			dot = cap.center.dot(edge)
			if dot <= 0.0 {
				if dot * dot > sin2_angle * edge.norm2() {
					# The whole cap is outside this edge.
					$ruled_out = Bool.True
				} else {
					# The edge's great circle cuts the cap; check that the
					# closest approach falls between the two endpoints.
					direction = edge.cross(cap.center)
					if direction.dot(cell.vertex(k)) < 0.0
						and direction.dot(cell.vertex((k + 1) % 4)) > 0.0 {
						$found = Bool.True
					}
				}
			}
		}
	}
	$found
}

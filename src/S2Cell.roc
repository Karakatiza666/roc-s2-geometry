import R1Interval
import R2Rect
import S1ChordAngle
import S2CellId
import S2Coords
import S2Edge
import S2LatLng
import Internal/S2Lookup
import S2Metric
import S2Point

## The geometry of one cell: its four vertices, its edges, its area, and the
## containment tests built on them.
##
## `S2CellId` is the cheap identity of a cell and the thing to store; `S2Cell`
## is the decoded form, worth building when the cell's shape is actually
## needed. Constructing one costs a Hilbert-curve decode, so hold on to it if
## several of these operations are wanted.
##
## The bounds of a cell are constructors on the bounding types rather than
## methods here, since Roc modules cannot import one another in a cycle: use
## `S2LatLngRect.from_cell` and `S2Cap.from_cell`.
S2Cell := { id : S2CellId, face : U64, level : U64, orientation : U64, uv : R2Rect }.{

	## The cell with the given id.
	from_cell_id : S2CellId -> S2Cell
	from_cell_id = |cell_id| {
		ij = cell_id.to_face_ij_orientation()
		cell_size = cell_id.size_ij()
		mask = cell_size.bitwise_not().plus_wrap(1)
		i_lo = ij.i.bitwise_and(mask)
		j_lo = ij.j.bitwise_and(mask)
		scale = 1.0 / S2Coords.max_size.to_f64()
		{
			id: cell_id,
			face: ij.face,
			level: cell_id.level(),
			orientation: ij.orientation,
			uv: R2Rect.new(
				R1Interval.new(
					S2Coords.st_to_uv(scale * i_lo.to_f64()),
					S2Coords.st_to_uv(scale * (i_lo + cell_size).to_f64()),
				),
				R1Interval.new(
					S2Coords.st_to_uv(scale * j_lo.to_f64()),
					S2Coords.st_to_uv(scale * (j_lo + cell_size).to_f64()),
				),
			),
		}
	}

	## The leaf cell containing the given point.
	from_point : S2Point -> S2Cell
	from_point = |p| S2Cell.from_cell_id(S2CellId.from_point(p))

	## The leaf cell containing the given position.
	from_lat_lng : S2LatLng -> S2Cell
	from_lat_lng = |ll| S2Cell.from_cell_id(S2CellId.from_lat_lng(ll))

	## The level-0 cell covering the given face.
	from_face : U64 -> S2Cell
	from_face = |face_index| S2Cell.from_cell_id(S2CellId.from_face(face_index))

	from_face_pos_level : U64, U64, U64 -> S2Cell
	from_face_pos_level = |face_index, position, target_level|
		S2Cell.from_cell_id(S2CellId.from_face_pos_level(face_index, position, target_level))

	id : S2Cell -> S2CellId
	id = |cell| cell.id

	face : S2Cell -> U64
	face = |cell| cell.face

	level : S2Cell -> U64
	level = |cell| cell.level

	## The Hilbert orientation of the cell, combining `S2Lookup.swap_mask` and
	## `S2Lookup.invert_mask`.
	orientation : S2Cell -> U64
	orientation = |cell| cell.orientation

	is_leaf : S2Cell -> Bool
	is_leaf = |cell| cell.level == S2CellId.max_level

	## The cell's extent in `(u, v)` coordinates on its own face.
	bound_uv : S2Cell -> R2Rect
	bound_uv = |cell| cell.uv

	## The `k`-th vertex, counterclockwise starting from the `(u_lo, v_lo)`
	## corner. Not unit length.
	vertex_raw : S2Cell, U64 -> S2Point
	vertex_raw = |cell, index| {
		k = index.bitwise_and(3)
		j = k.shr_zf_wrap(1)
		i = j.bitwise_xor(k.bitwise_and(1))
		S2Coords.face_uv_to_xyz(cell.face, cell.uv.x().bound(i), cell.uv.y().bound(j))
	}

	## The `k`-th vertex as a unit vector, counterclockwise.
	vertex : S2Cell, U64 -> S2Point
	vertex = |cell, k| cell.vertex_raw(k).normalize()

	## The inward-facing normal of the great circle through the `k`-th edge,
	## which runs from vertex `k` to vertex `k + 1`. Not unit length.
	edge_raw : S2Cell, U64 -> S2Point
	edge_raw = |cell, index| {
		k = index.bitwise_and(3)
		if k == 0 {
			S2Coords.v_norm(cell.face, cell.uv.y().lo())
		} else if k == 1 {
			S2Coords.u_norm(cell.face, cell.uv.x().hi())
		} else if k == 2 {
			-S2Coords.v_norm(cell.face, cell.uv.y().hi())
		} else {
			-S2Coords.u_norm(cell.face, cell.uv.x().lo())
		}
	}

	## The `k`-th edge normal as a unit vector.
	edge : S2Cell, U64 -> S2Point
	edge = |cell, k| cell.edge_raw(k).normalize()

	## The centre of the cell, not normalized.
	center_raw : S2Cell -> S2Point
	center_raw = |cell| cell.id.to_point_raw()

	## The centre of the cell as a unit vector.
	center : S2Cell -> S2Point
	center = |cell| cell.center_raw().normalize()

	## The centre of the cell in latitude and longitude.
	center_lat_lng : S2Cell -> S2LatLng
	center_lat_lng = |cell| S2LatLng.from_point(cell.center_raw())

	## The four children, in Hilbert order.
	##
	## Cheaper than building each child from its id, because the `(u, v)`
	## bounds are halved rather than decoded again.
	subdivide : S2Cell -> List(S2Cell)
	subdivide = |cell| {
		if cell.is_leaf() {
			return []
		}
		uv_mid = cell.id.center_uv()
		child_ids = cell.id.children()
		corners = S2Lookup.pos_to_ij.get(cell.orientation) ?? []
		var $out = []
		for position in (0.U64).until(4) {
			corner = corners.get(position) ?? 0
			i = corner.shr_zf_wrap(1)
			j = corner.bitwise_and(1)
			child_x =
				if i == 0 {
					R1Interval.new(cell.uv.x().lo(), uv_mid.x())
				} else {
					R1Interval.new(uv_mid.x(), cell.uv.x().hi())
				}
			child_y =
				if j == 0 {
					R1Interval.new(cell.uv.y().lo(), uv_mid.y())
				} else {
					R1Interval.new(uv_mid.y(), cell.uv.y().hi())
				}
			$out = $out.append({
				id: child_ids.get(position) ?? cell.id,
				face: cell.face,
				level: cell.level + 1,
				orientation: cell.orientation
					.bitwise_xor(S2Lookup.pos_to_orientation.get(position) ?? 0),
				uv: R2Rect.new(child_x, child_y),
			})
		}
		$out
	}

	## The area of the cell in steradians, accurate to six digits even for leaf
	## cells.
	exact_area : S2Cell -> F64
	exact_area = |cell| {
		v0 = cell.vertex(0)
		v1 = cell.vertex(1)
		v2 = cell.vertex(2)
		v3 = cell.vertex(3)
		S2Point.triangle_area(v0, v1, v2) + S2Point.triangle_area(v0, v2, v3)
	}

	## The average area of a cell at this level, which needs no geometry at
	## all.
	average_area : S2Cell -> F64
	average_area = |cell| S2Metric.avg_area.value_at(cell.level)

	## The area of the cell to within 3%, or 0.1% from level 5 down.
	##
	## Computes the area of the flat quadrilateral through the four vertices
	## and corrects it for the curvature of the sphere.
	approx_area : S2Cell -> F64
	approx_area = |cell| {
		if cell.level < 2 {
			return cell.average_area()
		}
		flat_area =
			0.5 * (cell.vertex(2) - cell.vertex(0)).cross(cell.vertex(3) - cell.vertex(1)).norm()
		flat_area * 2.0 / (1.0 + (1.0 - (1.0 / F64.pi) * flat_area).min(1.0).sqrt())
	}

	## True when the point lies inside the cell or on its boundary.
	##
	## The `(u, v)` bound grows by `F64` machine epsilon, which is the most
	## error that the conversion to `(s, t)` can add. So the cell of a point
	## always contains that point.
	contains_point : S2Cell, S2Point -> Bool
	contains_point = |cell, p|
		match S2Coords.face_xyz_to_uv(cell.face, p) {
			Ok(uv) => cell.uv.expanded_by(2.220446049250313e-16).contains_point(uv)
			Err(NotOnFace) => Bool.False
		}

	## True when `other` is this cell or one of its descendants.
	contains_cell : S2Cell, S2Cell -> Bool
	contains_cell = |cell, other| cell.id.contains(other.id)

	## True when either cell contains the other.
	may_intersect_cell : S2Cell, S2Cell -> Bool
	may_intersect_cell = |cell, other| cell.id.intersects(other.id)

	## The distance from the point to the closest point of the cell, which is
	## zero when the cell contains it.
	distance_to_point : S2Cell, S2Point -> S1ChordAngle
	distance_to_point = |cell, p|
		if cell.contains_point(p) {
			S1ChordAngle.zero()
		} else {
			cell.boundary_distance_to_point(p)
		}

	## The distance from the point to the closest point of the cell's
	## boundary, which is non-zero even for a point inside the cell.
	boundary_distance_to_point : S2Cell, S2Point -> S1ChordAngle
	boundary_distance_to_point = |cell, p| {
		var $best = S1ChordAngle.infinity()
		for k in (0.U64).until(4) {
			candidate = S2Edge.distance_to_edge(p, cell.vertex(k), cell.vertex((k + 1) % 4))
			$best = $best.min(candidate)
		}
		$best
	}

	## The distance from the point to the furthest point of the cell.
	##
	## When all four vertices are within a right angle of the point, the
	## furthest point is a vertex. Otherwise the furthest point can lie on an
	## edge or inside the cell, so the result is a straight angle minus the
	## distance from the antipode of the point to the cell.
	max_distance_to_point : S2Cell, S2Point -> S1ChordAngle
	max_distance_to_point = |cell, p| {
		var $worst = S1ChordAngle.negative()
		for k in (0.U64).until(4) {
			$worst = $worst.max(S1ChordAngle.from_points(p, cell.vertex(k)))
		}
		if $worst <= S1ChordAngle.right() {
			$worst
		} else {
			S1ChordAngle.straight() - cell.distance_to_point(p.negate())
		}
	}

	is_eq : S2Cell, S2Cell -> Bool
	is_eq = |a, b| a.id == b.id

	to_inspect : S2Cell -> Str
	to_inspect = |cell| "S2Cell(${cell.id.to_token()})"
}

expect S2Cell.from_face(0).level() == 0
expect {
	# The furthest point of face 0 from (-1, 0, 0) is a full straight angle
	# away, and it is not a vertex.
	S2Cell.from_face(0).max_distance_to_point(S2Point.new(-1.0, 0.0, 0.0)).degrees() > 179.999999
}
expect S2Cell.from_face(3).face() == 3
expect S2Cell.from_face(0).is_leaf() == Bool.False
expect S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(30)).is_leaf()
expect S2Cell.from_face(0).bound_uv() == R2Rect.new(R1Interval.new(-1.0, 1.0), R1Interval.new(-1.0, 1.0))
expect {
	# A face cell's four vertices are the four corners of that cube face.
	cell = S2Cell.from_face(0)
	cell.vertex(0).approx_eq(S2Point.new(1.0, -1.0, -1.0).normalize(), 1e-15)
		and cell.vertex(1).approx_eq(S2Point.new(1.0, 1.0, -1.0).normalize(), 1e-15)
		and cell.vertex(2).approx_eq(S2Point.new(1.0, 1.0, 1.0).normalize(), 1e-15)
		and cell.vertex(3).approx_eq(S2Point.new(1.0, -1.0, 1.0).normalize(), 1e-15)
}
expect {
	# Vertices wind counterclockwise as seen from outside the sphere.
	cell = S2Cell.from_face(2)
	normal = (cell.vertex(1) - cell.vertex(0)).cross(cell.vertex(2) - cell.vertex(0))
	normal.dot(cell.center()) > 0.0
}
expect {
	# Each edge normal is perpendicular to the two vertices it joins.
	cell = S2Cell.from_cell_id(S2CellId.from_face(1).child(2).child(3))
	failures : U64
	failures = (0.U64).until(4).fold(
		0,
		|acc, k| {
			n = cell.edge(k)
			ok = n.dot(cell.vertex(k)).abs() < 1e-15 and n.dot(cell.vertex((k + 1) % 4)).abs() < 1e-15
			if (ok) acc else acc + 1
		},
	)
	failures == 0
}
expect {
	# The six faces cover the sphere exactly once.
	total = (0.U64).until(6).fold(0.0, |acc, f| acc + S2Cell.from_face(f).exact_area())
	(total - 4.0 * F64.pi).abs() < 1e-13
}
expect {
	# A cell's children partition it.
	cell = S2Cell.from_cell_id(S2CellId.from_face(4).child(1))
	children_area = cell.subdivide().fold(0.0, |acc, child| acc + child.exact_area())
	(children_area - cell.exact_area()).abs() < 1e-15
}
expect S2Cell.from_face(0).subdivide().len() == 4
expect {
	# Subdividing agrees with decoding each child id from scratch.
	cell = S2Cell.from_cell_id(S2CellId.from_face(2).child(3).child(1))
	failures : U64
	failures = cell.subdivide().map2(
		cell.id.children(),
		|child, child_id| if child.id() == child_id and child.bound_uv() == S2Cell.from_cell_id(child_id).bound_uv() {
			0
		} else {
			1
		},
	)
		.fold(0, |acc, v| acc + v)
	failures == 0
}
expect {
	cell = S2Cell.from_face(0)
	cell.contains_point(S2Point.new(1.0, 0.0, 0.0)) and !cell.contains_point(S2Point.new(-1.0, 0.0, 0.0))
}
expect {
	# Every cell contains its own centre.
	cell = S2Cell.from_cell_id(S2CellId.from_face(5).child(0).child(2).child(1))
	cell.contains_point(cell.center())
}
expect {
	parent = S2Cell.from_cell_id(S2CellId.from_face(1).child(2))
	child = S2Cell.from_cell_id(S2CellId.from_face(1).child(2).child(0))
	parent.contains_cell(child) and !child.contains_cell(parent) and parent.may_intersect_cell(child)
}
expect {
	# approx_area is within 0.1% of exact_area from level 5 down.
	cell = S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(8))
	exact = cell.exact_area()
	(cell.approx_area() - exact).abs() / exact < 1e-3
}
expect {
	# average_area is the metric's value, independent of the cell.
	cell = S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(10))
	cell.average_area() == S2Metric.avg_area.value_at(10)
}
expect {
	cell = S2Cell.from_face(0)
	cell.distance_to_point(S2Point.new(1.0, 0.0, 0.0)).is_zero()
}
expect {
	# The closest point of face 0 to the antipode of its centre is one of its
	# corners, at acos(-1/sqrt(3)) away.
	cell = S2Cell.from_face(0)
	d = cell.distance_to_point(S2Point.new(-1.0, 0.0, 0.0))
	(d.degrees() - 125.26438968275465).abs() < 1e-12
}
expect {
	cell = S2Cell.from_face(0)
	cell.boundary_distance_to_point(cell.center()).radians() > 0.0
}
expect {
	cell = S2Cell.from_face(0)
	cell.max_distance_to_point(S2Point.new(1.0, 0.0, 0.0)) >= cell.distance_to_point(S2Point.new(1.0, 0.0, 0.0))
}
expect S2Cell.from_face(1).vertex_raw(5) == S2Cell.from_face(1).vertex_raw(1)
expect S2Cell.from_face(1).edge_raw(6) == S2Cell.from_face(1).edge_raw(2)
expect S2Cell.from_face(1).edge(7) == S2Cell.from_face(1).edge(3)
expect {
	# Leaf cells of points near cell edges must contain those points.
	points = [
		S2Point.new(1.0, 1.0e-9, 1.0e-9),
		S2Point.new(-0.3, 0.7, 0.2),
		S2Point.new(0.1, 0.2, 0.9999999),
		S2Point.new(1.0, 0.5, 0.5),
	]
	points.all(|p| S2Cell.from_cell_id(S2CellId.from_point(p)).contains_point(p.normalize()))
}
expect {
	# A point just outside the u bound by less than epsilon is still inside.
	cell = S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(5))
	hi = cell.bound_uv().x().hi()
	p = S2Coords.face_uv_to_xyz(0, hi + 1.5e-16, cell.bound_uv().y().lo() + 0.001)
	cell.contains_point(p)
}

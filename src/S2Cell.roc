import R1Interval
import R2Rect
import S1ChordAngle
import S2CellId
import S2Coords
import S2Edge
import S2EdgeCrosser
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

	## The cell at `level` whose Hilbert curve position on `face_index` is
	## `position`.
	from_face_pos_level : U64, U64, U64 -> S2Cell
	from_face_pos_level = |face_index, position, target_level|
		S2Cell.from_cell_id(S2CellId.from_face_pos_level(face_index, position, target_level))

	## The id of the cell.
	id : S2Cell -> S2CellId
	id = |cell| cell.id

	## The cube face of the cell, in `[0, 5]`.
	face : S2Cell -> U64
	face = |cell| cell.face

	## The subdivision level of the cell. Level 0 is a whole face and level 30
	## is a leaf cell.
	level : S2Cell -> U64
	level = |cell| cell.level

	## The Hilbert orientation of the cell, combining `S2Lookup.swap_mask` and
	## `S2Lookup.invert_mask`.
	orientation : S2Cell -> U64
	orientation = |cell| cell.orientation

	## True when the cell is at level 30, the finest level.
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
	## The `(u, v)` bound grows by 5/3 of `F64` machine epsilon, which is more
	## than the error that the conversion to `(s, t)` and back can add. So the
	## cell of a point always contains that point.
	contains_point : S2Cell, S2Point -> Bool
	contains_point = |cell, p|
		match S2Coords.face_xyz_to_uv(cell.face, p) {
			Ok(uv) => cell.uv.expanded_by((5.0 / 3.0) * 2.220446049250313e-16).contains_point(uv)
			Err(NotOnFace) => Bool.False
		}

	## True when `other` is this cell or one of its descendants.
	contains_cell : S2Cell, S2Cell -> Bool
	contains_cell = |cell, other| cell.id.contains(other.id)

	## True when either cell contains the other.
	may_intersect_cell : S2Cell, S2Cell -> Bool
	may_intersect_cell = |cell, other| cell.id.intersects(other.id)

	## The cell's own id, upstream's `S2Cell::GetCellUnionBound`. With
	## `contains_cell` and `may_intersect_cell` this makes a cell a region
	## that `S2RegionCoverer` can cover.
	cell_union_bound : S2Cell -> List(S2CellId)
	cell_union_bound = |cell| [cell.id]

	## The number of leaf cells along one edge of the cell.
	size_ij : S2Cell -> U64
	size_ij = |cell| S2CellId.size_ij_at_level(cell.level)

	## The edge length of the cell in `(s, t)` coordinates.
	size_st : S2Cell -> F64
	size_st = |cell| S2CellId.size_st_at_level(cell.level)

	## The distance from the point to the closest point of the cell, which is
	## zero when the cell contains it.
	distance_to_point : S2Cell, S2Point -> S1ChordAngle
	distance_to_point = |cell, p| distance_internal(cell, p, Bool.True)

	## The distance from the point to the closest point of the cell's
	## boundary, which is non-zero even for a point inside the cell.
	boundary_distance_to_point : S2Cell, S2Point -> S1ChordAngle
	boundary_distance_to_point = |cell, p| distance_internal(cell, p, Bool.False)

	## The distance from the point to the furthest point of the cell.
	##
	## When all four vertices are within a right angle of the point, the
	## furthest point is a vertex. Otherwise the furthest point can lie on an
	## edge or inside the cell, so the result is a straight angle minus the
	## distance from the antipode of the point to the cell.
	max_distance_to_point : S2Cell, S2Point -> S1ChordAngle
	max_distance_to_point = |cell, p| {
		target = S2Coords.face_xyz_to_uvw(cell.face, p)
		worst =
			vertex_chord_distance(cell, target, 0, 0)
				.max(vertex_chord_distance(cell, target, 1, 0))
				.max(vertex_chord_distance(cell, target, 0, 1).max(vertex_chord_distance(cell, target, 1, 1)))
		if worst <= S1ChordAngle.right() {
			worst
		} else {
			S1ChordAngle.straight() - cell.distance_to_point(-p)
		}
	}

	## The distance from the edge `ab` to the closest point of the cell,
	## which is zero when they meet.
	distance_to_edge : S2Cell, S2Point, S2Point -> S1ChordAngle
	distance_to_edge = |cell, a, b| {
		# An endpoint inside the cell gives zero.
		endpoints = cell.distance_to_point(a).min(cell.distance_to_point(b))
		if endpoints == S1ChordAngle.zero() {
			return endpoints
		}
		# So does an edge that crosses the boundary.
		v = [cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3)]
		(crosses, _) = v.fold(
			(Bool.False, S2EdgeCrosser.new_with_c(a, b, cell.vertex(3))),
			|(found, crosser), corner| {
				(sign, next) = crosser.crossing_sign(corner)
				(found or sign >= 0, next)
			},
		)
		if crosses {
			return S1ChordAngle.zero()
		}
		# Otherwise the minimum is between a cell vertex and the edge. The
		# interiors of two edges can only be closest where they cross, which
		# is ruled out above.
		v.fold(endpoints, |best, corner| S2Edge.update_min_distance(corner, a, b, best) ?? best)
	}

	## The distance from the edge `ab` to the furthest point of the cell.
	max_distance_to_edge : S2Cell, S2Point, S2Point -> S1ChordAngle
	max_distance_to_edge = |cell, a, b| {
		endpoints = cell.max_distance_to_point(a).max(cell.max_distance_to_point(b))
		if endpoints <= S1ChordAngle.right() {
			endpoints
		} else {
			S1ChordAngle.straight() - cell.distance_to_edge(-a, -b)
		}
	}

	## The distance between the closest points of two cells, which is zero
	## when they meet.
	distance_to_cell : S2Cell, S2Cell -> S1ChordAngle
	distance_to_cell = |cell, target| {
		if cell.face == target.face {
			match furthest_edge(cell, target) {
				Err(Touching) => S1ChordAngle.zero()
				Ok(ai) => {
					# The minimum is between an endpoint of edge ai of this cell
					# and the opposite edge of the target, or the other way
					# round.
					bi = ai.bitwise_xor(2)
					va1 = cell.vertex(ai)
					va2 = cell.vertex(ai + 1)
					vb1 = target.vertex(bi)
					vb2 = target.vertex(bi + 1)
					start = S1ChordAngle.infinity()
					d1 = S2Edge.update_min_distance(va1, vb1, vb2, start) ?? start
					d2 = S2Edge.update_min_distance(va2, vb1, vb2, d1) ?? d1
					d3 = S2Edge.update_min_interior_distance(vb1, va1, va2, d2) ?? d2
					S2Edge.update_min_interior_distance(vb2, va1, va2, d3) ?? d3
				}
			}
		} else {
			# The minimum is between a vertex of one cell and an edge of the
			# other: 32 pairs in all.
			va = vertices(cell)
			vb = vertices(target)
			pairs(4).fold(
				S1ChordAngle.infinity(),
				|best, (i, j)| {
					d1 = S2Edge.update_min_distance(at(va, i), at(vb, j), at(vb, j + 1), best) ?? best
					S2Edge.update_min_interior_distance(at(vb, i), at(va, j), at(va, j + 1), d1) ?? d1
				},
			)
		}
	}

	## The distance between the furthest points of two cells.
	max_distance_to_cell : S2Cell, S2Cell -> S1ChordAngle
	max_distance_to_cell = |cell, target| {
		# A cell that meets the antipodal image of the other is a straight
		# angle away from it. That image is the opposite face, with u and v
		# swapped.
		opposite_face = if (target.face >= 3) target.face - 3 else target.face + 3
		if cell.face == opposite_face and cell.uv.intersects(R2Rect.new(target.uv.y(), target.uv.x())) {
			return S1ChordAngle.straight()
		}
		va = vertices(cell)
		vb = vertices(target)
		pairs(4).fold(
			S1ChordAngle.negative(),
			|best, (i, j)| {
				d1 = S2Edge.update_max_distance(at(va, i), at(vb, j), at(vb, j + 1), best) ?? best
				S2Edge.update_max_distance(at(vb, i), at(va, j), at(va, j + 1), d1) ?? d1
			},
		)
	}

	## True when the distance between the cells is less than `limit`.
	##
	## Faster than comparing `distance_to_cell`, because it stops at the first
	## pair of points closer than the limit.
	is_distance_less : S2Cell, S2Cell, S1ChordAngle -> Bool
	is_distance_less = |cell, target, limit| {
		if limit <= S1ChordAngle.zero() {
			return Bool.False
		}
		if cell.face == target.face {
			match furthest_edge(cell, target) {
				Err(Touching) => Bool.True
				Ok(ai) => {
					bi = ai.bitwise_xor(2)
					va1 = cell.vertex(ai)
					va2 = cell.vertex(ai + 1)
					vb1 = target.vertex(bi)
					vb2 = target.vertex(bi + 1)
					S2Edge.update_min_distance(va1, vb1, vb2, limit).is_ok()
						or S2Edge.update_min_distance(va2, vb1, vb2, limit).is_ok()
						or S2Edge.update_min_interior_distance(vb1, va1, va2, limit).is_ok()
						or S2Edge.update_min_interior_distance(vb2, va1, va2, limit).is_ok()
				}
			}
		} else {
			va = vertices(cell)
			vb = vertices(target)
			pairs(4).any(
				|(i, j)|
					S2Edge.update_min_distance(at(va, i), at(vb, j), at(vb, j + 1), limit).is_ok()
						or S2Edge.update_min_interior_distance(at(vb, i), at(va, j), at(va, j + 1), limit).is_ok(),
			)
		}
	}

	## True when the distance between the cells is at most `limit`.
	is_distance_less_or_equal : S2Cell, S2Cell, S1ChordAngle -> Bool
	is_distance_less_or_equal = |cell, target, limit| cell.distance_to_cell(target) <= limit

	## True when the distance between the furthest points of the cells is
	## less than `limit`.
	is_max_distance_less : S2Cell, S2Cell, S1ChordAngle -> Bool
	is_max_distance_less = |cell, target, limit| cell.max_distance_to_cell(target) < limit

	## True when the distance between the furthest points of the cells is at
	## most `limit`.
	is_max_distance_less_or_equal : S2Cell, S2Cell, S1ChordAngle -> Bool
	is_max_distance_less_or_equal = |cell, target, limit| cell.max_distance_to_cell(target) <= limit

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
expect {
	# The bound grows by 5/3 of machine epsilon, so on face 0 the upper u bound
	# 1 rounds up to 1 + 2^-51. A point at u = 1 + 2^-51 is inside, and one at
	# u = 1 + 3 * 2^-52 is outside.
	cell = S2Cell.from_face(0)
	cell.contains_point(S2Point.new(1.0, 1.0000000000000004, 0.0))
		and !cell.contains_point(S2Point.new(1.0, 1.0000000000000007, 0.0))
}

## The distance from `target_xyz` to the cell, or to its boundary when
## `to_interior` is false. Everything is computed in the `(u, v, w)`
## coordinates of the cell's face.
distance_internal : S2Cell, S2Point, Bool -> S1ChordAngle
distance_internal = |cell, target_xyz, to_interior| {
	target = S2Coords.face_xyz_to_uvw(cell.face, target_xyz)
	u0 = cell.uv.x().lo()
	u1 = cell.uv.x().hi()
	v0 = cell.uv.y().lo()
	v1 = cell.uv.y().hi()
	# Dot products with the four edge normals that face up or right: dir01
	# is the right edge, the upper end of the u axis.
	dir00 = target.x() - target.z() * u0
	dir01 = target.x() - target.z() * u1
	dir10 = target.y() - target.z() * v0
	dir11 = target.y() - target.z() * v1
	if dir00 < 0.0 and v_edge_is_closest(cell, target, 0) {
		return edge_distance(-dir00, u0)
	}
	if dir01 > 0.0 and v_edge_is_closest(cell, target, 1) {
		return edge_distance(dir01, u1)
	}
	if dir10 < 0.0 and u_edge_is_closest(cell, target, 0) {
		return edge_distance(-dir10, v0)
	}
	if dir11 > 0.0 and u_edge_is_closest(cell, target, 1) {
		return edge_distance(dir11, v1)
	}
	inside = dir00 >= 0.0 and dir01 <= 0.0 and dir10 >= 0.0 and dir11 <= 0.0
	if inside {
		if to_interior {
			S1ChordAngle.zero()
		} else {
			# A cell is a quadrilateral on the sphere rather than a rectangle,
			# so all four edges are candidates.
			edge_distance(-dir00, u0)
				.min(edge_distance(dir01, u1))
				.min(edge_distance(-dir10, v0).min(edge_distance(dir11, v1)))
		}
	} else {
		# The closest point is a vertex. The edge tests above do not narrow
		# down which one, since the edges do not meet at right angles.
		vertex_chord_distance(cell, target, 0, 0)
			.min(vertex_chord_distance(cell, target, 1, 0))
			.min(vertex_chord_distance(cell, target, 0, 1).min(vertex_chord_distance(cell, target, 1, 1)))
	}
}

## The distance from `p`, in `(u, v, w)` coordinates, to the corner `(i, j)`
## of the cell.
vertex_chord_distance : S2Cell, S2Point, U64, U64 -> S1ChordAngle
vertex_chord_distance = |cell, p, i, j|
	S1ChordAngle.from_points(p, S2Point.new(cell.uv.x().bound(i), cell.uv.y().bound(j), 1.0).normalize())

## True when `p`, in `(u, v, w)` coordinates, is closer to the interior of
## the lower (`v_end` 0) or upper (`v_end` 1) edge than to either of its
## endpoints.
u_edge_is_closest : S2Cell, S2Point, U64 -> Bool
u_edge_is_closest = |cell, p, v_end| {
	u0 = cell.uv.x().lo()
	u1 = cell.uv.x().hi()
	v = cell.uv.y().bound(v_end)
	# The normals of the planes perpendicular to the edge through each of its
	# endpoints.
	dir0 = S2Point.new(v * v + 1.0, -u0 * v, -u0)
	dir1 = S2Point.new(v * v + 1.0, -u1 * v, -u1)
	p.dot(dir0) > 0.0 and p.dot(dir1) < 0.0
}

## As `u_edge_is_closest`, for the left (`u_end` 0) or right (`u_end` 1)
## edge.
v_edge_is_closest : S2Cell, S2Point, U64 -> Bool
v_edge_is_closest = |cell, p, u_end| {
	v0 = cell.uv.y().lo()
	v1 = cell.uv.y().hi()
	u = cell.uv.x().bound(u_end)
	dir0 = S2Point.new(-u * v0, u * u + 1.0, -v0)
	dir1 = S2Point.new(-u * v1, u * u + 1.0, -v1)
	p.dot(dir0) > 0.0 and p.dot(dir1) < 0.0
}

## The distance from a point to a u or v edge at coordinate `uv`, given the
## dot product `dir` of the point with the edge's normal.
edge_distance : F64, F64 -> S1ChordAngle
edge_distance = |dir, uv| {
	# PR^2 = PQ^2 + QR^2, where Q is P projected onto the plane of the edge
	# and R the closest point of the edge.
	pq2 = (dir * dir) / (1.0 + uv * uv)
	qr = 1.0 - (1.0 - pq2).sqrt()
	S1ChordAngle.from_length2(pq2 + qr * qr)
}

## For two cells on the same face, the edge of `a` that is furthest from the
## opposite edge of `b` in the direction of `b`, or `Err(Touching)` when the
## cells meet, even at a single point.
furthest_edge : S2Cell, S2Cell -> Try(U64, [Touching])
furthest_edge = |a, b| {
	a_uv = a.uv
	b_uv = b.uv
	candidates = [
		(a_uv.x().lo() - b_uv.x().hi(), 3),
		(b_uv.x().lo() - a_uv.x().hi(), 1),
		(a_uv.y().lo() - b_uv.y().hi(), 0),
		(b_uv.y().lo() - a_uv.y().hi(), 2),
	]
	(_, found) = candidates.fold(
		(0.0, Err(Touching)),
		|(max_dist, best), (dist, edge)| if (dist > max_dist) (dist, Ok(edge)) else (max_dist, best),
	)
	found
}

## The four vertices of the cell.
vertices : S2Cell -> List(S2Point)
vertices = |cell| [cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3)]

## The vertex `k` of a list of four, wrapping around.
at : List(S2Point), U64 -> S2Point
at = |v, k| v.get(k % 4) ?? S2Point.zero()

## Every pair `(i, j)` with both in `[0, n)`, with `i` varying slowest.
pairs : U64 -> List((U64, U64))
pairs = |n| (0.U64).until(n).fold([], |acc, i| (0.U64).until(n).fold(acc, |inner, j| inner.append((i, j))))

# Distances from a point to a cell, its boundary, and its furthest point,
# from upstream's S2Cell::GetDistance, GetBoundaryDistance and
# GetMaxDistance.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	p = S2LatLng.from_degrees(10.0, 20.0).to_point()
	cell.distance_to_point(p).length2() == 3.654442721693221
		and cell.boundary_distance_to_point(p).length2() == 3.654442721693221
		and cell.max_distance_to_point(p).length2() == 3.6699361475234324
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	p = S2LatLng.from_degrees(-30.0, 100.0).to_point()
	cell.distance_to_point(p).length2() == 1.4182021349134346
		and cell.boundary_distance_to_point(p).length2() == 1.4182021349134346
		and cell.max_distance_to_point(p).length2() == 1.7661906938443481
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	p = S2Point.new(1.0, 0.0, 0.0).normalize()
	cell.distance_to_point(p).length2() == 0.8452975039156431
		and cell.boundary_distance_to_point(p).length2() == 0.8452975039156431
		and cell.max_distance_to_point(p).length2() == 0.8452994616207485
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	p = S2Point.new(-1.0, -1.0, 0.2).normalize()
	cell.distance_to_point(p).length2() == 1.8377481125934685
		and cell.boundary_distance_to_point(p).length2() == 1.8377481125934685
		and cell.max_distance_to_point(p).length2() == 1.8383797757168592
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	p = S2Point.new(0.0, 0.0, -1.0)
	cell.distance_to_point(p).length2() == 0.0
		and cell.boundary_distance_to_point(p).length2() == 0.585786437626905
		and cell.max_distance_to_point(p).length2() == 0.8452994616207485
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	p = S2LatLng.from_degrees(0.0, 0.0).to_point()
	cell.distance_to_point(p).length2() == 0.585786437626905
		and cell.boundary_distance_to_point(p).length2() == 0.585786437626905
		and cell.max_distance_to_point(p).length2() == 3.414213562373095
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	p = S2LatLng.from_degrees(5.0, 5.0).to_point()
	cell.distance_to_point(p).length2() == 0.007610603816508934
		and cell.boundary_distance_to_point(p).length2() == 0.007610603816508934
		and cell.max_distance_to_point(p).length2() == 0.29022741015810605
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	p = S2LatLng.from_degrees(1.0, 95.0).to_point()
	cell.distance_to_point(p).length2() == 0.8263675422198626
		and cell.boundary_distance_to_point(p).length2() == 0.8263675422198626
		and cell.max_distance_to_point(p).length2() == 0.8263675465861035
}
# Distances from an edge to a cell, from upstream's S2Cell::GetDistance and
# GetMaxDistance for edges.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	cell.distance_to_edge(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(12.0, 25.0).to_point()).length2() == 3.654442721693221
		and cell.max_distance_to_edge(S2LatLng.from_degrees(10.0, 20.0).to_point(), S2LatLng.from_degrees(12.0, 25.0).to_point()).length2() == 3.7427377502634784
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	cell.distance_to_edge(S2LatLng.from_degrees(-30.0, 100.0).to_point(), S2LatLng.from_degrees(30.0, 100.0).to_point()).length2() == 0.41074469833158994
		and cell.max_distance_to_edge(S2LatLng.from_degrees(-30.0, 100.0).to_point(), S2LatLng.from_degrees(30.0, 100.0).to_point()).length2() == 1.7661906938443481
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	cell.distance_to_edge(S2LatLng.from_degrees(0.0, -10.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()).length2() == 0.6623285551691742
		and cell.max_distance_to_edge(S2LatLng.from_degrees(0.0, -10.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()).length2() == 1.0633536016373228
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	cell.distance_to_edge(S2LatLng.from_degrees(-10.0, -10.0).to_point(), S2LatLng.from_degrees(-20.0, -20.0).to_point()).length2() == 0.15212730343960795
		and cell.max_distance_to_edge(S2LatLng.from_degrees(-10.0, -10.0).to_point(), S2LatLng.from_degrees(-20.0, -20.0).to_point()).length2() == 3.1767925524718983
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	cell.distance_to_edge(S2LatLng.from_degrees(80.0, 0.0).to_point(), S2LatLng.from_degrees(80.0, 90.0).to_point()).length2() == 0.6621706095410638
		and cell.max_distance_to_edge(S2LatLng.from_degrees(80.0, 0.0).to_point(), S2LatLng.from_degrees(80.0, 90.0).to_point()).length2() == 1.0638907687100527
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	cell.distance_to_edge(S2LatLng.from_degrees(10.0, 170.0).to_point(), S2LatLng.from_degrees(-10.0, -170.0).to_point()).length2() == 0.3470822564667091
		and cell.max_distance_to_edge(S2LatLng.from_degrees(10.0, 170.0).to_point(), S2LatLng.from_degrees(-10.0, -170.0).to_point()).length2() == 3.652917743533291
}
# Distances between cells, from upstream's S2Cell::GetDistance and
# GetMaxDistance for cells, with the cells of the tests named in the comments.
# Each limit is the distance itself, so that "less" and "less or equal"
# differ, and a little more and less.
# GetDistanceToCellHighDifferenceExample
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	cell.distance_to_cell(target).length2() == 1.5371096051531166 and cell.max_distance_to_cell(target).length2() == 1.5829613948022998
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	limit = S1ChordAngle.from_length2(1.5371096051531166)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	limit = S1ChordAngle.from_length2(1.5371096051531166)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	limit = S1ChordAngle.from_length2(1.5371096051531166)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	limit = S1ChordAngle.from_length2(1.5829613948022998)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	limit = S1ChordAngle.from_length2(1.5829613948022998)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(9425259963900493824))
	target = S2Cell.from_cell_id(S2CellId.from_id(10565374357067005952))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.False
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
# GetDistanceToCellProjectionExample1
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	cell.distance_to_cell(target).length2() == 1.1848020234480885 and cell.max_distance_to_cell(target).length2() == 1.6103627624083112
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.1848020234480885)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.1848020234480885)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.1848020234480885)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.6103627624083112)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.6103627624083112)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2341884504082166412))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.False
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
# GetDistanceToCellProjectionExample2
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	cell.distance_to_cell(target).length2() == 1.1405944420980945 and cell.max_distance_to_cell(target).length2() == 1.5622602735510942
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	limit = S1ChordAngle.from_length2(1.1405944420980945)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	limit = S1ChordAngle.from_length2(1.1405944420980945)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	limit = S1ChordAngle.from_length2(1.1405944420980945)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	limit = S1ChordAngle.from_length2(1.5622602735510942)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	limit = S1ChordAngle.from_length2(1.5622602735510942)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5367593936036560896))
	target = S2Cell.from_cell_id(S2CellId.from_id(6142909891733356544))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.False
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
# IsDistanceLess, adjacent
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	cell.distance_to_cell(target).length2() == 0.0 and cell.max_distance_to_cell(target).length2() == 0.4387248041078994
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	limit = S1ChordAngle.from_length2(1.0000000000000001e-20)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	limit = S1ChordAngle.from_length2(0.4387248041078994)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	limit = S1ChordAngle.from_length2(0.4387248041078994)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(1170935903116328960))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
# IsDistanceLess, adjacent
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	cell.distance_to_cell(target).length2() == 0.0 and cell.max_distance_to_cell(target).length2() == 1.8341946655420642
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	limit = S1ChordAngle.from_length2(1.0000000000000001e-20)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	limit = S1ChordAngle.from_length2(1.8341946655420642)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	limit = S1ChordAngle.from_length2(1.8341946655420642)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(864691128455135232))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
# IsDistanceLess, not adjacent
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	cell.distance_to_cell(target).length2() == 1.2307692307692308 and cell.max_distance_to_cell(target).length2() == 2.9388683612693494
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	limit = S1ChordAngle.from_length2(1.2307692307692308)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	limit = S1ChordAngle.from_length2(1.2307692307692308)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	limit = S1ChordAngle.from_length2(1.2307692307692308)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	limit = S1ChordAngle.from_length2(2.9388683612693494)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	limit = S1ChordAngle.from_length2(2.9388683612693494)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1945555039024054272))
	target = S2Cell.from_cell_id(S2CellId.from_id(10304235947423694848))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.False
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	cell.distance_to_cell(target).length2() == 3.9999999054226625 and cell.max_distance_to_cell(target).length2() == 4.0
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	limit = S1ChordAngle.from_length2(3.9999999054226625)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	limit = S1ChordAngle.from_length2(3.9999999054226625)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	limit = S1ChordAngle.from_length2(3.9999999054226625)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	limit = S1ChordAngle.from_length2(4.0)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	limit = S1ChordAngle.from_length2(4.0)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(1048576))
	target = S2Cell.from_cell_id(S2CellId.from_id(6917529096360558592))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.False
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	cell.distance_to_cell(target).length2() == 1.0362002528498804 and cell.max_distance_to_cell(target).length2() == 4.0
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.0362002528498804)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.0362002528498804)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(1.0362002528498804)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(4.0)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(4.0)
	cell.is_distance_less(target, limit) == Bool.True
		and cell.is_distance_less_or_equal(target, limit) == Bool.True
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(12682136550675316736))
	target = S2Cell.from_cell_id(S2CellId.from_id(4593671619917905920))
	limit = S1ChordAngle.from_length2(0.0)
	cell.is_distance_less(target, limit) == Bool.False
		and cell.is_distance_less_or_equal(target, limit) == Bool.False
		and cell.is_max_distance_less(target, limit) == Bool.False
		and cell.is_max_distance_less_or_equal(target, limit) == Bool.False
}

# Pairs of cells on the same face, on every side of each other, where
# upstream compares only the two facing edges.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4097994185930440704))
	cell.distance_to_cell(target).length2() == 0.0 and cell.max_distance_to_cell(target).length2() == 0.002962304919778112
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4092927636349648896))
	cell.distance_to_cell(target).length2() == 0.000838202066327192 and cell.max_distance_to_cell(target).length2() == 0.007534074161771757
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4179621929176530944))
	cell.distance_to_cell(target).length2() == 0.1000851927873334 and cell.max_distance_to_cell(target).length2() == 0.142007737870441
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4034943791147253760))
	cell.distance_to_cell(target).length2() == 0.08444374102409748 and cell.max_distance_to_cell(target).length2() == 0.12135813491564629
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4143593132157566976))
	cell.distance_to_cell(target).length2() == 0.03968446503850982 and cell.max_distance_to_cell(target).length2() == 0.06836372597838439
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4044513940355416064))
	cell.distance_to_cell(target).length2() == 0.06024329732521473 and cell.max_distance_to_cell(target).length2() == 0.08939741349468014
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(2753669697160347648))
	cell.distance_to_cell(target).length2() == 1.1817926611283667 and cell.max_distance_to_cell(target).length2() == 1.2817975292454895
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(3395995594014064640))
	cell.distance_to_cell(target).length2() == 0.8793905329293809 and cell.max_distance_to_cell(target).length2() == 0.9839736986824591
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4097994185930440704))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.0 and cell.max_distance_to_cell(target).length2() == 0.002962304919778112
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4092927636349648896))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.000838202066327192 and cell.max_distance_to_cell(target).length2() == 0.007534074161771757
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4179621929176530944))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.1000851927873334 and cell.max_distance_to_cell(target).length2() == 0.142007737870441
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4034943791147253760))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.08444374102409748 and cell.max_distance_to_cell(target).length2() == 0.12135813491564629
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4143593132157566976))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.03968446503850982 and cell.max_distance_to_cell(target).length2() == 0.06836372597838439
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4044513940355416064))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.06024329732521473 and cell.max_distance_to_cell(target).length2() == 0.08939741349468014
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2753669697160347648))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 1.1817926611283667 and cell.max_distance_to_cell(target).length2() == 1.2817975292454895
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(3395995594014064640))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.distance_to_cell(target).length2() == 0.8793905329293809 and cell.max_distance_to_cell(target).length2() == 0.9839736986824591
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4092927636349648896))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.000838202066327192)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.0008382021501473987)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4179621929176530944))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.1000851927873334)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.10008520279585269)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4034943791147253760))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.08444374102409748)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.08444374946847158)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4143593132157566976))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.03968446503850982)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.03968446900695633)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(4044513940355416064))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.06024329732521473)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.06024330334954447)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(2753669697160347648))
	cell.is_distance_less(target, S1ChordAngle.from_length2(1.1817926611283667)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(1.1817927793076328)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	target = S2Cell.from_cell_id(S2CellId.from_id(3395995594014064640))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.8793905329293809)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.8793906208684342)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4092927636349648896))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.000838202066327192)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.0008382021501473987)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4179621929176530944))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.1000851927873334)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.10008520279585269)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4034943791147253760))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.08444374102409748)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.08444374946847158)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4143593132157566976))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.03968446503850982)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.03968446900695633)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(4044513940355416064))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.06024329732521473)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.06024330334954447)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(2753669697160347648))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(1.1817926611283667)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(1.1817927793076328)) == Bool.True
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(3395995594014064640))
	target = S2Cell.from_cell_id(S2CellId.from_id(4096305336070176768))
	cell.is_distance_less(target, S1ChordAngle.from_length2(0.8793905329293809)) == Bool.False
		and cell.is_distance_less(target, S1ChordAngle.from_length2(0.8793906208684342)) == Bool.True
}

# Upstream's GetMaxDistanceToCellAntipodal: a leaf cell and the leaf cell of
# the antipode of a point inside it are a straight angle apart.
expect {
	p = S2LatLng.from_degrees(0.0, 0.0).to_point()
	S2Cell.from_point(p).max_distance_to_cell(S2Cell.from_point(-p)) == S1ChordAngle.straight()
}

# Upstream's GetMaxDistanceToEdge: an edge whose antipodal image crosses the
# cell is a straight angle from it, to within 1e-15 radians.
expect {
	cell = S2Cell.from_face_pos_level(0, 0, 20)
	a = -S2Edge.interpolate(cell.center(), cell.vertex(0), 2.0)
	b = -S2Edge.interpolate(cell.center(), cell.vertex(2), 2.0)
	(cell.max_distance_to_edge(a, b).radians() - F64.pi).abs() <= 1e-15
}
expect S2Cell.from_cell_id(S2CellId.from_face(2).child(1).child(3)).size_ij() == 268435456
expect S2Cell.from_cell_id(S2CellId.from_face(2).child(1).child(3)).size_st() == 0.25

# A cell bounds itself, as upstream's S2Cell::GetCellUnionBound does, so a
# coverer that may use the cell's level returns the cell.
expect S2Cell.from_cell_id(S2CellId.from_id(9926595690882924544)).cell_union_bound() == [9926595690882924544].map(S2CellId.from_id)

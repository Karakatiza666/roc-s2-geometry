import R2Point
import S2Coords
import S2LatLng
import Internal/S2Lookup
import S2Point

## A cell in S2's hierarchical decomposition of the sphere, encoded in 64 bits.
##
## The encoding is 3 bits of cube face, then up to 60 bits of position along a
## Hilbert curve over that face, then a single trailing 1 bit whose position
## records the level. That trailing bit is the *lsb*, and everything about a
## cell id follows from it: cells at level `n` have their lsb at bit
## `2 * (30 - n)`, a cell's descendants form a contiguous id range, and
## `id / 2` compares cells in Hilbert order.
##
##     S2CellId.from_lat_lng(S2LatLng.from_degrees(37.77, -122.42))
##         .parent_at_level(10)
##         .to_token()
S2CellId := { id : U64 }.{

	## The finest level, at which cells are roughly 1 cm across.
	max_level : U64
	max_level = 30

	## The number of leaf cells along one edge of a face.
	max_size : U64
	max_size = 1073741824

	## The number of bits a cell id spends on Hilbert position plus the level
	## marker.
	pos_bits : U8
	pos_bits = 61

	## The id one past the last valid cell id, `6 << pos_bits`. Wrapping
	## traversal adds or subtracts this.
	wrap_offset : U64
	wrap_offset = 13835058055282163712

	## The cell id with the given 64-bit encoding, whether or not it is valid.
	from_id : U64 -> S2CellId
	from_id = |value| { id: value }

	## The invalid cell id zero, used as a "no cell" sentinel.
	none : () -> S2CellId
	none = || { id: 0 }

	## An id larger than any valid cell id, useful as an exclusive upper bound.
	sentinel : () -> S2CellId
	sentinel = || { id: U64.highest }

	## The level-0 cell covering the given face.
	from_face : U64 -> S2CellId
	from_face = |face_index| {
		id: face_index.shl_wrap(S2CellId.pos_bits).plus_wrap(S2CellId.lsb_for_level(0)),
	}

	## The cell at the given level whose Hilbert position on `face` is `pos`.
	from_face_pos_level : U64, U64, U64 -> S2CellId
	from_face_pos_level = |face_index, position, target_level|
		S2CellId.from_id(face_index.shl_wrap(S2CellId.pos_bits).plus_wrap(position.bitwise_or(1)))
			.parent_at_level(target_level)

	## The leaf cell containing the given position.
	from_lat_lng : S2LatLng -> S2CellId
	from_lat_lng = |ll| S2CellId.from_point(ll.to_point())

	## The leaf cell containing the given point, which need not be unit length.
	from_point : S2Point -> S2CellId
	from_point = |p| {
		(face, uv) = S2Coords.xyz_to_face_uv(p)
		i = S2Coords.st_to_ij(S2Coords.uv_to_st(uv.x()))
		j = S2Coords.st_to_ij(S2Coords.uv_to_st(uv.y()))
		S2CellId.from_face_ij(face, i, j)
	}

	## The 64-bit encoding.
	id : S2CellId -> U64
	id = |c| c.id

	## The lowest set bit, which encodes the cell's level.
	lsb : S2CellId -> U64
	lsb = |c| c.id.bitwise_and(c.id.bitwise_not().plus_wrap(1))

	## The lowest set bit a cell at the given level has.
	lsb_for_level : U64 -> U64
	lsb_for_level = |target_level|
		(1.U64).shl_wrap((2 * (S2CellId.max_level - target_level)).to_u8_wrap())

	## True when the id encodes a real cell: a face in range and a level
	## marker in an odd bit position.
	is_valid : S2CellId -> Bool
	is_valid = |c|
		c.face() < S2Coords.num_faces and c.lsb().bitwise_and(0x1555555555555555) != 0

	## The cube face the cell lies on.
	face : S2CellId -> U64
	face = |c| c.id.shr_zf_wrap(S2CellId.pos_bits)

	## The cell's position along the Hilbert curve over its face, including
	## the level marker.
	pos : S2CellId -> U64
	pos = |c| c.id.bitwise_and(U64.highest.shr_zf_wrap(3))

	## True for a level-0 cell, which covers a whole face.
	is_face : S2CellId -> Bool
	is_face = |c| c.id.bitwise_and(S2CellId.lsb_for_level(0) - 1) == 0

	## True for a level-30 cell, which has no children.
	is_leaf : S2CellId -> Bool
	is_leaf = |c| c.id.bitwise_and(1) != 0

	## The subdivision level, from 0 for a face cell to 30 for a leaf cell.
	level : S2CellId -> U64
	level = |c| S2CellId.max_level - (c.id.count_trailing_zero_bits() / 2).to_u64()

	## Which of its parent's four children this cell is, in Hilbert order.
	child_position : S2CellId -> U64
	child_position = |c| c.child_position_at_level(c.level())

	## Which child this cell's ancestor at `level` is of its own parent.
	child_position_at_level : S2CellId, U64 -> U64
	child_position_at_level = |c, target_level|
		c.id
			.shr_zf_wrap((2 * (S2CellId.max_level - target_level) + 1).to_u8_wrap())
			.bitwise_and(3)

	## The cell one level up. Undefined for a face cell.
	parent : S2CellId -> S2CellId
	parent = |c| {
		new_lsb = c.lsb().shl_wrap(2)
		{ id: c.id.bitwise_and(new_lsb.bitwise_not().plus_wrap(1)).bitwise_or(new_lsb) }
	}

	## The ancestor at the given level, which must not be finer than this
	## cell's own level.
	parent_at_level : S2CellId, U64 -> S2CellId
	parent_at_level = |c, target_level| {
		new_lsb = S2CellId.lsb_for_level(target_level)
		{ id: c.id.bitwise_and(new_lsb.bitwise_not().plus_wrap(1)).bitwise_or(new_lsb) }
	}

	## The child at the given Hilbert position `0..3`.
	child : S2CellId, U64 -> S2CellId
	child = |c, position| {
		new_lsb = c.lsb().shr_zf_wrap(2)
		{ id: c.id.plus_wrap((2 * position + 1).minus_wrap(4).times_wrap(new_lsb)) }
	}

	## The first child in Hilbert order.
	child_begin : S2CellId -> S2CellId
	child_begin = |c| {
		old_lsb = c.lsb()
		{ id: c.id.minus_wrap(old_lsb).plus_wrap(old_lsb.shr_zf_wrap(2)) }
	}

	## The first descendant at the given level, in Hilbert order.
	child_begin_at_level : S2CellId, U64 -> S2CellId
	child_begin_at_level = |c, target_level|
		{ id: c.id.minus_wrap(c.lsb()).plus_wrap(S2CellId.lsb_for_level(target_level)) }

	## One past the last child, in Hilbert order.
	child_end : S2CellId -> S2CellId
	child_end = |c| {
		old_lsb = c.lsb()
		{ id: c.id.plus_wrap(old_lsb).plus_wrap(old_lsb.shr_zf_wrap(2)) }
	}

	## One past the last descendant at the given level, in Hilbert order.
	child_end_at_level : S2CellId, U64 -> S2CellId
	child_end_at_level = |c, target_level|
		{ id: c.id.plus_wrap(c.lsb()).plus_wrap(S2CellId.lsb_for_level(target_level)) }

	## The four children, in Hilbert order.
	children : S2CellId -> List(S2CellId)
	children = |c| [c.child(0), c.child(1), c.child(2), c.child(3)]

	## Every descendant at the given level, in Hilbert order.
	##
	## The count is `4 ^ (level - this level)`, so this is only practical for
	## a few levels down.
	children_at_level : S2CellId, U64 -> List(S2CellId)
	children_at_level = |c, target_level| {
		last = c.child_end_at_level(target_level)
		step = S2CellId.lsb_for_level(target_level).shl_wrap(1)
		var $current = c.child_begin_at_level(target_level).id
		var $out = []
		while $current != last.id {
			$out = $out.append({ id: $current })
			$current = $current.plus_wrap(step)
		}
		$out
	}

	## The first leaf cell contained by this one, which is the smallest id in
	## its range.
	range_min : S2CellId -> S2CellId
	range_min = |c| { id: c.id.minus_wrap(c.lsb() - 1) }

	## The last leaf cell contained by this one, which is the largest id in
	## its range.
	range_max : S2CellId -> S2CellId
	range_max = |c| { id: c.id.plus_wrap(c.lsb() - 1) }

	## True when `other` is this cell or one of its descendants.
	contains : S2CellId, S2CellId -> Bool
	contains = |c, other| other.id >= c.range_min().id and other.id <= c.range_max().id

	## True when either cell contains the other.
	intersects : S2CellId, S2CellId -> Bool
	intersects = |c, other|
		other.range_min().id <= c.range_max().id and other.range_max().id >= c.range_min().id

	## The finest level at which both cells share an ancestor, or
	## `Err(NoCommonAncestor)` when they are on different faces.
	common_ancestor_level : S2CellId, S2CellId -> Try(U64, [NoCommonAncestor])
	common_ancestor_level = |c, other| {
		bits = c.id.bitwise_xor(other.id).max(c.lsb()).max(other.lsb())
		msb_pos = 63 - bits.count_leading_zero_bits().to_u64()
		if msb_pos > 60 {
			Err(NoCommonAncestor)
		} else {
			Ok((60 - msb_pos) / 2)
		}
	}

	## The next cell at the same level in Hilbert order, running off the end
	## of the last face.
	next : S2CellId -> S2CellId
	next = |c| { id: c.id.plus_wrap(c.lsb().shl_wrap(1)) }

	## The previous cell at the same level in Hilbert order.
	prev : S2CellId -> S2CellId
	prev = |c| { id: c.id.minus_wrap(c.lsb().shl_wrap(1)) }

	## `next`, wrapping from the last face back to the first.
	next_wrap : S2CellId -> S2CellId
	next_wrap = |c| {
		n = c.next()
		if n.id < S2CellId.wrap_offset {
			n
		} else {
			{ id: n.id.minus_wrap(S2CellId.wrap_offset) }
		}
	}

	## `prev`, wrapping from the first face back to the last.
	prev_wrap : S2CellId -> S2CellId
	prev_wrap = |c| {
		p = c.prev()
		if p.id < S2CellId.wrap_offset {
			p
		} else {
			{ id: p.id.plus_wrap(S2CellId.wrap_offset) }
		}
	}

	## The cell `steps` positions along at this level, stopping at either end
	## of the curve.
	advance : S2CellId, I64 -> S2CellId
	advance = |c, steps| {
		if steps == 0 {
			return c
		}
		step_shift = (2 * (S2CellId.max_level - c.level()) + 1).to_u8_wrap()
		clamped =
			if steps < 0 {
				min_steps = -(c.id.shr_zf_wrap(step_shift).to_i64_wrap())
				steps.max(min_steps)
			} else {
				max_steps =
					S2CellId.wrap_offset
						.plus_wrap(c.lsb())
						.minus_wrap(c.id)
						.shr_zf_wrap(step_shift)
						.to_i64_wrap()
				steps.min(max_steps)
			}
		{ id: c.id.plus_wrap(clamped.to_u64_wrap().shl_wrap(step_shift)) }
	}

	## The cell `steps` positions along at this level, wrapping around the
	## curve rather than stopping.
	advance_wrap : S2CellId, I64 -> S2CellId
	advance_wrap = |c, steps| {
		if steps == 0 {
			return c
		}
		step_shift = (2 * (S2CellId.max_level - c.level()) + 1).to_u8_wrap()
		step_wrap = S2CellId.wrap_offset.shr_zf_wrap(step_shift).to_i64_wrap()
		wrapped =
			if steps < 0 {
				min_steps = -(c.id.shr_zf_wrap(step_shift).to_i64_wrap())
				if steps < min_steps {
					reduced = steps % step_wrap
					if reduced < min_steps {
						reduced + step_wrap
					} else {
						reduced
					}
				} else {
					steps
				}
			} else {
				max_steps =
					S2CellId.wrap_offset.minus_wrap(c.id).shr_zf_wrap(step_shift).to_i64_wrap()
				if steps > max_steps {
					reduced = steps % step_wrap
					if reduced > max_steps {
						reduced - step_wrap
					} else {
						reduced
					}
				} else {
					steps
				}
			}
		{ id: c.id.plus_wrap(wrapped.to_u64_wrap().shl_wrap(step_shift)) }
	}

	## The first cell at the given level, in Hilbert order.
	begin : U64 -> S2CellId
	begin = |target_level| S2CellId.from_face(0).child_begin_at_level(target_level)

	## One past the last cell at the given level, in Hilbert order.
	end : U64 -> S2CellId
	end = |target_level| S2CellId.from_face(5).child_end_at_level(target_level)

	## The number of leaf cells along one edge of this cell.
	size_ij : S2CellId -> U64
	size_ij = |c| S2CellId.size_ij_at_level(c.level())

	## The number of leaf cells along one edge of a cell at the given level.
	size_ij_at_level : U64 -> U64
	size_ij_at_level = |target_level| (1.U64).shl_wrap((S2CellId.max_level - target_level).to_u8_wrap())

	## The edge length of this cell in `(s, t)` coordinates.
	size_st : S2CellId -> F64
	size_st = |c| S2CellId.size_st_at_level(c.level())

	## The edge length in `(s, t)` coordinates of a cell at the given level.
	size_st_at_level : U64 -> F64
	size_st_at_level = |target_level|
		S2CellId.size_ij_at_level(target_level).to_f64() / S2Coords.max_size.to_f64()

	## The cell's face, `(i, j)` position, and Hilbert orientation.
	##
	## The orientation combines `S2Lookup.swap_mask` and
	## `S2Lookup.invert_mask`.
	to_face_ij_orientation : S2CellId -> { face : U64, i : U64, j : U64, orientation : U64 }
	to_face_ij_orientation = |c| {
		face_index = c.face()
		var $i = 0
		var $j = 0
		var $bits = face_index.bitwise_and(S2Lookup.swap_mask)
		for step in (0.U64).until(8) {
			k = 7 - step
			nbits = if k == 7 {
				2
			} else {
				4
			}
			shift = (k * 8 + 1).to_u8_wrap()
			mask = (1.U64).shl_wrap((2 * nbits).to_u8_wrap()) - 1
			$bits = $bits.plus_wrap(c.id.shr_zf_wrap(shift).bitwise_and(mask).shl_wrap(2))
			$bits = S2Lookup.ij_entry($bits)
			$i = $i.plus_wrap($bits.shr_zf_wrap(6).shl_wrap((k * 4).to_u8_wrap()))
			$j = $j.plus_wrap(
				$bits.shr_zf_wrap(2).bitwise_and(15).shl_wrap((k * 4).to_u8_wrap()),
			)
			$bits = $bits.bitwise_and(S2Lookup.swap_mask.bitwise_or(S2Lookup.invert_mask))
		}
		orientation =
			if c.lsb().bitwise_and(0x1111111111111110) != 0 {
				$bits.bitwise_xor(S2Lookup.swap_mask)
			} else {
				$bits
			}
		{ face: face_index, i: $i, j: $j, orientation: orientation }
	}

	## The leaf cell at the given `(i, j)` position on the given face.
	from_face_ij : U64, U64, U64 -> S2CellId
	from_face_ij = |face_index, i, j| {
		var $n = face_index.shl_wrap(S2CellId.pos_bits - 1)
		var $bits = face_index.bitwise_and(S2Lookup.swap_mask)
		for step in (0.U64).until(8) {
			k = 7 - step
			shift = (k * 4).to_u8_wrap()
			$bits = $bits.plus_wrap(i.shr_zf_wrap(shift).bitwise_and(15).shl_wrap(6))
			$bits = $bits.plus_wrap(j.shr_zf_wrap(shift).bitwise_and(15).shl_wrap(2))
			$bits = S2Lookup.pos_entry($bits)
			$n = $n.bitwise_or($bits.shr_zf_wrap(2).shl_wrap((k * 8).to_u8_wrap()))
			$bits = $bits.bitwise_and(S2Lookup.swap_mask.bitwise_or(S2Lookup.invert_mask))
		}
		{ id: $n.times_wrap(2).plus_wrap(1) }
	}

	## The leaf cell at `(i, j)` on `face`, following the cube's wrapping when
	## the position falls off the edge of the face.
	from_face_ij_wrap : U64, I64, I64 -> S2CellId
	from_face_ij_wrap = |face_index, i, j| {
		max_i = S2CellId.max_size.to_i64_wrap()
		clamped_i = i.max(-1).min(max_i)
		clamped_j = j.max(-1).min(max_i)

		# The linear projection is enough here, since the result is only used
		# to find which face the position lands on.
		scale = 1.0 / S2CellId.max_size.to_f64()
		u = scale * (clamped_i * 2 + 1 - max_i).to_f64()
		v = scale * (clamped_j * 2 + 1 - max_i).to_f64()

		(new_face, uv) = S2Coords.xyz_to_face_uv(S2Coords.face_uv_to_xyz(face_index, u, v))
		S2CellId.from_face_ij(
			new_face,
			S2Coords.st_to_ij(0.5 * (uv.x() + 1.0)),
			S2Coords.st_to_ij(0.5 * (uv.y() + 1.0)),
		)
	}

	## `from_face_ij` when `same_face` says the position is still on `face`,
	## and `from_face_ij_wrap` when it is not.
	from_face_ij_same : U64, I64, I64, Bool -> S2CellId
	from_face_ij_same = |face_index, i, j, same_face|
		if same_face {
			S2CellId.from_face_ij(face_index, i.to_u64_wrap(), j.to_u64_wrap())
		} else {
			S2CellId.from_face_ij_wrap(face_index, i, j)
		}

	## The cell's face and the `(si, ti)` of its centre, in half-leaf units.
	center_si_ti : S2CellId -> { face : U64, si : U64, ti : U64 }
	center_si_ti = |c| {
		ij = c.to_face_ij_orientation()
		delta =
			if c.is_leaf() {
				1
			} else if ij.i.bitwise_xor(c.id.shr_zf_wrap(2)).bitwise_and(1) != 0 {
				2
			} else {
				0
			}
		{ face: ij.face, si: 2 * ij.i + delta, ti: 2 * ij.j + delta }
	}

	## The `(u, v)` coordinate of the cell's centre on its own face.
	center_uv : S2CellId -> R2Point
	center_uv = |c| {
		center = c.center_si_ti()
		R2Point.new(
			S2Coords.st_to_uv(S2Coords.si_ti_to_st(center.si)),
			S2Coords.st_to_uv(S2Coords.si_ti_to_st(center.ti)),
		)
	}

	## The `(u, v)` extent of the cell on its own face, as `(u_lo, u_hi, v_lo,
	## v_hi)`.
	bound_uv : S2CellId -> (F64, F64, F64, F64)
	bound_uv = |c| {
		ij = c.to_face_ij_orientation()
		cell_size = c.size_ij()
		i_lo = ij.i.bitwise_and(cell_size.bitwise_not().plus_wrap(1))
		j_lo = ij.j.bitwise_and(cell_size.bitwise_not().plus_wrap(1))
		scale = 1.0 / S2Coords.max_size.to_f64()
		(
			S2Coords.st_to_uv(scale * i_lo.to_f64()),
			S2Coords.st_to_uv(scale * (i_lo + cell_size).to_f64()),
			S2Coords.st_to_uv(scale * j_lo.to_f64()),
			S2Coords.st_to_uv(scale * (j_lo + cell_size).to_f64()),
		)
	}

	## The centre of the cell, not normalized.
	to_point_raw : S2CellId -> S2Point
	to_point_raw = |c| {
		center = c.center_si_ti()
		S2Coords.face_uv_to_xyz(
			center.face,
			S2Coords.st_to_uv(S2Coords.si_ti_to_st(center.si)),
			S2Coords.st_to_uv(S2Coords.si_ti_to_st(center.ti)),
		)
	}

	## The centre of the cell as a unit vector.
	to_point : S2CellId -> S2Point
	to_point = |c| c.to_point_raw().normalize()

	## The centre of the cell in latitude and longitude.
	to_lat_lng : S2CellId -> S2LatLng
	to_lat_lng = |c| S2LatLng.from_point(c.to_point_raw())

	## The four cells sharing an edge with this one, in the order south,
	## east, north, west.
	edge_neighbors : S2CellId -> List(S2CellId)
	edge_neighbors = |c| {
		cell_level = c.level()
		size = c.size_ij().to_i64_wrap()
		ij = c.to_face_ij_orientation()
		i = ij.i.to_i64_wrap()
		j = ij.j.to_i64_wrap()
		max_ij = S2CellId.max_size.to_i64_wrap()
		[
			S2CellId.from_face_ij_same(ij.face, i, j - size, j - size >= 0)
				.parent_at_level(cell_level),
			S2CellId.from_face_ij_same(ij.face, i + size, j, i + size < max_ij)
				.parent_at_level(cell_level),
			S2CellId.from_face_ij_same(ij.face, i, j + size, j + size < max_ij)
				.parent_at_level(cell_level),
			S2CellId.from_face_ij_same(ij.face, i - size, j, i - size >= 0)
				.parent_at_level(cell_level),
		]
	}

	## The cells at `level` that touch the vertex of this cell closest to its
	## centre.
	##
	## There are four, except at the eight corners of the cube where there are
	## three. `level` must be strictly coarser than this cell's level.
	vertex_neighbors : S2CellId, U64 -> List(S2CellId)
	vertex_neighbors = |c, target_level| {
		ij = c.to_face_ij_orientation()
		i = ij.i.to_i64_wrap()
		j = ij.j.to_i64_wrap()
		max_ij = S2CellId.max_size.to_i64_wrap()

		halfsize = S2CellId.size_ij_at_level(target_level + 1).to_i64_wrap()
		size = halfsize * 2

		(ioffset, isame) =
			if i.bitwise_and(halfsize) != 0 {
				(size, i + size < max_ij)
			} else {
				(-size, i - size >= 0)
			}
		(joffset, jsame) =
			if j.bitwise_and(halfsize) != 0 {
				(size, j + size < max_ij)
			} else {
				(-size, j - size >= 0)
			}

		base = [
			c.parent_at_level(target_level),
			S2CellId.from_face_ij_same(ij.face, i + ioffset, j, isame)
				.parent_at_level(target_level),
			S2CellId.from_face_ij_same(ij.face, i, j + joffset, jsame)
				.parent_at_level(target_level),
		]
		if isame or jsame {
			base.append(
				S2CellId.from_face_ij_same(
					ij.face,
					i + ioffset,
					j + joffset,
					isame and jsame,
				)
					.parent_at_level(target_level),
			)
		} else {
			base
		}
	}

	## Every cell at `nbr_level` that touches this cell's boundary, without
	## the cell itself.
	##
	## `nbr_level` must be at least this cell's level. Neighbors that touch
	## only at a corner are included once each.
	all_neighbors : S2CellId, U64 -> List(S2CellId)
	all_neighbors = |c, nbr_level| {
		ij = c.to_face_ij_orientation()
		size = c.size_ij().to_i64_wrap()
		max_ij = S2CellId.max_size.to_i64_wrap()

		# Normalize to the lower-left leaf cell, since nbr_level may be finer
		# than this cell's own level.
		i = ij.i.to_i64_wrap().bitwise_and(-size)
		j = ij.j.to_i64_wrap().bitwise_and(-size)
		nbr_size = S2CellId.size_ij_at_level(nbr_level).to_i64_wrap()

		var $out = []
		var $k = -nbr_size
		while Bool.True {
			same_face =
				if $k < 0 {
					j + $k >= 0
				} else if $k >= size {
					j + $k < max_ij
				} else {
					# North and south neighbors, emitted once per column.
					$out = $out
						.append(
							S2CellId.from_face_ij_same(ij.face, i + $k, j - nbr_size, j - size >= 0)
								.parent_at_level(nbr_level),
						)
						.append(
							S2CellId.from_face_ij_same(ij.face, i + $k, j + size, j + size < max_ij)
								.parent_at_level(nbr_level),
						)
					Bool.False
				}
			$out = $out
				.append(
					S2CellId.from_face_ij_same(
						ij.face,
						i - nbr_size,
						j + $k,
						same_face and i - size >= 0,
					)
						.parent_at_level(nbr_level),
				)
				.append(
					S2CellId.from_face_ij_same(
						ij.face,
						i + size,
						j + $k,
						same_face and i + size < max_ij,
					)
						.parent_at_level(nbr_level),
				)
			if $k >= size {
				break
			}
			$k = $k + nbr_size
		}
		$out
	}

	## The cell id as a hex token with trailing zeros stripped, which is the
	## compact form S2 uses in URLs and logs. The invalid id is `"X"`.
	to_token : S2CellId -> Str
	to_token = |c| {
		if c.id == 0 {
			return "X"
		}
		var $digits = []
		for nibble_index in (0.U64).until(16) {
			shift = ((15 - nibble_index) * 4).to_u8_wrap()
			$digits = $digits.append(c.id.shr_zf_wrap(shift).bitwise_and(15))
		}
		var $len = 16
		while $len > 1 and ($digits.get($len - 1) ?? 0) == 0 {
			$len = $len - 1
		}
		$digits
			.take_first($len)
			.map(|d| S2CellId.hex_digits.get(d) ?? "0")
			|> Str.join_with("")
	}

	## The cell id a hex token names, or `Err(BadToken)` when the token is not
	## 1 to 16 hex digits.
	from_token : Str -> Try(S2CellId, [BadToken])
	from_token = |token| {
		if token == "X" {
			return Ok(S2CellId.none())
		}
		bytes = token.to_utf8()
		if bytes.is_empty() or bytes.len() > 16 {
			return Err(BadToken)
		}
		var $value = 0
		for byte in bytes {
			digit = S2CellId.hex_value(byte)?
			$value = $value.shl_wrap(4).bitwise_or(digit)
		}
		Ok({ id: $value.shl_wrap((4 * (16 - bytes.len())).to_u8_wrap()) })
	}

	## The face and Hilbert child positions, as `"2/301"`, which is the form
	## upstream prints cell ids in.
	to_debug_str : S2CellId -> Str
	to_debug_str = |c| {
		if !c.is_valid() {
			return "Invalid: ${c.id.to_str()}"
		}
		cell_level = c.level()
		var $out = "${c.face().to_str()}/"
		for depth in (1.U64).to(cell_level) {
			$out = $out.concat(c.child_position_at_level(depth).to_str())
		}
		$out
	}

	## The cell a debug string such as `"2/301"` names.
	from_debug_str : Str -> Try(S2CellId, [BadDebugStr])
	from_debug_str = |text| {
		parts = text.split_on("/")
		when_two =
			match parts {
				[face_str, positions] => Ok((face_str, positions))
				_ => Err(BadDebugStr)
			}
		(face_str, positions) = when_two?
		face_index = U64.from_str(face_str) ? |_| BadDebugStr
		if face_index >= S2Coords.num_faces {
			return Err(BadDebugStr)
		}
		digits = positions.to_utf8()
		if digits.len() > S2CellId.max_level {
			return Err(BadDebugStr)
		}
		var $cell = S2CellId.from_face(face_index)
		for digit in digits {
			if digit < 48 or digit > 51 {
				return Err(BadDebugStr)
			}
			$cell = $cell.child((digit - 48).to_u64())
		}
		Ok($cell)
	}

	## The hex digit for a nibble.
	hex_digits : List(Str)
	hex_digits = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"]

	## The nibble a hex digit byte stands for.
	hex_value : U8 -> Try(U64, [BadToken])
	hex_value = |byte|
		if byte >= 48 and byte <= 57 {
			Ok((byte - 48).to_u64())
		} else if byte >= 97 and byte <= 102 {
			Ok((byte - 87).to_u64())
		} else if byte >= 65 and byte <= 70 {
			Ok((byte - 55).to_u64())
		} else {
			Err(BadToken)
		}

	is_eq : S2CellId, S2CellId -> Bool
	is_eq = |a, b| a.id == b.id

	is_lt : S2CellId, S2CellId -> Bool
	is_lt = |a, b| a.id < b.id

	is_lte : S2CellId, S2CellId -> Bool
	is_lte = |a, b| a.id <= b.id

	is_gt : S2CellId, S2CellId -> Bool
	is_gt = |a, b| a.id > b.id

	is_gte : S2CellId, S2CellId -> Bool
	is_gte = |a, b| a.id >= b.id

	to_hash : S2CellId, Hasher -> Hasher
	to_hash = |c, hasher| hasher.write_u64(c.id)

	to_inspect : S2CellId -> Str
	to_inspect = |c| "S2CellId(${c.to_token()})"
}

import R1Interval
import R2Point
import R2Rect
import S1Angle
import S2Coords
import S2LatLng
import Internal/S2Lookup
import Internal/S2Math
import S2Point
import Internal/S2Coder

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

	## The number of cube faces, which is the number of level-0 cells.
	num_faces : U64
	num_faces = 6

	## The number of bits a cell id spends on the cube face.
	face_bits : U64
	face_bits = 3

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

	## The cell at the given level that contains the Hilbert position `pos` on
	## `face`.
	##
	## The position is that of a leaf cell, so its lowest bit is forced to 1,
	## and the cell is the ancestor of that leaf at `target_level`.
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
	##
	## Upstream does not define the level of the invalid id zero. Here it is 0.
	level : S2CellId -> U64
	level = |c|
		S2CellId.max_level.minus_saturated((c.id.count_trailing_zero_bits() / 2).to_u64())

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
	## a few levels down. The list is empty when `target_level` is coarser
	## than this cell, or when the cell is not valid.
	children_at_level : S2CellId, U64 -> List(S2CellId)
	children_at_level = |c, target_level| {
		if !c.is_valid() or target_level < c.level() or target_level > S2CellId.max_level {
			return []
		}
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
	## its range. The invalid id zero has no range, so it gives itself.
	range_min : S2CellId -> S2CellId
	range_min = |c|
		if c.id == 0 {
			c
		} else {
			{ id: c.id.minus_wrap(c.lsb() - 1) }
		}

	## The last leaf cell contained by this one, which is the largest id in
	## its range. The invalid id zero has no range, so it gives itself.
	range_max : S2CellId -> S2CellId
	range_max = |c|
		if c.id == 0 {
			c
		} else {
			{ id: c.id.plus_wrap(c.lsb() - 1) }
		}

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

	## The number of cells at this cell's level that come before it in Hilbert
	## order, counting from the first cell of face 0.
	distance_from_begin : S2CellId -> I64
	distance_from_begin = |c|
		c.id.shr_zf_wrap((2 * (S2CellId.max_level - c.level()) + 1).to_u8_wrap()).to_i64_wrap()

	## The largest cell that starts where this one starts and ends before
	## `limit` starts. It is `limit` itself when there is no such cell.
	##
	## Use it to cover a range of leaf cells with few cells. For the half-open
	## range `[start, limit)`, the cells are `start.maximum_tile(limit)`, then
	## `next().maximum_tile(limit)` of each one, until the result is `limit`.
	## The cells start small, grow in the middle of the range, and shrink again
	## near `limit`.
	maximum_tile : S2CellId, S2CellId -> S2CellId
	maximum_tile = |c, limit| {
		start = c.range_min()
		if start >= limit.range_min() {
			return limit
		}
		if c.range_max() >= limit {
			# The cell is too large, so shrink it. Because the range minimum
			# is below that of the limit, the loop ends by the leaf level.
			var $shrunk = c
			while $shrunk.range_max() >= limit {
				$shrunk = $shrunk.child(0)
			}
			return $shrunk
		}
		# The cell may be too small, so grow it while it stays inside.
		var $grown = c
		var $more = Bool.True
		while $more and !$grown.is_face() {
			up = $grown.parent()
			if up.range_min() != start or up.range_max() >= limit {
				$more = Bool.False
			} else {
				$grown = up
			}
		}
		$grown
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
		# to find which face the position lands on. The limit keeps the point
		# barely outside the face rectangle, so that the reprojection cannot
		# move it into the wrong leaf cell.
		scale = 1.0 / S2CellId.max_size.to_f64()
		limit = 1.0 + 2.220446049250313e-16
		u = (scale * (2 * (clamped_i - max_i / 2) + 1).to_f64()).max(-limit).min(limit)
		v = (scale * (2 * (clamped_j - max_i / 2) + 1).to_f64()).max(-limit).min(limit)

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

	## The `(s, t)` coordinate of the cell's centre on its own face.
	center_st : S2CellId -> R2Point
	center_st = |c| {
		center = c.center_si_ti()
		R2Point.new(S2Coords.si_ti_to_st(center.si), S2Coords.si_ti_to_st(center.ti))
	}

	## The `(s, t)` extent of the cell on its own face, as a rectangle.
	bound_st : S2CellId -> R2Rect
	bound_st = |c| {
		size = c.size_st()
		R2Rect.from_center_size(c.center_st(), R2Point.new(size, size))
	}

	## The `(u, v)` extent of the cell with the leaf indices `i` and `j` at
	## `target_level`, as a rectangle.
	##
	## The indices need not be those of the cell's corner: any leaf in the cell
	## gives the same cell, because the low bits are dropped.
	ij_level_to_bound_uv : U64, U64, U64 -> R2Rect
	ij_level_to_bound_uv = |i, j, target_level| {
		cell_size = S2CellId.size_ij_at_level(target_level)
		mask = cell_size.bitwise_not().plus_wrap(1)
		bound = |ij| {
			lo = ij.bitwise_and(mask)
			R1Interval.new(
				S2Coords.st_to_uv(S2Coords.ij_to_st_min(lo)),
				S2Coords.st_to_uv(S2Coords.ij_to_st_min(lo + cell_size)),
			)
		}
		R2Rect.new(bound(i), bound(j))
	}

	## The rectangle grown so that it holds every point within `distance` of
	## it, and the smallest such rectangle.
	##
	## A negative distance shrinks the rectangle instead, so that it leaves out
	## every point within the distance of its boundary. The distance is
	## measured on the sphere, not in `(u, v)` space, so each side moves a
	## different amount. This is how to widen a cell's `(u, v)` bound to cover
	## the points within 5 km of the cell.
	##
	## The rectangle lies on one cube face, so it covers at most one
	## hemisphere. A cell bound can safely grow by at most 45 degrees. For a
	## negative distance the result is not exact: it may be slightly smaller
	## than needed. When the rectangle shrinks to nothing, the result is the
	## single point at its first corner.
	expanded_by_distance_uv : R2Rect, S1Angle -> R2Rect
	expanded_by_distance_uv = |uv, distance| {
		u0 = uv.x().lo()
		u1 = uv.x().hi()
		v0 = uv.y().lo()
		v1 = uv.y().hi()
		max_u = u0.abs().max(u1.abs())
		max_v = v0.abs().max(v1.abs())
		sin_dist = distance.sin()
		x_interval = R1Interval.new(
			expand_endpoint(u0, max_v, -sin_dist),
			expand_endpoint(u1, max_v, sin_dist),
		)
		y_interval = R1Interval.new(
			expand_endpoint(v0, max_u, -sin_dist),
			expand_endpoint(v1, max_u, sin_dist),
		)
		# An R2Rect needs both or neither side to be empty.
		if x_interval.is_empty() or y_interval.is_empty() {
			R2Rect.new(R1Interval.new(u0, u0), R1Interval.new(v0, v0))
		} else {
			R2Rect.new(x_interval, y_interval)
		}
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
	## `nbr_level` must be at least this cell's level. At a corner of the cube
	## the list can hold the same cell more than once.
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
			.map(|d| hex_digits.get(d) ?? "0")
			|> Str.join_with("")
	}

	## The cell id a hex token names, or `Err(BadToken)` when the token is not
	## 1 to 16 hex digits.
	##
	## The tokens `"X"` and `"0"` name the invalid id zero. Other tokens can
	## name ids that are not valid, and `is_valid` tells them apart. Upstream
	## gives the invalid id for a bad token, where this gives `Err`.
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
			digit = hex_value(byte)?
			$value = $value.shl_wrap(4).bitwise_or(digit)
		}
		Ok({ id: $value.shl_wrap((4 * (16 - bytes.len())).to_u8_wrap()) })
	}

	## The face and Hilbert child positions, as `"2/301"`, which is the form
	## upstream prints cell ids in.
	to_debug_str : S2CellId -> Str
	to_debug_str = |c| {
		if !c.is_valid() {
			return "Invalid: ${hex16(c.id)}"
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

	## The 8 bytes that upstream's `S2CellId::Encode` writes: the id as a
	## little-endian 64-bit integer. Any id can be written, valid or not.
	encode : S2CellId -> List(U8)
	encode = |c| S2Coder.put_u64([], c.id)

	## The cell id that `encode` writes. Bytes after the first 8 are ignored.
	## The id is not checked, so `is_valid` tells whether it names a cell.
	decode : List(U8) -> Try(S2CellId, [Truncated])
	decode = |bytes| Ok(S2CellId.from_id(S2Coder.get_u64(bytes, 0)?))
}

expect S2CellId.none().level() == 0 and !S2CellId.none().is_valid()
expect S2CellId.none().range_min() == S2CellId.none() and S2CellId.none().range_max() == S2CellId.none()
expect !S2CellId.none().contains(S2CellId.from_face(0)) and !S2CellId.none().intersects(S2CellId.from_face(0))
expect S2CellId.from_token("X") == Ok(S2CellId.none())
expect S2CellId.from_token("0") == Ok(S2CellId.none())
expect {
	c = S2CellId.from_token("2").ok_or(S2CellId.none())
	!c.is_valid() and c.range_min().id() <= c.range_max().id() and c.level() <= 30
}
expect S2CellId.none().children_at_level(3) == [] and S2CellId.none().children().len() == 4
expect S2CellId.from_face(0).child(1).children_at_level(0) == []
expect S2CellId.from_face(0).child(1).children_at_level(1) == [S2CellId.from_face(0).child(1)]
expect S2CellId.from_face(0).children_at_level(2).len() == 16
expect {
	# A position far outside the face still lands on a real neighbour face.
	c = S2CellId.from_face_ij_wrap(0, -1, 5)
	c.is_valid() and c.face() == 4
}
expect {
	# At the face corner the clamped point is barely outside the face and the
	# result is the same leaf as the unclamped corner.
	c = S2CellId.from_face_ij_wrap(0, 1073741824, 1073741824)
	c.is_valid() and c.is_leaf()
}
expect S2CellId.none().to_debug_str() == "Invalid: 0000000000000000"
expect S2CellId.from_id(0xffffffffffffffff).to_debug_str() == "Invalid: ffffffffffffffff"
expect S2CellId.from_face(2).child(3).to_debug_str() == "2/3"
expect {
	# Just across the u = -1 edge, the clamp keeps the leaf next to the edge
	# cell at the far end of the edge. Without it the result is off by one.
	S2CellId.from_face_ij_wrap(0, -1, 1073741823).to_token() == "8aaaaaaaaaaaaaab"
}

## The 16 hex digits of an id, with leading zeros.
hex16 : U64 -> Str
hex16 = |value| {
	var $out = ""
	for nibble_index in (0.U64).until(16) {
		digit = value.shr_zf_wrap(((15 - nibble_index) * 4).to_u8_wrap()).bitwise_and(15)
		$out = $out.concat(hex_digits.get(digit) ?? "0")
	}
	$out
}

## The hex digit for a nibble.
## A new `u` coordinate such that the line `u = u'` is exactly the angle
## `asin(sin_dist)` away from the edge from `(u, v0)` to `(u, v1)`, where
## `max_v` is the larger of `|v0|` and `|v1|`.
##
## This solves a spherical right triangle, as `S2Cap.rect_bound` does.
expand_endpoint : F64, F64, F64 -> F64
expand_endpoint = |u, max_v, sin_dist| {
	sin_u_shift = sin_dist * S2Math.sqrt((1.0 + u * u + max_v * max_v) / (1.0 + u * u))
	cos_u_shift = S2Math.sqrt(1.0 - sin_u_shift * sin_u_shift)
	# This is an expansion of tan(atan(u) + asin(sin_u_shift)).
	(cos_u_shift * u + sin_u_shift) / (cos_u_shift - sin_u_shift * u)
}

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

# The values below were printed by upstream's S2CellId at v0.14.0 through
# tools/s2_oracle.cc.
expect {
	# FromFacePosLevel keeps the cell at the level, not the leaf.
	cases = [
		{ face: 0, pos: 0, level: 0, id: 1152921504606846976 },
		{ face: 5, pos: 1152921504606846976, level: 0, id: 12682136550675316736 },
		{ face: 2, pos: 5, level: 29, id: 4611686018427387908 },
		{ face: 2, pos: 5, level: 30, id: 4611686018427387909 },
		{ face: 3, pos: 81985529216486895, level: 7, id: 6999508614608060416 },
		{ face: 1, pos: 2305843009213693951, level: 12, id: 4611685949707911168 },
		{ face: 4, pos: 12345, level: 1, id: 9511602413006487552 },
		{ face: 0, pos: 0, level: 30, id: 1 },
	]
	cases.fold(
		Bool.True,
		|ok, c| ok and S2CellId.from_face_pos_level(c.face, c.pos, c.level) == S2CellId.from_id(c.id),
	)
}
expect {
	cases = [
		{ id: 3269754736974233600, level: 14, begin: 3269754724089331712, end: 3269754758449070080 },
		{ id: 13473683767604281344, level: 22, begin: 13473679369557835776, end: 13473688165650857984 },
		{ id: 4168628197916834816, level: 30, begin: 4168628197916833793, end: 4168628197916835841 },
		{ id: 10440469836151652352, level: 29, begin: 10439343936244809732, end: 10441595736058494980 },
		{ id: 2338404620882179072, level: 28, begin: 2338404620882178064, end: 2338404620882180112 },
		{ id: 5599027521151193356, level: 30, begin: 5599027521151193353, end: 5599027521151193361 },
		{ id: 1733885856537640960, level: 5, begin: 1730508156817113088, end: 1739515356071854080 },
		{ id: 3905910188457190772, level: 30, begin: 3905910188457190769, end: 3905910188457190777 },
		{ id: 1152921504606846976, level: 0, begin: 1152921504606846976, end: 3458764513820540928 },
		{ id: 1152921504606846976, level: 30, begin: 1, end: 2305843009213693953 },
		{ id: 11529215046068469761, level: 30, begin: 11529215046068469761, end: 11529215046068469763 },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			id = S2CellId.from_id(c.id)
			ok
				and id.child_begin_at_level(c.level) == S2CellId.from_id(c.begin)
				and id.child_end_at_level(c.level) == S2CellId.from_id(c.end)
		},
	)
}
expect {
	expected : List(U64)
	expected = [1152921504606846976, 288230376151711744, 72057594037927936, 18014398509481984, 4503599627370496, 1125899906842624, 281474976710656, 70368744177664, 17592186044416, 4398046511104, 1099511627776, 274877906944, 68719476736, 17179869184, 4294967296, 1073741824, 268435456, 67108864, 16777216, 4194304, 1048576, 262144, 65536, 16384, 4096, 1024, 256, 64, 16, 4, 1]
	(0.U64).until(31).fold(
		Bool.True,
		|ok, level| ok and S2CellId.lsb_for_level(level) == (expected.get(level) ?? 0),
	)
}
expect {
	# GetCommonAncestorLevel is -1 for cells on different faces.
	cases = [
		{ a: 9490411270927548416, b: 9276923292706571493, level: 1 },
		{ a: 2509826875221098496, b: 2677311090458635151, level: 1 },
		{ a: 10148806554242629632, b: 9309010023986529877, level: 0 },
		{ a: 7459093440474971072, b: 8471193027927627091, level: 0 },
		{ a: 13288095138149937152, b: 11811629783402954752, level: 0 },
		{ a: 11130345907571130368, b: 9560373548734002099, level: 0 },
		{ a: 10065513264155983872, b: 9956519077805555712, level: 2 },
		{ a: 6979407824065396736, b: 8569224190979211264, level: 0 },
		{ a: 8070450532247928832, b: 7429502321411571712, level: 0 },
		{ a: 10506543696009232384, b: 10754595910160744448, level: 1 },
		{ a: 1152921504606846976, b: 3458764513820540928, level: -1 },
		{ a: 3269754736974233600, b: 3269754736974233600, level: 13 },
		{ a: 13473683767604281344, b: 13473680469069398016, level: 9 },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			got = S2CellId.from_id(c.a).common_ancestor_level(S2CellId.from_id(c.b))
			ok and got == (if (c.level < 0) Err(NoCommonAncestor) else Ok(c.level.to_u64_wrap()))
		},
	)
}
expect {
	cases = [
		{ id: 3269754736974233600, face: 1, si: 2011824128, ti: 1056833536, point: (-0.83686380088329315, 1, -0.010580703616142273) },
		{ id: 13473683767604281344, face: 5, si: 828375040, ti: 1306525696, point: (0.16019821166992188, -0.16975021362304688, -1) },
		{ id: 4168628197916834816, face: 1, si: 1042801376, ti: 1805987872, point: (0.019487136864886935, 1, 0.60966009127779852) },
		{ id: 10440469836151652352, face: 4, si: 1442840576, ti: 1308622848, point: (0.16178385416666666, -1, -0.2685546875) },
		{ id: 2338404620882179072, face: 1, si: 153816224, ti: 48176160, point: (0.81583706599181272, 1, -0.94084763838734897) },
		{ id: 5599027521151193356, face: 2, si: 828203730, ti: 1787327702, point: (0.16988089101856857, -0.59027401303900495, 1) },
		{ id: 1733885856537640960, face: 0, si: 2080374784, ti: 1006632960, point: (1, 0.91796875, -0.04296875) },
		{ id: 3905910188457190772, face: 1, si: 1352555462, ti: 2038999630, point: (-0.19558566952913004, 1, 0.86869111051865744) },
		{ id: 4611686018427387909, face: 2, si: 3, ti: 3, point: (0.9999999962747097, 0.9999999962747097, 1) },
		{ id: 1152921504606846976, face: 0, si: 1073741824, ti: 1073741824, point: (1, 0, 0) },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			id = S2CellId.from_id(c.id)
			got = id.center_si_ti()
			p = id.to_point_raw()
			ok
				and got == { face: c.face, si: c.si, ti: c.ti }
				and p == S2Point.new(c.point.0, c.point.1, c.point.2)
		},
	)
}
expect {
	# MaximumTile: cases with a limit before, inside and far after the cell.
	cases = [
		{ id: 8889130030429499392, limit: 8893320591588539943, tile: 8889130030429499392 },
		{ id: 11077038690122334208, limit: 11077034292075826157, tile: 11077034292075824128 },
		{ id: 326957320145731584, limit: 326957320279949312, tile: 326957320145731584 },
		{ id: 10822332307066583504, limit: 10822332307066593245, tile: 10822332307066583504 },
		{ id: 8621353045025882112, limit: 8621353044958773495, tile: 8621353044958773312 },
		{ id: 9305562730054287360, limit: 9307814529867972608, tile: 9305562730054287360 },
		{ id: 3668502698083221504, limit: 4100038831010676736, tile: 3668502698083221504 },
		{ id: 3782255168020545536, limit: 3833347634134584320, tile: 3782255168020545536 },
		{ id: 641399986260541440, limit: 2148319860934157760, tile: 641399986461868032 },
		{ id: 726979767773285376, limit: 726979767773287424, tile: 726979767773285376 },
		{ id: 9385296358363103232, limit: 9385296289643633059, tile: 9385296289643627520 },
		{ id: 891239538036874419, limit: 891239538036874421, tile: 891239538036874419 },
		{ id: 1256538573730031, limit: 1256538573730033, tile: 1256538573730031 },
		{ id: 3175037737296199680, limit: 3170534137668836063, tile: 3170534137668830208 },
		{ id: 1152921504606846976, limit: 3458764513820540928, tile: 1152921504606846976 },
		{ id: 4611686018427387909, limit: 4611686018427387909, tile: 4611686018427387909 },
		{ id: 4611686018427387908, limit: 4611686018427387909, tile: 4611686018427387905 },
	]
	cases.fold(
		Bool.True,
		|ok, c| ok and S2CellId.from_id(c.id).maximum_tile(S2CellId.from_id(c.limit)) == S2CellId.from_id(c.tile),
	)
}

# Printed by GetCenterST, GetBoundST and distance_from_begin.
expect {
	cases = [
		{ id: 1152921504606846976, s: 0.5, t: 0.5, bound: (0, 1, 0, 1), distance: 0 },
		{ id: 8070450532247928832, s: 0.5, t: 0.5, bound: (0, 1, 0, 1), distance: 3 },
		{ id: 12682136550675316736, s: 0.5, t: 0.5, bound: (0, 1, 0, 1), distance: 5 },
		{ id: 4775657076574030543, s: 0.3243116089142859, t: 0.085606755223125219, bound: (0.32431160844862461, 0.32431160937994719, 0.085606754757463932, 0.085606755688786507), distance: 2387828538287015271 },
		{ id: 2306031919055241216, s: 0.0147705078125, t: 0.0006103515625, bound: (0.0146484375, 0.014892578125, 0.00048828125, 0.000732421875), distance: 16778590 },
		{ id: 9224497936761618432, s: 0.015625, t: 0.015625, bound: (0, 0.03125, 0, 0.03125), distance: 4096 },
		{ id: 1537228672809129301, s: 0.99999999953433871, t: 0.99999999953433871, bound: (0.99999999906867743, 1, 0.99999999906867743, 1), distance: 768614336404564650 },
		{ id: 11817445422220181504, s: 0.25, t: 0.25, bound: (0, 0.5, 0, 0.5), distance: 20 },
		{ id: 6917529027641081855, s: 0.99999999953433871, t: 4.6566128730773926e-10, bound: (0.99999999906867743, 1, 0, 9.3132257461547852e-10), distance: 3458764513820540927 },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			id = S2CellId.from_id(c.id)
			center = id.center_st()
			bound = id.bound_st()
			ok
				and center == R2Point.new(c.s, c.t)
				and bound.x().lo() == c.bound.0
				and bound.x().hi() == c.bound.1
				and bound.y().lo() == c.bound.2
				and bound.y().hi() == c.bound.3
				and id.distance_from_begin() == c.distance
		},
	)
}
# Printed by IJLevelToBoundUV.
expect {
	cases = [
		{ i: 0, j: 0, level: 0, bound: (-1, 1, -1, 1) },
		{ i: 1073741823, j: 1073741823, level: 0, bound: (-1, 1, -1, 1) },
		{ i: 5, j: 9, level: 30, bound: (-0.99999998758236563, -0.99999998509883881, -0.99999997764825832, -0.99999997516473149) },
		{ i: 123456789, j: 987654321, level: 10, bound: (-0.71271896362304688, -0.71041361490885413, 0.79261398315429688, 0.79500834147135413) },
		{ i: 1073741823, j: 0, level: 1, bound: (0, 1, -1, 0) },
		{ i: 536870912, j: 536870911, level: 1, bound: (0, 1, -1, 0) },
		{ i: 100, j: 2000000, level: 20, bound: (-1, -0.99999745686970221, -0.99503788949732552, -0.99503535110367614) },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			bound = S2CellId.ij_level_to_bound_uv(c.i, c.j, c.level)
			ok
				and bound.x().lo() == c.bound.0
				and bound.x().hi() == c.bound.1
				and bound.y().lo() == c.bound.2
				and bound.y().hi() == c.bound.3
		},
	)
}
# Printed by ExpandedByDistanceUV. A shrink past nothing leaves the first corner.
expect {
	cases = [
		{ uv: (-0.5, 0.5, -0.25, 0.25), radians: 0.01, expanded: (-0.51287511515526796, 0.51287511515526796, -0.26184246676223483, 0.26184246676223483) },
		{ uv: (-0.5, 0.5, -0.25, 0.25), radians: -0.01, expanded: (-0.4872561476974655, 0.4872561476974655, -0.2382231646641319, 0.2382231646641319) },
		{ uv: (0.0, 1.0, 0.0, 1.0), radians: 0.0, expanded: (0, 1, 0, 1) },
		{ uv: (0.1, 0.2, 0.3, 0.4), radians: 0.001, expanded: (0.098913056283128145, 0.20111737971358362, 0.29889051870122335, 0.40118031110561769) },
		{ uv: (0.1, 0.2, 0.3, 0.4), radians: -0.05, expanded: (0.10000000000000001, 0.10000000000000001, 0.29999999999999999, 0.29999999999999999) },
		{ uv: (-1.0, 1.0, -1.0, 1.0), radians: 0.7, expanded: (-1, -1, -1, -1) },
		{ uv: (-0.3, 0.7, -1.0, 0.2), radians: 0.1, expanded: (-0.45879242001158149, 0.91335400083022833, -1.2524838712957795, 0.33003876986949349) },
		{ uv: (0.3243116084486246, 0.3243116093799472, 0.08560675475746393, 0.0856067556887865), radians: 1.567e-06, expanded: (0.32430987090314872, 0.32431334692719593, 0.085605095912551415, 0.085608414534166996) },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			uv = R2Rect.new(R1Interval.new(c.uv.0, c.uv.1), R1Interval.new(c.uv.2, c.uv.3))
			got = S2CellId.expanded_by_distance_uv(uv, S1Angle.from_radians(c.radians))
			ok
				and got.x().lo() == c.expanded.0
				and got.x().hi() == c.expanded.1
				and got.y().lo() == c.expanded.2
				and got.y().hi() == c.expanded.3
		},
	)
}

# S2CellId encoding against upstream's `Encode`, and decoding it back.
expect S2Coder.to_hex(S2CellId.none().encode()) == "0000000000000000"
expect S2CellId.decode(S2Coder.from_hex("0000000000000000")) == Ok(S2CellId.none())
expect S2Coder.to_hex(S2CellId.from_id(18446744073709551615).encode()) == "ffffffffffffffff"
expect S2CellId.decode(S2Coder.from_hex("ffffffffffffffff")) == Ok(S2CellId.from_id(18446744073709551615))
expect S2Coder.to_hex(S2CellId.from_face(0).encode()) == "0000000000000010"
expect S2CellId.decode(S2Coder.from_hex("0000000000000010")) == Ok(S2CellId.from_face(0))

expect S2CellId.decode(S2Coder.from_hex("00000000000000")) == Err(Truncated)
expect S2CellId.decode([]) == Err(Truncated)
expect S2CellId.decode(S2Coder.from_hex("0000000000000010ff")) == Ok(S2CellId.from_face(0))

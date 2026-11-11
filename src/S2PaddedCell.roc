import R1Interval
import R2Rect
import S2CellId
import S2Coords
import Internal/S2Lookup
import S2Point

## A cell whose `(u, v)` bound has been grown by a fixed padding, with the
## parts of the Hilbert curve walk that a recursive subdivision needs.
##
## Built for algorithms that descend from a cell to its children and test
## each against shapes, as upstream's spatial index does. `child` derives a
## child from its parent without decoding the child's id again, which is why
## it is cheaper than building each child with `new`.
S2PaddedCell := {
	id : S2CellId,
	padding : F64,
	bound : R2Rect,
	middle : R2Rect,
	i_lo : U64,
	j_lo : U64,
	orientation : U64,
	level : U64,
}.{

	## The cell `id` with its `(u, v)` bound grown by `padding` on every side.
	new : S2CellId, F64 -> S2PaddedCell
	new = |id, padding| {
		if id.is_face() {
			limit = 1.0 + padding
			{
				id,
				padding,
				bound: R2Rect.new(R1Interval.new(-limit, limit), R1Interval.new(-limit, limit)),
				middle: R2Rect.new(R1Interval.new(-padding, padding), R1Interval.new(-padding, padding)),
				i_lo: 0,
				j_lo: 0,
				orientation: id.face().bitwise_and(1),
				level: 0,
			}
		} else {
			ij = id.to_face_ij_orientation()
			level = id.level()
			size = S2CellId.size_ij_at_level(level)
			mask = size.bitwise_not().plus_wrap(1)
			i_lo = ij.i.bitwise_and(mask)
			j_lo = ij.j.bitwise_and(mask)
			{
				id,
				padding,
				bound: S2CellId.ij_level_to_bound_uv(ij.i, ij.j, level).expanded_by(padding),
				middle: middle_of(i_lo, j_lo, level, padding),
				i_lo,
				j_lo,
				orientation: ij.orientation,
				level,
			}
		}
	}

	## The child of `parent` at offset `(i, j)`, each `0` or `1`, in `(u, v)`
	## space.
	##
	## The child's bound is taken from the parent's bound and middle, so it
	## costs no trigonometry and no decoding.
	child : S2PaddedCell, U64, U64 -> S2PaddedCell
	child = |parent, i, j| {
		positions = S2Lookup.pos_to_ij.get(parent.orientation) ?? []
		ij = 2 * i + j
		pos = (0.U64).until(4).fold(0, |found, k| if ((positions.get(k) ?? 4) == ij) k else found)
		level = parent.level + 1
		size = S2CellId.size_ij_at_level(level)
		i_lo = parent.i_lo + i * size
		j_lo = parent.j_lo + j * size
		# The side of the child that faces the parent's centre lies on the
		# parent's middle.
		x =
			if i == 0 {
				R1Interval.new(parent.bound.x().lo(), parent.middle.x().hi())
			} else {
				R1Interval.new(parent.middle.x().lo(), parent.bound.x().hi())
			}
		y =
			if j == 0 {
				R1Interval.new(parent.bound.y().lo(), parent.middle.y().hi())
			} else {
				R1Interval.new(parent.middle.y().lo(), parent.bound.y().hi())
			}
		{
			id: parent.id.child(pos),
			padding: parent.padding,
			bound: R2Rect.new(x, y),
			middle: middle_of(i_lo, j_lo, level, parent.padding),
			i_lo,
			j_lo,
			orientation: parent.orientation.bitwise_xor(S2Lookup.pos_to_orientation.get(pos) ?? 0),
			level,
		}
	}

	## The id of the cell.
	id : S2PaddedCell -> S2CellId
	id = |cell| cell.id

	## The padding the bound was grown by.
	padding : S2PaddedCell -> F64
	padding = |cell| cell.padding

	## The subdivision level of the cell.
	level : S2PaddedCell -> U64
	level = |cell| cell.level

	## The padded `(u, v)` bound of the cell.
	bound : S2PaddedCell -> R2Rect
	bound = |cell| cell.bound

	## The rectangle where the four children overlap once padded: the
	## `(u, v)` centre of the cell, grown by the padding. It is a single
	## point when the padding is zero.
	middle : S2PaddedCell -> R2Rect
	middle = |cell| cell.middle

	## The `(i, j)` offset of the child at position `pos` along the Hilbert
	## curve, each coordinate `0` or `1`. This is the inverse of the position
	## that `child` gives a child.
	child_ij : S2PaddedCell, U64 -> (U64, U64)
	child_ij = |cell, pos| {
		ij = (S2Lookup.pos_to_ij.get(cell.orientation) ?? []).get(pos) ?? 0
		(ij.shr_zf_wrap(1), ij.bitwise_and(1))
	}

	## The centre of the cell, which is the centre of `middle`, as a unit
	## vector.
	center : S2PaddedCell -> S2Point
	center = |cell| {
		size = S2CellId.size_ij_at_level(cell.level)
		S2Coords.face_si_ti_to_xyz(cell.id.face(), 2 * cell.i_lo + size, 2 * cell.j_lo + size).normalize()
	}

	## The vertex where the Hilbert curve enters the cell, as a unit vector.
	entry_vertex : S2PaddedCell -> S2Point
	entry_vertex = |cell| {
		# The curve enters at (0, 0) unless the orientation inverts it, in
		# which case it enters at (1, 1).
		offset = if (cell.orientation.bitwise_and(S2Lookup.invert_mask) != 0) S2CellId.size_ij_at_level(cell.level) else 0
		i = cell.i_lo + offset
		j = cell.j_lo + offset
		S2Coords.face_si_ti_to_xyz(cell.id.face(), 2 * i, 2 * j).normalize()
	}

	## The vertex where the Hilbert curve leaves the cell, as a unit vector.
	exit_vertex : S2PaddedCell -> S2Point
	exit_vertex = |cell| {
		size = S2CellId.size_ij_at_level(cell.level)
		# The curve leaves at (1, 0) or (0, 1), unless inverted.
		u_exit = cell.orientation == 0 or cell.orientation == S2Lookup.swap_mask + S2Lookup.invert_mask
		(i, j) = if (u_exit) (cell.i_lo + size, cell.j_lo) else (cell.i_lo, cell.j_lo + size)
		S2Coords.face_si_ti_to_xyz(cell.id.face(), 2 * i, 2 * j).normalize()
	}

	## The smallest descendant of this cell whose padded bound contains
	## `rect`, which must intersect this cell's padded bound.
	##
	## A descendant may be returned whose padded bound only just contains
	## `rect`: the test allows for rounding, so it errs towards the larger
	## cell.
	shrink_to_fit : S2PaddedCell, R2Rect -> S2CellId
	shrink_to_fit = |cell, rect| {
		size = S2CellId.size_ij_at_level(cell.level)
		# A rectangle that spans a centre line of the cell fits no child.
		spans_center =
			if cell.level == 0 {
				rect.x().contains_point(0.0) or rect.y().contains_point(0.0)
			} else {
				rect.x().contains_point(S2Coords.st_to_uv(S2Coords.si_ti_to_st(2 * cell.i_lo + size)))
					or rect.y().contains_point(S2Coords.st_to_uv(S2Coords.si_ti_to_st(2 * cell.j_lo + size)))
			}
		if spans_center {
			return cell.id
		}

		# Otherwise the level is that of the largest cell whose (i, j) range
		# the padded rectangle stays within, which is where the minimum and
		# maximum coordinates it spans first differ.
		padded = rect.expanded_by(cell.padding + 1.5 * 2.220446049250313e-16)
		span = |lo_bound, interval| {
			ij_min = lo_bound.max(S2Coords.st_to_ij(S2Coords.uv_to_st(interval.lo())))
			ij_max = (lo_bound + size - 1).min(S2Coords.st_to_ij(S2Coords.uv_to_st(interval.hi())))
			(ij_min, ij_min.bitwise_xor(ij_max))
		}
		(i_min, i_xor) = span(cell.i_lo, padded.x())
		(j_min, j_xor) = span(cell.j_lo, padded.y())
		level_msb = i_xor.bitwise_or(j_xor).shl_wrap(1) + 1
		bit_width = 64 - level_msb.count_leading_zero_bits().to_u64()
		target_level = S2CellId.max_level - (bit_width - 1)
		if target_level <= cell.level {
			cell.id
		} else {
			S2CellId.from_face_ij(cell.id.face(), i_min, j_min).parent_at_level(target_level)
		}
	}
}

## The `(u, v)` centre of the cell with the given low corner and level, grown
## by the padding.
middle_of : U64, U64, U64, F64 -> R2Rect
middle_of = |i_lo, j_lo, level, padding| {
	size = S2CellId.size_ij_at_level(level)
	u = S2Coords.st_to_uv(S2Coords.si_ti_to_st(2 * i_lo + size))
	v = S2Coords.st_to_uv(S2Coords.si_ti_to_st(2 * j_lo + size))
	R2Rect.new(R1Interval.new(u - padding, u + padding), R1Interval.new(v - padding, v + padding))
}

# Padded cells against upstream's S2PaddedCell: the bound, the middle, the
# centre and the curve's entry and exit vertices, and the same for every
# child.
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0)
	Bool.True
		and cell.id() == S2CellId.from_id(1152921504606846976)
		and cell.level() == 0
		and cell.bound() == R2Rect.new(R1Interval.new(-1.0, 1.0), R1Interval.new(-1.0, 1.0))
		and cell.middle() == R2Rect.new(R1Interval.new(-0.0, 0.0), R1Interval.new(-0.0, 0.0))
		and cell.center() == S2Point.new(1.0, 0.0, 0.0)
		and cell.entry_vertex() == S2Point.new(0.5773502691896258, -0.5773502691896258, -0.5773502691896258)
		and cell.exit_vertex() == S2Point.new(0.5773502691896258, 0.5773502691896258, -0.5773502691896258)
		and cell.padding() == 0.0
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0).child(0, 0)
	Bool.True
		and child.id() == S2CellId.from_id(288230376151711744)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-1.0, 0.0), R1Interval.new(-1.0, 0.0))
		and child.middle() == R2Rect.new(R1Interval.new(-0.41666666666666663, -0.41666666666666663), R1Interval.new(-0.41666666666666663, -0.41666666666666663))
		and child.center() == S2Point.new(0.8615497903412856, -0.35897907930886896, -0.35897907930886896)
		and child.entry_vertex() == S2Point.new(0.5773502691896258, -0.5773502691896258, -0.5773502691896258)
		and child.exit_vertex() == S2Point.new(0.7071067811865475, -0.7071067811865475, 0.0)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0).child(0, 1)
	Bool.True
		and child.id() == S2CellId.from_id(864691128455135232)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-1.0, 0.0), R1Interval.new(-0.0, 1.0))
		and child.middle() == R2Rect.new(R1Interval.new(-0.41666666666666663, -0.41666666666666663), R1Interval.new(0.41666666666666663, 0.41666666666666663))
		and child.center() == S2Point.new(0.8615497903412856, -0.35897907930886896, 0.35897907930886896)
		and child.entry_vertex() == S2Point.new(0.7071067811865475, -0.7071067811865475, 0.0)
		and child.exit_vertex() == S2Point.new(1.0, 0.0, 0.0)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0).child(1, 0)
	Bool.True
		and child.id() == S2CellId.from_id(2017612633061982208)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-0.0, 1.0), R1Interval.new(-1.0, 0.0))
		and child.middle() == R2Rect.new(R1Interval.new(0.41666666666666663, 0.41666666666666663), R1Interval.new(-0.41666666666666663, -0.41666666666666663))
		and child.center() == S2Point.new(0.8615497903412856, 0.35897907930886896, -0.35897907930886896)
		and child.entry_vertex() == S2Point.new(0.7071067811865475, 0.7071067811865475, 0.0)
		and child.exit_vertex() == S2Point.new(0.5773502691896258, 0.5773502691896258, -0.5773502691896258)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0).child(1, 1)
	Bool.True
		and child.id() == S2CellId.from_id(1441151880758558720)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-0.0, 1.0), R1Interval.new(-0.0, 1.0))
		and child.middle() == R2Rect.new(R1Interval.new(0.41666666666666663, 0.41666666666666663), R1Interval.new(0.41666666666666663, 0.41666666666666663))
		and child.center() == S2Point.new(0.8615497903412856, 0.35897907930886896, 0.35897907930886896)
		and child.entry_vertex() == S2Point.new(1.0, 0.0, 0.0)
		and child.exit_vertex() == S2Point.new(0.7071067811865475, 0.7071067811865475, 0.0)
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0)
	[cell.child_ij(0), cell.child_ij(1), cell.child_ij(2), cell.child_ij(3)] == [(0, 0), (0, 1), (1, 1), (1, 0)]
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(8070450532247928832), 0.1)
	Bool.True
		and cell.id() == S2CellId.from_id(8070450532247928832)
		and cell.level() == 0
		and cell.bound() == R2Rect.new(R1Interval.new(-1.1, 1.1), R1Interval.new(-1.1, 1.1))
		and cell.middle() == R2Rect.new(R1Interval.new(-0.1, 0.1), R1Interval.new(-0.1, 0.1))
		and cell.center() == S2Point.new(-1.0, -0.0, -0.0)
		and cell.entry_vertex() == S2Point.new(-0.5773502691896258, 0.5773502691896258, 0.5773502691896258)
		and cell.exit_vertex() == S2Point.new(-0.5773502691896258, -0.5773502691896258, 0.5773502691896258)
		and cell.padding() == 0.1
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(8070450532247928832), 0.1).child(0, 0)
	Bool.True
		and child.id() == S2CellId.from_id(7205759403792793600)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-1.1, 0.1), R1Interval.new(-1.1, 0.1))
		and child.middle() == R2Rect.new(R1Interval.new(-0.5166666666666666, -0.31666666666666665), R1Interval.new(-0.5166666666666666, -0.31666666666666665))
		and child.center() == S2Point.new(-0.8615497903412856, 0.35897907930886896, 0.35897907930886896)
		and child.entry_vertex() == S2Point.new(-0.5773502691896258, 0.5773502691896258, 0.5773502691896258)
		and child.exit_vertex() == S2Point.new(-0.7071067811865475, 0.7071067811865475, -0.0)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(8070450532247928832), 0.1).child(0, 1)
	Bool.True
		and child.id() == S2CellId.from_id(8935141660703064064)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-1.1, 0.1), R1Interval.new(-0.1, 1.1))
		and child.middle() == R2Rect.new(R1Interval.new(-0.5166666666666666, -0.31666666666666665), R1Interval.new(0.31666666666666665, 0.5166666666666666))
		and child.center() == S2Point.new(-0.8615497903412856, -0.35897907930886896, 0.35897907930886896)
		and child.entry_vertex() == S2Point.new(-0.7071067811865475, -0.7071067811865475, -0.0)
		and child.exit_vertex() == S2Point.new(-0.5773502691896258, -0.5773502691896258, 0.5773502691896258)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(8070450532247928832), 0.1).child(1, 0)
	Bool.True
		and child.id() == S2CellId.from_id(7782220156096217088)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-0.1, 1.1), R1Interval.new(-1.1, 0.1))
		and child.middle() == R2Rect.new(R1Interval.new(0.31666666666666665, 0.5166666666666666), R1Interval.new(-0.5166666666666666, -0.31666666666666665))
		and child.center() == S2Point.new(-0.8615497903412856, 0.35897907930886896, -0.35897907930886896)
		and child.entry_vertex() == S2Point.new(-0.7071067811865475, 0.7071067811865475, -0.0)
		and child.exit_vertex() == S2Point.new(-1.0, -0.0, -0.0)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(8070450532247928832), 0.1).child(1, 1)
	Bool.True
		and child.id() == S2CellId.from_id(8358680908399640576)
		and child.level() == 1
		and child.bound() == R2Rect.new(R1Interval.new(-0.1, 1.1), R1Interval.new(-0.1, 1.1))
		and child.middle() == R2Rect.new(R1Interval.new(0.31666666666666665, 0.5166666666666666), R1Interval.new(0.31666666666666665, 0.5166666666666666))
		and child.center() == S2Point.new(-0.8615497903412856, -0.35897907930886896, -0.35897907930886896)
		and child.entry_vertex() == S2Point.new(-1.0, -0.0, -0.0)
		and child.exit_vertex() == S2Point.new(-0.7071067811865475, -0.7071067811865475, -0.0)
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(8070450532247928832), 0.1)
	[cell.child_ij(0), cell.child_ij(1), cell.child_ij(2), cell.child_ij(3)] == [(0, 0), (1, 0), (1, 1), (0, 1)]
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(4859383997932765184), 0.001)
	Bool.True
		and cell.id() == S2CellId.from_id(4859383997932765184)
		and cell.level() == 4
		and cell.bound() == R2Rect.new(R1Interval.new(-0.1885, -0.08754166666666666), R1Interval.new(-0.547875, -0.41566666666666663))
		and cell.middle() == R2Rect.new(R1Interval.new(-0.13771875, -0.13571875), R1Interval.new(-0.48146875, -0.47946875))
		and cell.center() == S2Point.new(0.12230736471758044, 0.4298230245789255, 0.8945910105057312)
		and cell.entry_vertex() == S2Point.new(0.0814591518180723, 0.3833371850262226, 0.9200092440629343)
		and cell.exit_vertex() == S2Point.new(0.1705414337057506, 0.37898096379055685, 0.9095543130973365)
		and cell.padding() == 0.001
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(4859383997932765184), 0.001).child(0, 0)
	Bool.True
		and child.id() == S2CellId.from_id(4860509897839607808)
		and child.level() == 5
		and child.bound() == R2Rect.new(R1Interval.new(-0.1885, -0.13571875), R1Interval.new(-0.547875, -0.47946875))
		and child.middle() == R2Rect.new(R1Interval.new(-0.16278385416666666, -0.16078385416666666), R1Interval.new(-0.5143463541666666, -0.5123463541666666))
		and child.center() == S2Point.new(0.14245939016021336, 0.45202909111198486, 0.8805538160405946)
		and child.entry_vertex() == S2Point.new(0.12230736471758044, 0.4298230245789255, 0.8945910105057312)
		and child.exit_vertex() == S2Point.new(0.1666415549949205, 0.42701898467448385, 0.8887549599729094)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(4859383997932765184), 0.001).child(0, 1)
	Bool.True
		and child.id() == S2CellId.from_id(4862761697653293056)
		and child.level() == 5
		and child.bound() == R2Rect.new(R1Interval.new(-0.1885, -0.13571875), R1Interval.new(-0.48146875, -0.41566666666666663))
		and child.middle() == R2Rect.new(R1Interval.new(-0.16278385416666666, -0.16078385416666666), R1Interval.new(-0.4492421875, -0.4472421875))
		and child.center() == S2Point.new(0.1460481536625016, 0.40464448207900344, 0.9027362737448791)
		and child.entry_vertex() == S2Point.new(0.1666415549949205, 0.42701898467448385, 0.8887549599729094)
		and child.exit_vertex() == S2Point.new(0.1705414337057506, 0.37898096379055685, 0.9095543130973365)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(4859383997932765184), 0.001).child(1, 0)
	Bool.True
		and child.id() == S2CellId.from_id(4858258098025922560)
		and child.level() == 5
		and child.bound() == R2Rect.new(R1Interval.new(-0.13771875, -0.08754166666666666), R1Interval.new(-0.547875, -0.47946875))
		and child.middle() == R2Rect.new(R1Interval.new(-0.1133046875, -0.1113046875), R1Interval.new(-0.5143463541666666, -0.5123463541666666))
		and child.center() == S2Point.new(0.09941439265032596, 0.4544246295929393, 0.8852203310776852)
		and child.entry_vertex() == S2Point.new(0.0795548028505115, 0.4317017978211581, 0.8985013027822477)
		and child.exit_vertex() == S2Point.new(0.12230736471758044, 0.4298230245789255, 0.8945910105057312)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(4859383997932765184), 0.001).child(1, 1)
	Bool.True
		and child.id() == S2CellId.from_id(4856006298212237312)
		and child.level() == 5
		and child.bound() == R2Rect.new(R1Interval.new(-0.13771875, -0.08754166666666666), R1Interval.new(-0.48146875, -0.41566666666666663))
		and child.middle() == R2Rect.new(R1Interval.new(-0.1133046875, -0.1113046875), R1Interval.new(-0.4492421875, -0.4472421875))
		and child.center() == S2Point.new(0.10194642868912013, 0.4068992240722273, 0.9077664606752958)
		and child.entry_vertex() == S2Point.new(0.0814591518180723, 0.3833371850262226, 0.9200092440629343)
		and child.exit_vertex() == S2Point.new(0.0795548028505115, 0.4317017978211581, 0.8985013027822477)
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(4859383997932765184), 0.001)
	[cell.child_ij(0), cell.child_ij(1), cell.child_ij(2), cell.child_ij(3)] == [(1, 1), (1, 0), (0, 0), (0, 1)]
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 1.0e-09)
	Bool.True
		and cell.id() == S2CellId.from_id(13313594200290230272)
		and cell.level() == 14
		and cell.bound() == R2Rect.new(R1Interval.new(-0.32413085898422495, -0.32401657004492185), R1Interval.new(0.7750341286195984, 0.7751825312839279))
		and cell.middle() == R2Rect.new(R1Interval.new(-0.32407371427281, -0.32407371227280996), R1Interval.new(0.7751083277099997, 0.7751083297099997))
		and cell.center() == S2Point.new(0.5934665198968908, -0.24812905716825923, -0.7656562288326686)
		and cell.entry_vertex() == S2Point.new(0.5935097634442272, -0.24807963404753783, -0.7656387241168103)
		and cell.exit_vertex() == S2Point.new(0.5934968779252446, -0.24816174866893387, -0.7656221015556983)
		and cell.padding() == 1.0e-09
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 1.0e-09).child(0, 0)
	Bool.True
		and child.id() == S2CellId.from_id(13313594201363972096)
		and child.level() == 15
		and child.bound() == R2Rect.new(R1Interval.new(-0.32413085898422495, -0.32407371227280996), R1Interval.new(0.7750341286195984, 0.7751083297099997))
		and child.middle() == R2Rect.new(R1Interval.new(-0.32410228631807664, -0.3241022843180766), R1Interval.new(0.7750712278543582, 0.7750712298543582))
		and child.center() == S2Point.new(0.5934448967106659, -0.24815376971039432, -0.765664979704954)
		and child.entry_vertex() == S2Point.new(0.5934665198968908, -0.24812905716825923, -0.7656562288326686)
		and child.exit_vertex() == S2Point.new(0.5934600764993331, -0.24817011590528526, -0.7656479159332723)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 1.0e-09).child(0, 1)
	Bool.True
		and child.id() == S2CellId.from_id(13313594203511455744)
		and child.level() == 15
		and child.bound() == R2Rect.new(R1Interval.new(-0.32413085898422495, -0.32407371227280996), R1Interval.new(0.7751083277099997, 0.7751825312839279))
		and child.middle() == R2Rect.new(R1Interval.new(-0.32410228631807664, -0.3241022843180766), R1Interval.new(0.775145428186523, 0.7751454301865229))
		and child.center() == S2Point.new(0.5934816993644508, -0.2481454031927077, -0.7656391652690008)
		and child.entry_vertex() == S2Point.new(0.5934600764993331, -0.24817011590528526, -0.7656479159332723)
		and child.exit_vertex() == S2Point.new(0.5934968779252446, -0.24816174866893387, -0.7656221015556983)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 1.0e-09).child(1, 0)
	Bool.True
		and child.id() == S2CellId.from_id(13313594199216488448)
		and child.level() == 15
		and child.bound() == R2Rect.new(R1Interval.new(-0.32407371427281, -0.32401657004492185), R1Interval.new(0.7750341286195984, 0.7751083297099997))
		and child.middle() == R2Rect.new(R1Interval.new(-0.32404514284842506, -0.324045140848425), R1Interval.new(0.7750712278543582, 0.7750712298543582))
		and child.center() == S2Point.new(0.593451339522554, -0.24811271059560833, -0.7656732922466254)
		and child.entry_vertex() == S2Point.new(0.5934729620882208, -0.24808799887846877, -0.7656645401758594)
		and child.exit_vertex() == S2Point.new(0.5934665198968908, -0.24812905716825923, -0.7656562288326686)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 1.0e-09).child(1, 1)
	Bool.True
		and child.id() == S2CellId.from_id(13313594197069004800)
		and child.level() == 15
		and child.bound() == R2Rect.new(R1Interval.new(-0.32407371427281, -0.32401657004492185), R1Interval.new(0.7751083277099997, 0.7751825312839279))
		and child.middle() == R2Rect.new(R1Interval.new(-0.32404514284842506, -0.324045140848425), R1Interval.new(0.775145428186523, 0.7751454301865229))
		and child.center() == S2Point.new(0.5934881421414255, -0.24810434528060582, -0.765647476969918)
		and child.entry_vertex() == S2Point.new(0.5935097634442272, -0.24807963404753783, -0.7656387241168103)
		and child.exit_vertex() == S2Point.new(0.5934729620882208, -0.24808799887846877, -0.7656645401758594)
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 1.0e-09)
	[cell.child_ij(0), cell.child_ij(1), cell.child_ij(2), cell.child_ij(3)] == [(1, 1), (1, 0), (0, 0), (0, 1)]
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.5)
	Bool.True
		and cell.id() == S2CellId.from_id(3746994889972252672)
		and cell.level() == 1
		and cell.bound() == R2Rect.new(R1Interval.new(-0.5, 1.5), R1Interval.new(-0.5, 1.5))
		and cell.middle() == R2Rect.new(R1Interval.new(-0.08333333333333337, 0.9166666666666666), R1Interval.new(-0.08333333333333337, 0.9166666666666666))
		and cell.center() == S2Point.new(-0.35897907930886896, 0.8615497903412856, 0.35897907930886896)
		and cell.entry_vertex() == S2Point.new(-0.0, 1.0, 0.0)
		and cell.exit_vertex() == S2Point.new(-0.0, 0.7071067811865475, 0.7071067811865475)
		and cell.padding() == 0.5
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.5).child(0, 0)
	Bool.True
		and child.id() == S2CellId.from_id(3530822107858468864)
		and child.level() == 2
		and child.bound() == R2Rect.new(R1Interval.new(-0.5, 0.9166666666666666), R1Interval.new(-0.5, 0.9166666666666666))
		and child.middle() == R2Rect.new(R1Interval.new(-0.3125, 0.6875), R1Interval.new(-0.3125, 0.6875))
		and child.center() == S2Point.new(-0.1812366279990531, 0.9665953493282832, 0.1812366279990531)
		and child.entry_vertex() == S2Point.new(-0.0, 1.0, 0.0)
		and child.exit_vertex() == S2Point.new(-0.3846153846153846, 0.9230769230769231, 0.0)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.5).child(0, 1)
	Bool.True
		and child.id() == S2CellId.from_id(3963167672086036480)
		and child.level() == 2
		and child.bound() == R2Rect.new(R1Interval.new(-0.5, 0.9166666666666666), R1Interval.new(-0.08333333333333337, 1.5))
		and child.middle() == R2Rect.new(R1Interval.new(-0.3125, 0.6875), R1Interval.new(0.1875, 1.1875))
		and child.center() == S2Point.new(-0.1526959795677863, 0.8143785576948602, 0.5598852584152164)
		and child.entry_vertex() == S2Point.new(-0.28261670947211076, 0.6782801027330658, 0.6782801027330658)
		and child.exit_vertex() == S2Point.new(-0.0, 0.7071067811865475, 0.7071067811865475)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.5).child(1, 0)
	Bool.True
		and child.id() == S2CellId.from_id(3674937295934324736)
		and child.level() == 2
		and child.bound() == R2Rect.new(R1Interval.new(-0.08333333333333337, 1.5), R1Interval.new(-0.5, 0.9166666666666666))
		and child.middle() == R2Rect.new(R1Interval.new(0.1875, 1.1875), R1Interval.new(-0.3125, 0.6875))
		and child.center() == S2Point.new(-0.5598852584152164, 0.8143785576948602, 0.1526959795677863)
		and child.entry_vertex() == S2Point.new(-0.3846153846153846, 0.9230769230769231, 0.0)
		and child.exit_vertex() == S2Point.new(-0.35897907930886896, 0.8615497903412856, 0.35897907930886896)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.5).child(1, 1)
	Bool.True
		and child.id() == S2CellId.from_id(3819052484010180608)
		and child.level() == 2
		and child.bound() == R2Rect.new(R1Interval.new(-0.08333333333333337, 1.5), R1Interval.new(-0.08333333333333337, 1.5))
		and child.middle() == R2Rect.new(R1Interval.new(0.1875, 1.1875), R1Interval.new(0.1875, 1.1875))
		and child.center() == S2Point.new(-0.49292178644304296, 0.7169771439171534, 0.49292178644304296)
		and child.entry_vertex() == S2Point.new(-0.35897907930886896, 0.8615497903412856, 0.35897907930886896)
		and child.exit_vertex() == S2Point.new(-0.28261670947211076, 0.6782801027330658, 0.6782801027330658)
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.5)
	[cell.child_ij(0), cell.child_ij(1), cell.child_ij(2), cell.child_ij(3)] == [(0, 0), (1, 0), (1, 1), (0, 1)]
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(9223373024509096960), 1.0e-15)
	Bool.True
		and cell.id() == S2CellId.from_id(9223373024509096960)
		and cell.level() == 25
		and cell.bound() == R2Rect.new(R1Interval.new(-0.9990163869419578, -0.9990163074984166), R1Interval.new(-0.9982498670568819, -0.9982497876361965))
		and cell.middle() == R2Rect.new(R1Interval.new(-0.999016347220188, -0.999016347220186), R1Interval.new(-0.9982498273465399, -0.9982498273465379))
		and cell.center() == S2Point.new(-0.5768653414440085, -0.5778767254860258, 0.5773082954386122)
		and cell.entry_vertex() == S2Point.new(-0.5768653491108607, -0.5778767101784053, 0.5773083031003348)
		and cell.exit_vertex() == S2Point.new(-0.5768653643997533, -0.5778767254941024, 0.5773082724923949)
		and cell.padding() == 1.0e-15
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(9223373024509096960), 1.0e-15).child(0, 0)
	Bool.True
		and child.id() == S2CellId.from_id(9223373024509096192)
		and child.level() == 26
		and child.bound() == R2Rect.new(R1Interval.new(-0.9990163869419578, -0.999016347220186), R1Interval.new(-0.9982498670568819, -0.9982498273465379))
		and child.middle() == R2Rect.new(R1Interval.new(-0.9990163670810727, -0.9990163670810707), R1Interval.new(-0.9982498472017107, -0.9982498472017087))
		and child.center() == S2Point.new(-0.5768653452774347, -0.5778767178322156, 0.5773082992694736)
		and child.entry_vertex() == S2Point.new(-0.5768653491108607, -0.5778767101784053, 0.5773083031003348)
		and child.exit_vertex() == S2Point.new(-0.5768653337995621, -0.5778767178281768, 0.5773083107425819)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(9223373024509096960), 1.0e-15).child(0, 1)
	Bool.True
		and child.id() == S2CellId.from_id(9223373024509096704)
		and child.level() == 26
		and child.bound() == R2Rect.new(R1Interval.new(-0.9990163869419578, -0.999016347220186), R1Interval.new(-0.9982498273465399, -0.9982497876361965))
		and child.middle() == R2Rect.new(R1Interval.new(-0.9990163670810727, -0.9990163670810707), R1Interval.new(-0.998249807491369, -0.998249807491367))
		and child.center() == S2Point.new(-0.5768653299661358, -0.5778767254819872, 0.5773083069117206)
		and child.entry_vertex() == S2Point.new(-0.5768653337995621, -0.5778767178281768, 0.5773083107425819)
		and child.exit_vertex() == S2Point.new(-0.5768653414440085, -0.5778767254860258, 0.5773082954386122)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(9223373024509096960), 1.0e-15).child(1, 0)
	Bool.True
		and child.id() == S2CellId.from_id(9223373024509097728)
		and child.level() == 26
		and child.bound() == R2Rect.new(R1Interval.new(-0.999016347220188, -0.9990163074984166), R1Interval.new(-0.9982498670568819, -0.9982498273465379))
		and child.middle() == R2Rect.new(R1Interval.new(-0.9990163273593031, -0.9990163273593011), R1Interval.new(-0.9982498472017107, -0.9982498472017087))
		and child.center() == S2Point.new(-0.576865352921881, -0.5778767254900643, 0.5773082839655036)
		and child.entry_vertex() == S2Point.new(-0.5768653490884547, -0.5778767331438746, 0.577308280134642)
		and child.exit_vertex() == S2Point.new(-0.5768653643997533, -0.5778767254941024, 0.5773082724923949)
}
expect {
	child = S2PaddedCell.new(S2CellId.from_id(9223373024509096960), 1.0e-15).child(1, 1)
	Bool.True
		and child.id() == S2CellId.from_id(9223373024509097216)
		and child.level() == 26
		and child.bound() == R2Rect.new(R1Interval.new(-0.999016347220188, -0.9990163074984166), R1Interval.new(-0.9982498273465399, -0.9982497876361965))
		and child.middle() == R2Rect.new(R1Interval.new(-0.9990163273593031, -0.9990163273593011), R1Interval.new(-0.998249807491369, -0.998249807491367))
		and child.center() == S2Point.new(-0.5768653376105822, -0.5778767331398362, 0.5773082916077507)
		and child.entry_vertex() == S2Point.new(-0.5768653414440085, -0.5778767254860258, 0.5773082954386122)
		and child.exit_vertex() == S2Point.new(-0.5768653490884547, -0.5778767331438746, 0.577308280134642)
}
expect {
	cell = S2PaddedCell.new(S2CellId.from_id(9223373024509096960), 1.0e-15)
	[cell.child_ij(0), cell.child_ij(1), cell.child_ij(2), cell.child_ij(3)] == [(0, 0), (0, 1), (1, 1), (1, 0)]
}
# shrink_to_fit against upstream's ShrinkToFit.
expect S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0).shrink_to_fit(R2Rect.new(R1Interval.new(0.1, 0.2), R1Interval.new(0.3, 0.4))) == S2CellId.from_id(1224979098644774912)
expect S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.0).shrink_to_fit(R2Rect.new(R1Interval.new(-0.1, 0.2), R1Interval.new(0.3, 0.4))) == S2CellId.from_id(1152921504606846976)
expect S2PaddedCell.new(S2CellId.from_id(1152921504606846976), 0.001).shrink_to_fit(R2Rect.new(R1Interval.new(0.1, 0.10001), R1Interval.new(0.3, 0.30001))) == S2CellId.from_id(1266918870174662656)
expect S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.0).shrink_to_fit(R2Rect.new(R1Interval.new(-0.6, -0.59), R1Interval.new(0.21, 0.22))) == S2CellId.from_id(3746994889972252672)
expect S2PaddedCell.new(S2CellId.from_id(3746994889972252672), 0.01).shrink_to_fit(R2Rect.new(R1Interval.new(-0.6, -0.59), R1Interval.new(0.21, 0.22))) == S2CellId.from_id(3746994889972252672)
expect S2PaddedCell.new(S2CellId.from_id(13313594200290230272), 0.0).shrink_to_fit(R2Rect.new(R1Interval.new(-0.324096571902434, -0.32409542903304095), R1Interval.new(0.7751231700181961, 0.7751246540248394))) == S2CellId.from_id(13313594203029110784)

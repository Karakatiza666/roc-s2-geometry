import S1Angle
import S2Cap
import S2Cell
import S2CellId
import S2LatLng
import S2LatLngRect
import S2Metric
import S2Point

## A set of cells, held in normalized form: sorted, with no cell contained in
## another, and with no four siblings that could be replaced by their parent.
##
## Normalization is what makes the set operations linear and the containment
## test a binary search. Any list of cells can be normalized, so this is the
## general-purpose way to describe an arbitrary region to cell-level accuracy.
S2CellUnion := { ids : List(S2CellId) }.{

	## The union of the given cells, normalized.
	##
	## Ids that are not valid cells are dropped. Upstream requires valid ids.
	from_cell_ids : List(S2CellId) -> S2CellUnion
	from_cell_ids = |ids| {
		ids: normalize_sorted(sorted(ids.keep_if(S2CellId.is_valid))),
	}

	## The union of the cells with the given 64-bit encodings, normalized.
	## Ids that are not valid cells are dropped.
	from_ids : List(U64) -> S2CellUnion
	from_ids = |ids| S2CellUnion.from_cell_ids(ids.map(S2CellId.from_id))

	## The union of cells that are already sorted and non-overlapping.
	##
	## Skips the sort and the normalization pass, so the caller must have
	## established both.
	from_normalized_cell_ids : List(S2CellId) -> S2CellUnion
	from_normalized_cell_ids = |ids| { ids: ids }

	## The union of cells that are sorted and do not overlap, kept exactly as
	## given.
	##
	## Unlike `from_normalized_cell_ids`, it does not need four sibling cells
	## to have been replaced by their parent: the cells must pass `is_valid`
	## but need not pass `is_normalized`. Some operations give other answers on
	## a union that is not normalized, such as `contains_union`.
	from_verbatim : List(S2CellId) -> S2CellUnion
	from_verbatim = |ids| { ids: ids }

	## The union of all the leaf cells from `min_id` to `max_id`, both
	## included, as a normalized list of the fewest cells.
	##
	## Both ids must be leaf cells, with `min_id` not after `max_id`.
	from_min_max : S2CellId, S2CellId -> S2CellUnion
	from_min_max = |min_id, max_id| S2CellUnion.from_begin_end(min_id, max_id.next())

	## The union of all the leaf cells from `begin` up to, but not including,
	## `end`. When the two are equal, the union is empty.
	##
	## Both ids must be leaf cells, or the end of the leaf cells, with `begin`
	## not after `end`.
	from_begin_end : S2CellId, S2CellId -> S2CellUnion
	from_begin_end = |begin, end| {
		var $ids = []
		var $id = begin.maximum_tile(end)
		var $more = Bool.True
		while $more and $id != end {
			$ids = $ids.append($id)
			next = $id.next().maximum_tile(end)
			# Stop if the id wrapped past the last cell, which a valid range
			# cannot do.
			if next <= $id {
				$more = Bool.False
			} else {
				$id = next
			}
		}
		{ ids: $ids }
	}

	## The union that contains no cell.
	empty : () -> S2CellUnion
	empty = || { ids: [] }

	## The union covering the whole sphere: the six face cells.
	whole_sphere : () -> S2CellUnion
	whole_sphere = || {
		ids: [
			S2CellId.from_face(0),
			S2CellId.from_face(1),
			S2CellId.from_face(2),
			S2CellId.from_face(3),
			S2CellId.from_face(4),
			S2CellId.from_face(5),
		],
	}

	## The ids of the cells, in the order stored.
	cell_ids : S2CellUnion -> List(S2CellId)
	cell_ids = |u| u.ids

	## The number of cells in the union.
	num_cells : S2CellUnion -> U64
	num_cells = |u| u.ids.len()

	## The id of the `index`-th cell, or `OutOfBounds` when there is no such
	## cell.
	cell_id_at : S2CellUnion, U64 -> Try(S2CellId, [OutOfBounds])
	cell_id_at = |u, index| u.ids.get(index)

	## True when the union has no cell.
	is_empty : S2CellUnion -> Bool
	is_empty = |u| u.ids.is_empty()

	## True when every cell is valid and the cells are sorted and do not
	## overlap.
	is_valid : S2CellUnion -> Bool
	is_valid = |u| ids_in_order(u.ids)

	## True when the union is valid and also has no four siblings that a
	## parent could replace.
	is_normalized : S2CellUnion -> Bool
	is_normalized = |u| {
		if !ids_in_order(u.ids) {
			return Bool.False
		}
		var $ok = Bool.True
		for index in (3.U64).until(u.ids.len()) {
			a = (u.ids.get(index - 3) ?? S2CellId.none()).id()
			b = (u.ids.get(index - 2) ?? S2CellId.none()).id()
			c = (u.ids.get(index - 1) ?? S2CellId.none()).id()
			d = u.ids.get(index) ?? S2CellId.none()
			if a.bitwise_xor(b).bitwise_xor(c) == d.id() {
				step = d.lsb().shl_wrap(1)
				mask = step.plus_wrap(step.shl_wrap(1)).bitwise_not()
				wanted = d.id().bitwise_and(mask)
				if a.bitwise_and(mask) == wanted
					and b.bitwise_and(mask) == wanted
					and c.bitwise_and(mask) == wanted
					and !d.is_face() {
					$ok = Bool.False
				}
			}
		}
		$ok
	}

	## True when the union covers the whole of the given cell.
	contains_cell_id : S2CellUnion, S2CellId -> Bool
	contains_cell_id = |u, cell_id| {
		index = lower_bound(u, cell_id)
		if index < u.ids.len() and (u.ids.get(index) ?? S2CellId.sentinel()).range_min() <= cell_id {
			return Bool.True
		}
		index != 0 and (u.ids.get(index - 1) ?? S2CellId.none()).range_max() >= cell_id
	}

	## True when the union covers any part of the given cell.
	intersects_cell_id : S2CellUnion, S2CellId -> Bool
	intersects_cell_id = |u, cell_id| {
		index = lower_bound(u, cell_id)
		if index < u.ids.len()
			and (u.ids.get(index) ?? S2CellId.sentinel()).range_min() <= cell_id.range_max() {
			return Bool.True
		}
		index != 0 and (u.ids.get(index - 1) ?? S2CellId.none()).range_max() >= cell_id.range_min()
	}

	## True when the leaf cell that holds the point is in the union.
	contains_point : S2CellUnion, S2Point -> Bool
	contains_point = |u, p| u.contains_cell_id(S2CellId.from_point(p))

	## True when the leaf cell that holds the position is in the union.
	contains_lat_lng : S2CellUnion, S2LatLng -> Bool
	contains_lat_lng = |u, ll| u.contains_cell_id(S2CellId.from_lat_lng(ll))

	## True when the union covers every cell of `other`. Every union contains
	## an empty union.
	contains_union : S2CellUnion, S2CellUnion -> Bool
	contains_union = |u, other| {
		var $ok = Bool.True
		for cell_id in other.ids {
			if !u.contains_cell_id(cell_id) {
				$ok = Bool.False
			}
		}
		$ok
	}

	## True when the union covers part of at least one cell of `other`. An
	## empty union intersects nothing.
	intersects_union : S2CellUnion, S2CellUnion -> Bool
	intersects_union = |u, other| {
		var $hit = Bool.False
		for cell_id in other.ids {
			if u.intersects_cell_id(cell_id) {
				$hit = Bool.True
			}
		}
		$hit
	}

	## Every point in either union.
	union : S2CellUnion, S2CellUnion -> S2CellUnion
	union = |u, other| S2CellUnion.from_cell_ids(u.ids.concat(other.ids))

	## Every point in both unions.
	##
	## Linear in the two sizes: because both are normalized, two cells that
	## meet at all must have one containing the other.
	intersection : S2CellUnion, S2CellUnion -> S2CellUnion
	intersection = |u, other| {
		var $out = []
		var $i = 0
		var $j = 0
		while $i < u.ids.len() and $j < other.ids.len() {
			x = u.ids.get($i) ?? S2CellId.none()
			y = other.ids.get($j) ?? S2CellId.none()
			if x.range_max().id() < y.range_min().id() {
				$i = $i + 1
			} else if y.range_max().id() < x.range_min().id() {
				$j = $j + 1
			} else if x.contains(y) {
				$out = $out.append(y)
				$j = $j + 1
			} else {
				$out = $out.append(x)
				$i = $i + 1
			}
		}
		{ ids: normalize_sorted($out) }
	}

	## Every point of this union that also lies in the given cell.
	intersection_with_cell_id : S2CellUnion, S2CellId -> S2CellUnion
	intersection_with_cell_id = |u, cell_id|
		u.intersection(S2CellUnion.from_normalized_cell_ids([cell_id]))

	## Every point in this union but not the other.
	difference : S2CellUnion, S2CellUnion -> S2CellUnion
	difference = |u, other| {
		var $out = []
		for cell_id in u.ids {
			$out = $out.concat(difference_of_cell(cell_id, other))
		}
		{ ids: normalize_sorted($out) }
	}

	## The union grown to include every cell at `level` that touches it.
	##
	## Coarsens any cell finer than `level` first, so the result is never
	## finer than `level`.
	expand_at_level : S2CellUnion, U64 -> S2CellUnion
	expand_at_level = |u, level| {
		level_lsb = S2CellId.lsb_for_level(level)
		var $out = []
		for cell_id in u.ids {
			coarsened = if cell_id.lsb() < level_lsb {
				cell_id.parent_at_level(level)
			} else {
				cell_id
			}
			$out = $out.append(coarsened)
			$out = $out.concat(coarsened.all_neighbors(level))
		}
		S2CellUnion.from_cell_ids($out)
	}

	## The union grown by at least `min_radius` in every direction.
	##
	## `max_level_diff` caps how much finer than the union's own coarsest cell
	## the expansion is allowed to work, which bounds the cell count at the
	## cost of expanding further than asked.
	expand_by_radius : S2CellUnion, S1Angle, U64 -> S2CellUnion
	expand_by_radius = |u, min_radius, max_level_diff| {
		if u.ids.is_empty() {
			return u
		}
		var $min_level = S2CellId.max_level
		for cell_id in u.ids {
			$min_level = $min_level.min(cell_id.level())
		}
		radius_level = S2Metric.min_width.max_level_for(min_radius.radians())
		# A radius wider than a face cell needs two passes: one at level 0, then
		# the normal one. The second pass uses the level found before the first.
		first = if radius_level == 0 and min_radius.radians() > S2Metric.min_width.value_at(0) {
			u.expand_at_level(0)
		} else {
			u
		}
		first.expand_at_level(($min_level + max_level_diff).min(radius_level))
	}

	## The same region as a list of cells no coarser than `min_level`, whose
	## levels are all congruent to `min_level` modulo `level_mod`.
	##
	## This is what a region coverer applies at the end to honour the level
	## constraints it was given.
	denormalize : S2CellUnion, U64, U64 -> List(S2CellId)
	denormalize = |u, min_level, level_mod| {
		var $out = []
		for cell_id in u.ids {
			level = cell_id.level()
			var $new_level = min_level.max(level)
			if level_mod > 1 {
				$new_level = $new_level
					+ (S2CellId.max_level - ($new_level - min_level)) % level_mod
				$new_level = $new_level.min(S2CellId.max_level)
			}
			if $new_level == level {
				$out = $out.append(cell_id)
			} else {
				$out = $out.concat(cell_id.children_at_level($new_level))
			}
		}
		$out
	}

	## The number of leaf cells the union covers.
	leaf_cells_covered : S2CellUnion -> U64
	leaf_cells_covered = |u| {
		var $total = 0
		for cell_id in u.ids {
			inverted = S2CellId.max_level - cell_id.level()
			$total = $total.plus_wrap((1.U64).shl_wrap((inverted * 2).to_u8_wrap()))
		}
		$total
	}

	## The area of the union using each cell's average area for its level.
	average_area : S2CellUnion -> F64
	average_area = |u| u.ids.fold(0.0, |acc, cell_id| acc + S2Metric.avg_area.value_at(cell_id.level()))

	## The area of the union to within a few percent.
	approx_area : S2CellUnion -> F64
	approx_area = |u|
		u.ids.fold(0.0, |acc, cell_id| acc + S2Cell.from_cell_id(cell_id).approx_area())

	## The area of the union, accurate to six digits.
	exact_area : S2CellUnion -> F64
	exact_area = |u|
		u.ids.fold(0.0, |acc, cell_id| acc + S2Cell.from_cell_id(cell_id).exact_area())

	## The bounding cap of the union.
	cap_bound : S2CellUnion -> S2Cap
	cap_bound = |u| {
		if u.ids.is_empty() {
			return S2Cap.empty()
		}
		# Centre the cap on the centroid of the cell centres, each weighted by
		# the average area of its level, then grow it to
		# cover every cell's own bounding cap.
		var $centroid = S2Point.zero()
		for cell_id in u.ids {
			area = S2Metric.avg_area.value_at(cell_id.level())
			$centroid = $centroid + cell_id.to_point().times(area)
		}
		axis = if $centroid == S2Point.zero() {
			S2Point.new(1.0, 0.0, 0.0)
		} else {
			$centroid.normalize()
		}
		var $cap = S2Cap.from_point(axis)
		for cell_id in u.ids {
			$cap = $cap.add_cap(S2Cap.from_cell(S2Cell.from_cell_id(cell_id)))
		}
		$cap
	}

	## The bounding rectangle of the union.
	rect_bound : S2CellUnion -> S2LatLngRect
	rect_bound = |u| {
		var $bound = S2LatLngRect.empty()
		for cell_id in u.ids {
			$bound = $bound.union(S2LatLngRect.from_cell(S2Cell.from_cell_id(cell_id)))
		}
		$bound
	}

	## True when the union covers the whole of the cell.
	contains_cell : S2CellUnion, S2Cell -> Bool
	contains_cell = |u, cell| u.contains_cell_id(cell.id())

	## True when the union covers any part of the cell. The answer is exact for
	## a cell union.
	may_intersect_cell : S2CellUnion, S2Cell -> Bool
	may_intersect_cell = |u, cell| u.intersects_cell_id(cell.id())

	is_eq : S2CellUnion, S2CellUnion -> Bool
	is_eq = |a, b| a.ids == b.ids

	to_inspect : S2CellUnion -> Str
	to_inspect = |u| "S2CellUnion(${u.ids.len().to_str()} cells)"
}

expect S2CellUnion.empty().is_empty()
expect S2CellUnion.empty().num_cells() == 0
expect S2CellUnion.whole_sphere().num_cells() == 6
expect (S2CellUnion.whole_sphere().exact_area() - 4.0 * F64.pi).abs() < 1e-13
expect {
	# Four siblings collapse into their parent.
	parent = S2CellId.from_face(0).child(1)
	u = S2CellUnion.from_cell_ids(parent.children())
	u.num_cells() == 1 and (u.cell_id_at(0) ?? S2CellId.none()) == parent
}
expect {
	# A cell contained in another is dropped.
	parent = S2CellId.from_face(0).child(1)
	u = S2CellUnion.from_cell_ids([parent, parent.child(0), parent.child(1)])
	u.num_cells() == 1 and (u.cell_id_at(0) ?? S2CellId.none()) == parent
}
expect {
	# Cells come back sorted regardless of input order.
	u = S2CellUnion.from_cell_ids([S2CellId.from_face(3), S2CellId.from_face(1), S2CellId.from_face(5)])
	u.cell_ids() == [S2CellId.from_face(1), S2CellId.from_face(3), S2CellId.from_face(5)]
}
expect {
	# Collapsing cascades: all 16 grandchildren become the grandparent.
	parent = S2CellId.from_face(2).child(0)
	grandchildren = parent.children_at_level(parent.level() + 2)
	u = S2CellUnion.from_cell_ids(grandchildren)
	grandchildren.len() == 16 and u.num_cells() == 1 and (u.cell_id_at(0) ?? S2CellId.none()) == parent
}
expect {
	# Six face cells stay six cells: a face never collapses further.
	u = S2CellUnion.whole_sphere()
	u.num_cells() == 6
}
expect {
	cell_id = S2CellId.from_face(0).child(2)
	u = S2CellUnion.from_cell_ids([cell_id])
	u.contains_cell_id(cell_id)
		and u.contains_cell_id(cell_id.child(1))
		and !u.contains_cell_id(cell_id.parent())
		and u.intersects_cell_id(cell_id.parent())
}
expect {
	u = S2CellUnion.whole_sphere()
	u.contains_point(S2Point.new(1.0, 2.0, 3.0).normalize())
		and u.contains_lat_lng(S2LatLng.from_degrees(37.0, -122.0))
}
expect {
	a = S2CellUnion.from_cell_ids([S2CellId.from_face(0), S2CellId.from_face(1)])
	b = S2CellUnion.from_cell_ids([S2CellId.from_face(1), S2CellId.from_face(2)])
	a.union(b).num_cells() == 3
		and a.intersection(b).cell_ids() == [S2CellId.from_face(1)]
		and a.difference(b).cell_ids() == [S2CellId.from_face(0)]
}
expect {
	# The difference of a cell and one of its children is the other three.
	parent = S2CellId.from_face(4).child(1)
	a = S2CellUnion.from_cell_ids([parent])
	b = S2CellUnion.from_cell_ids([parent.child(2)])
	d = a.difference(b)
	d.num_cells() == 3 and !d.contains_cell_id(parent.child(2)) and d.contains_cell_id(parent.child(0))
}
expect {
	a = S2CellUnion.from_cell_ids([S2CellId.from_face(0)])
	a.difference(a).is_empty() and a.intersection(a) == a and a.union(a) == a
}
expect {
	parent = S2CellId.from_face(0).child(1)
	a = S2CellUnion.from_cell_ids([parent])
	a.intersection_with_cell_id(parent.child(0)).cell_ids() == [parent.child(0)]
}
expect {
	a = S2CellUnion.from_cell_ids([S2CellId.from_face(0), S2CellId.from_face(1)])
	b = S2CellUnion.from_cell_ids([S2CellId.from_face(0)])
	a.contains_union(b) and !b.contains_union(a) and a.intersects_union(b)
}
expect {
	# Expanding a single cell brings in its neighbors.
	cell_id = S2CellId.from_face(0).child_begin_at_level(5)
	u = S2CellUnion.from_cell_ids([cell_id])
	expanded = u.expand_at_level(5)
	expanded.num_cells() > 1 and expanded.contains_cell_id(cell_id)
}
expect {
	cell_id = S2CellId.from_face(0).child_begin_at_level(10)
	u = S2CellUnion.from_cell_ids([cell_id])
	expanded = u.expand_by_radius(S1Angle.from_degrees(1.0), 2)
	expanded.contains_cell_id(cell_id)
}
expect {
	# A radius wider than a face cell expands at level 0 and then once more, so
	# one level 10 cell reaches past its face's neighbors.
	cell_id = S2CellId.from_face(0).child_begin_at_level(10)
	u = S2CellUnion.from_cell_ids([cell_id])
	expanded = u.expand_by_radius(S1Angle.from_degrees(80.0), 2)
	expected = u.expand_at_level(0).expand_at_level(0)
	expanded == expected and expanded.num_cells() > u.expand_at_level(0).num_cells()
}
expect {
	# Denormalizing to a finer level replaces each cell with its descendants.
	u = S2CellUnion.from_cell_ids([S2CellId.from_face(0)])
	u.denormalize(2, 1).len() == 16
}
expect {
	u = S2CellUnion.from_cell_ids([S2CellId.from_face(0)])
	u.denormalize(0, 1) == [S2CellId.from_face(0)]
}
expect S2CellUnion.whole_sphere().leaf_cells_covered() == 6 * 1152921504606846976
expect {
	u = S2CellUnion.from_cell_ids([S2CellId.from_face(0)])
	(u.average_area() - 2.0943951023931953).abs() < 1e-15
		and u.approx_area() > 0.0
		and (u.exact_area() - 4.0 * F64.pi / 6.0).abs() < 1e-13
}
expect {
	u = S2CellUnion.from_cell_ids([S2CellId.from_face(0).child_begin_at_level(6)])
	cap = u.cap_bound()
	rect = u.rect_bound()
	cell = S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(6))
	cap.contains_point(cell.center()) and rect.contains_point(cell.center())
}
expect S2CellUnion.empty().cap_bound().is_empty()
expect S2CellUnion.empty().rect_bound().is_empty()
expect {
	u = S2CellUnion.from_ids([S2CellId.from_face(0).id()])
	u.contains_cell(S2Cell.from_face(0)) and u.may_intersect_cell(S2Cell.from_face(0))
}
expect S2CellUnion.from_ids([0]).is_empty()
expect S2CellUnion.from_ids([0, S2CellId.from_face(2).id(), 2]).cell_ids() == [S2CellId.from_face(2)]
expect S2CellUnion.from_ids([0]).is_valid() and S2CellUnion.from_ids([0]).is_normalized()
expect S2CellUnion.whole_sphere().is_normalized()
expect !S2CellUnion.from_normalized_cell_ids([S2CellId.none()]).is_valid()
expect {
	c = S2CellId.from_face(0).child(1)
	# Overlapping cells are not valid, and four siblings are not normalized.
	!S2CellUnion.from_normalized_cell_ids([c, c.child(0)]).is_valid()
		and S2CellUnion.from_normalized_cell_ids(c.children()).is_valid()
		and !S2CellUnion.from_normalized_cell_ids(c.children()).is_normalized()
}
expect {
	# The big cell outweighs the small one, so the cap axis stays near its centre.
	big = S2CellId.from_face(0)
	small = S2CellId.from_point(S2Point.new(0.0, 1.0, 0.0))
	axis = S2CellUnion.from_cell_ids([big, small]).cap_bound().center()
	axis.dot(S2Point.new(1.0, 0.0, 0.0)) > 0.99999
}

## True when every id is valid and each range ends before the next begins.
ids_in_order : List(S2CellId) -> Bool
ids_in_order = |ids| {
	var $ok = ids.first().map_ok(S2CellId.is_valid).ok_or(Bool.True)
	for index in (1.U64).until(ids.len()) {
		prev = ids.get(index - 1) ?? S2CellId.none()
		cur = ids.get(index) ?? S2CellId.none()
		if !cur.is_valid() or prev.range_max().id() >= cur.range_min().id() {
			$ok = Bool.False
		}
	}
	$ok
}

## The cells sorted by id.
sorted : List(S2CellId) -> List(S2CellId)
sorted = |ids| ids.map(S2CellId.id).sort().map(S2CellId.from_id)

## Collapses a sorted list into normal form.
##
## Drops cells contained in an earlier one, and folds any four siblings
## into their parent, repeatedly, so that the same region always has the
## same representation.
normalize_sorted : List(S2CellId) -> List(S2CellId)
normalize_sorted = |ids| {
	var $out = []
	for cell_id in ids {
		var $current = cell_id
		var $skip = Bool.False

		# Already covered by the cell before it.
		if !$out.is_empty() {
			last = $out.get($out.len() - 1) ?? $current
			if last.contains($current) {
				$skip = Bool.True
			}
		}

		if !$skip {
			# This cell swallows the ones before it.
			while !$out.is_empty() and $current.contains($out.get($out.len() - 1) ?? $current) {
				$out = $out.drop_last(1)
			}

			# Four siblings collapse into their parent, which may then
			# complete another set of four.
			var $merging = Bool.True
			while $merging and $out.len() >= 3 {
				a = ($out.get($out.len() - 3) ?? $current).id()
				b = ($out.get($out.len() - 2) ?? $current).id()
				c = ($out.get($out.len() - 1) ?? $current).id()
				if a.bitwise_xor(b).bitwise_xor(c) != $current.id() {
					$merging = Bool.False
				} else {
					step = $current.lsb().shl_wrap(1)
					mask = step.plus_wrap(step.shl_wrap(1)).bitwise_not()
					wanted = $current.id().bitwise_and(mask)
					if a.bitwise_and(mask) != wanted
						or b.bitwise_and(mask) != wanted
						or c.bitwise_and(mask) != wanted
						or $current.is_face() {
						$merging = Bool.False
					} else {
						$out = $out.drop_last(3)
						$current = $current.parent()
					}
				}
			}
			$out = $out.append($current)
		}
	}
	$out
}

## The index of the first cell not less than `target`.
lower_bound : S2CellUnion, S2CellId -> U64
lower_bound = |u, target| {
	var $low = 0
	var $high = u.ids.len()
	while $low < $high {
		mid = $low + ($high - $low) / 2
		if (u.ids.get(mid) ?? S2CellId.sentinel()).id() < target.id() {
			$low = mid + 1
		} else {
			$high = mid
		}
	}
	$low
}

## The part of one cell that `other` does not cover, refining the cell
## only where the two actually overlap.
difference_of_cell : S2CellId, S2CellUnion -> List(S2CellId)
difference_of_cell = |cell_id, other| {
	if !other.intersects_cell_id(cell_id) {
		[cell_id]
	} else if other.contains_cell_id(cell_id) {
		[]
	} else if cell_id.is_leaf() {
		[]
	} else {
		var $out = []
		for child in cell_id.children() {
			$out = $out.concat(difference_of_cell(child, other))
		}
		$out
	}
}

# The values below were printed by upstream's S2CellUnion at v0.14.0 through
# tools/s2_oracle.cc.
expect {
	cases = [
		{ min: 1451424208011999247, max: 1451424208011999253, ids: [1451424208011999247, 1451424208011999249, 1451424208011999251, 1451424208011999253] },
		{ min: 12306037041796219737, max: 12306037041796219739, ids: [12306037041796219737, 12306037041796219739] },
		{ min: 4646618397623473393, max: 4646618397623473593, ids: [4646618397623473396, 4646618397623473404, 4646618397623473472, 4646618397623473552, 4646618397623473572, 4646618397623473580, 4646618397623473588, 4646618397623473593] },
		{ min: 568131930826271257, max: 568131930826271259, ids: [568131930826271257, 568131930826271259] },
		{ min: 1072078284639251605, max: 1072078284639259797, ids: [1072078284639251605, 1072078284639251607, 1072078284639251612, 1072078284639251632, 1072078284639251664, 1072078284639251696, 1072078284639251776, 1072078284639251904, 1072078284639252224, 1072078284639253504, 1072078284639255552, 1072078284639257600, 1072078284639258880, 1072078284639259392, 1072078284639259712, 1072078284639259780, 1072078284639259788, 1072078284639259793, 1072078284639259795, 1072078284639259797] },
		{ min: 3595489801276268683, max: 3595489801276268689, ids: [3595489801276268683, 3595489801276268685, 3595489801276268687, 3595489801276268689] },
		{ min: 7357217347452862821, max: 7357217347452862825, ids: [7357217347452862821, 7357217347452862823, 7357217347452862825] },
		{ min: 7802400414888526771, max: 7802400414888526773, ids: [7802400414888526771, 7802400414888526773] },
		{ min: 7887724893851090945, max: 7887727092874346495, ids: [7887725993362718720] },
		{ min: 2305843009213693953, max: 4611686018427387903, ids: [3458764513820540928] },
		{ min: 1, max: 13835058055282163711, ids: [1152921504606846976, 3458764513820540928, 5764607523034234880, 8070450532247928832, 10376293541461622784, 12682136550675316736] },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			got = S2CellUnion.from_min_max(S2CellId.from_id(c.min), S2CellId.from_id(c.max))
			ok and got.cell_ids() == c.ids.map(S2CellId.from_id) and got.is_normalized()
		},
	)
}
expect {
	cases = [
		{ begin: 1451424208011999247, end: 1451424208011999255, ids: [1451424208011999247, 1451424208011999249, 1451424208011999251, 1451424208011999253] },
		{ begin: 12306037041796219737, end: 12306037041796219741, ids: [12306037041796219737, 12306037041796219739] },
		{ begin: 4646618397623473393, end: 4646618397623473595, ids: [4646618397623473396, 4646618397623473404, 4646618397623473472, 4646618397623473552, 4646618397623473572, 4646618397623473580, 4646618397623473588, 4646618397623473593] },
		{ begin: 568131930826271257, end: 568131930826271261, ids: [568131930826271257, 568131930826271259] },
		{ begin: 1072078284639251605, end: 1072078284639259799, ids: [1072078284639251605, 1072078284639251607, 1072078284639251612, 1072078284639251632, 1072078284639251664, 1072078284639251696, 1072078284639251776, 1072078284639251904, 1072078284639252224, 1072078284639253504, 1072078284639255552, 1072078284639257600, 1072078284639258880, 1072078284639259392, 1072078284639259712, 1072078284639259780, 1072078284639259788, 1072078284639259793, 1072078284639259795, 1072078284639259797] },
		{ begin: 3595489801276268683, end: 3595489801276268691, ids: [3595489801276268683, 3595489801276268685, 3595489801276268687, 3595489801276268689] },
		{ begin: 7357217347452862821, end: 7357217347452862827, ids: [7357217347452862821, 7357217347452862823, 7357217347452862825] },
		{ begin: 7802400414888526771, end: 7802400414888526775, ids: [7802400414888526771, 7802400414888526773] },
		{ begin: 1451424208011999247, end: 1451424208011999247, ids: [] },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			got = S2CellUnion.from_begin_end(S2CellId.from_id(c.begin), S2CellId.from_id(c.end))
			ok and got.cell_ids() == c.ids.map(S2CellId.from_id) and got.is_normalized()
		},
	)
}
expect {
	# The end of the leaf cells is a valid end of a range.
	last = S2CellId.end(30)
	got = S2CellUnion.from_begin_end(S2CellId.begin(30), last)
	got == S2CellUnion.whole_sphere()
}
expect {
	# FromVerbatim keeps the cells it is given, and the flags are upstream's
	# IsValid and IsNormalized.
	cases = [
		{ ids: [288230376151711744, 864691128455135232, 1441151880758558720, 2017612633061982208], valid: Bool.True, normalized: Bool.False },
		{ ids: [1152921504606846976, 3458764513820540928], valid: Bool.True, normalized: Bool.True },
		{ ids: [3458764513820540928, 1152921504606846976], valid: Bool.False, normalized: Bool.False },
		{ ids: [1152921504606846976, 864691128455135232], valid: Bool.False, normalized: Bool.False },
		{ ids: [], valid: Bool.True, normalized: Bool.True },
		{ ids: [288230376151711744, 864691128455135232, 1441151880758558720, 3458764513820540928], valid: Bool.True, normalized: Bool.True },
		{ ids: [288230376151711744, 288230376151711744], valid: Bool.False, normalized: Bool.False },
		{ ids: [0], valid: Bool.False, normalized: Bool.False },
		{ ids: [1152921504606846976, 99999], valid: Bool.False, normalized: Bool.False },
	]
	cases.fold(
		Bool.True,
		|ok, c| {
			ids = c.ids.map(S2CellId.from_id)
			got = S2CellUnion.from_verbatim(ids)
			ok and got.cell_ids() == ids and got.is_valid() == c.valid and got.is_normalized() == c.normalized
		},
	)
}

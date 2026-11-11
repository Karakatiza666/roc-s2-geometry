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
	from_cell_ids : List(S2CellId) -> S2CellUnion
	from_cell_ids = |ids| { ids: S2CellUnion.normalize_sorted(S2CellUnion.sorted(ids)) }

	## The union of the cells with the given 64-bit encodings, normalized.
	from_ids : List(U64) -> S2CellUnion
	from_ids = |ids| S2CellUnion.from_cell_ids(ids.map(S2CellId.from_id))

	## The union of cells that are already sorted and non-overlapping.
	##
	## Skips the sort and the normalization pass, so the caller must have
	## established both.
	from_normalized_cell_ids : List(S2CellId) -> S2CellUnion
	from_normalized_cell_ids = |ids| { ids: ids }

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

	cell_ids : S2CellUnion -> List(S2CellId)
	cell_ids = |u| u.ids

	num_cells : S2CellUnion -> U64
	num_cells = |u| u.ids.len()

	cell_id_at : S2CellUnion, U64 -> Try(S2CellId, [OutOfBounds])
	cell_id_at = |u, index| u.ids.get(index)

	is_empty : S2CellUnion -> Bool
	is_empty = |u| u.ids.is_empty()

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

	## True when the union covers the whole of the given cell.
	contains_cell_id : S2CellUnion, S2CellId -> Bool
	contains_cell_id = |u, cell_id| {
		index = u.lower_bound(cell_id)
		if index < u.ids.len() and (u.ids.get(index) ?? S2CellId.sentinel()).range_min() <= cell_id {
			return Bool.True
		}
		index != 0 and (u.ids.get(index - 1) ?? S2CellId.none()).range_max() >= cell_id
	}

	## True when the union covers any part of the given cell.
	intersects_cell_id : S2CellUnion, S2CellId -> Bool
	intersects_cell_id = |u, cell_id| {
		index = u.lower_bound(cell_id)
		if index < u.ids.len()
			and (u.ids.get(index) ?? S2CellId.sentinel()).range_min() <= cell_id.range_max() {
			return Bool.True
		}
		index != 0 and (u.ids.get(index - 1) ?? S2CellId.none()).range_max() >= cell_id.range_min()
	}

	contains_point : S2CellUnion, S2Point -> Bool
	contains_point = |u, p| u.contains_cell_id(S2CellId.from_point(p))

	contains_lat_lng : S2CellUnion, S2LatLng -> Bool
	contains_lat_lng = |u, ll| u.contains_cell_id(S2CellId.from_lat_lng(ll))

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
		{ ids: S2CellUnion.normalize_sorted($out) }
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
			$out = $out.concat(S2CellUnion.difference_of_cell(cell_id, other))
		}
		{ ids: S2CellUnion.normalize_sorted($out) }
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
				$out = $out.concat(S2CellUnion.difference_of_cell(child, other))
			}
			$out
		}
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
		if radius_level == 0 and min_radius.radians() > S2Metric.min_width.value_at(0) {
			# Wider than a face cell, so nothing finer than level 0 will do.
			u.expand_at_level(0)
		} else {
			u.expand_at_level(($min_level + max_level_diff).min(radius_level))
		}
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
		# Centre the cap on the centroid of the cell centres, then grow it to
		# cover every cell's own bounding cap.
		var $centroid = S2Point.zero()
		for cell_id in u.ids {
			$centroid = $centroid + cell_id.to_point()
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

	contains_cell : S2CellUnion, S2Cell -> Bool
	contains_cell = |u, cell| u.contains_cell_id(cell.id())

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

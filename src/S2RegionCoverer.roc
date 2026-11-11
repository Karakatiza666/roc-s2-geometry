import S1Angle
import S2Cap
import S2Cell
import S2CellId
import S2CellUnion
import S2LatLng
import S2LatLngRect
import S2Metric
import S2Point

## Approximates a region by a set of cells.
##
## The coverer refines cells that straddle the region's boundary, always
## splitting the one that promises the most improvement, until it has spent its
## budget of `max_cells`. The result is a covering, not a partition of the
## region: cells may extend outside it, and `interior_covering` gives the dual
## approximation whose cells all lie inside.
##
##     S2RegionCoverer.default()
##         .with_max_cells(12)
##         .with_max_level(16)
##         .covering(cap)
##
## Any type works as a region if it provides `cap_bound`, `contains_cell`, and
## `may_intersect_cell`; `S2Cap`, `S2LatLngRect`, and `S2CellUnion` all do.
##
## `max_cells` is a budget, not a guarantee: the result may exceed it slightly
## when `min_level` or `level_mod` forces a finer subdivision than the budget
## would otherwise allow.
##
## Always set `max_level` before asking for an interior covering. An interior
## covering stops only when it has filled its budget, and cells that straddle
## the boundary never fill it, so with the default `max_level` of 30 the search
## can subdivide the boundary all the way down. Upstream behaves the same way.
S2RegionCoverer := { min_level : U64, max_level : U64, level_mod : U64, max_cells : U64 }.{

	## A coverer of at most 8 cells at any level.
	default : () -> S2RegionCoverer
	default = || { min_level: 0, max_level: 30, level_mod: 1, max_cells: 8 }

	## The cell budget. Larger budgets track the region more closely.
	with_max_cells : S2RegionCoverer, U64 -> S2RegionCoverer
	with_max_cells = |coverer, max_cells| { ..coverer, max_cells: max_cells }

	## The coarsest level any cell of the covering may have.
	with_min_level : S2RegionCoverer, U64 -> S2RegionCoverer
	with_min_level = |coverer, min_level| {
		..coverer,
		min_level: min_level.min(S2CellId.max_level),
	}

	## The finest level any cell of the covering may have.
	with_max_level : S2RegionCoverer, U64 -> S2RegionCoverer
	with_max_level = |coverer, max_level| {
		..coverer,
		max_level: max_level.min(S2CellId.max_level),
	}

	## Restricts the covering to levels congruent to `min_level` modulo this
	## value, which must be 1, 2, or 3.
	##
	## A value of 2 or 3 makes the covering coarser but lets a consumer index
	## fewer distinct levels.
	with_level_mod : S2RegionCoverer, U64 -> S2RegionCoverer
	with_level_mod = |coverer, level_mod| { ..coverer, level_mod: level_mod.max(1).min(3) }

	## The coarsest level any cell of the covering may have.
	min_level : S2RegionCoverer -> U64
	min_level = |coverer| coverer.min_level

	## The finest level any cell of the covering may have.
	max_level : S2RegionCoverer -> U64
	max_level = |coverer| coverer.max_level

	## The step between allowed levels. A value of 1 allows every level.
	level_mod : S2RegionCoverer -> U64
	level_mod = |coverer| coverer.level_mod

	## The cell budget of the covering.
	max_cells : S2RegionCoverer -> U64
	max_cells = |coverer| coverer.max_cells

	## Cells that together cover the whole region.
	covering : S2RegionCoverer, r -> List(S2CellId)
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	covering = |coverer, region| run(coverer, probe_of(region), Bool.False)

	## Cells that all lie within the region, together covering as much of it as
	## the budget allows.
	interior_covering : S2RegionCoverer, r -> List(S2CellId)
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	interior_covering = |coverer, region| run(coverer, probe_of(region), Bool.True)

	## `covering` as a cell union.
	##
	## The cells are the ones `covering` returns, unchanged. Like upstream's
	## `GetCovering`, the union is not normalized again, so the cells keep the
	## `min_level` and `level_mod` constraints.
	cell_union_covering : S2RegionCoverer, r -> S2CellUnion
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	cell_union_covering = |coverer, region| S2CellUnion.from_normalized_cell_ids(coverer.covering(region))

	## `interior_covering` as a cell union, with the cells unchanged.
	cell_union_interior_covering : S2RegionCoverer, r -> S2CellUnion
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	cell_union_interior_covering = |coverer, region|
		S2CellUnion.from_normalized_cell_ids(coverer.interior_covering(region))
}

## One cell under consideration, with the children it was refined into.
Candidate := { cell : S2Cell, is_terminal : Bool, children : List(Candidate) }

## A queue entry: the refinement priority and the candidate. The candidate
## with the lowest priority is refined first.
Entry : (U64, Candidate)

## The three questions the coverer asks of a region, bound to one region.
##
## Collecting them here keeps the generic constraint on the two public
## entry points instead of on every internal step.
Probe : {
	cap : S2Cap,
	contains_cell : S2Cell -> Bool,
	may_intersect_cell : S2Cell -> Bool,
}

## The work in progress: cells decided so far, and cells still to refine.
Search : { result : List(S2CellId), queue : List(Entry) }

## Binds a region's three region operations into a `Probe`.
probe_of : r -> Probe
	where [
		r.cap_bound : r -> S2Cap,
		r.contains_cell : r, S2Cell -> Bool,
		r.may_intersect_cell : r, S2Cell -> Bool,
	]
probe_of = |region| {
	cap: region.cap_bound(),
	contains_cell: |cell| region.contains_cell(cell),
	may_intersect_cell: |cell| region.may_intersect_cell(cell),
}

## The main loop, upstream's `GetCoveringInternal`: refine the most promising
## candidate until the budget is spent, then apply the level constraints.
run : S2RegionCoverer, Probe, Bool -> List(S2CellId)
run = |coverer, probe, interior| {
	var $search = initial_candidates(coverer, probe, interior)
	while !$search.queue.is_empty() and (!interior or $search.result.len() < coverer.max_cells) {
		match queue_pop($search.queue) {
			Ok((candidate, queue)) => {
				$search = refine(coverer, { ..$search, queue: queue }, probe, interior, candidate)
			}
			Err(Empty) => {}
		}
	}

	# Normalizing replaces four children by their parent, and denormalizing
	# then restores whatever min_level and level_mod require.
	normalized = S2CellUnion.from_cell_ids($search.result)
	if coverer.min_level > 0 or coverer.level_mod > 1 {
		normalized.denormalize(coverer.min_level, coverer.level_mod)
	} else {
		normalized.cell_ids()
	}
}

## One step of the main loop: either refines a candidate just taken from the
## queue into its children, or accepts it as it is.
refine : S2RegionCoverer, Search, Probe, Bool, Candidate -> Search
refine = |coverer, rest, probe, interior, candidate| {
	# An interior covering refines a candidate however many children it
	# has, and uses only the children that fit the budget. An exterior
	# covering must use all of them, so it refines only when they fit.
	# A candidate with one child is always refined: that cannot add a
	# cell, and it helps when min_level already forces too many cells.
	if interior
		or candidate.cell.level() < coverer.min_level
		or candidate.children.len() == 1
		or rest.result.len() + rest.queue.len() + candidate.children.len() <= coverer.max_cells {
		var $next = rest
		for child in candidate.children {
			if !interior or $next.result.len() < coverer.max_cells {
				$next = add_candidate(coverer, $next, probe, interior, Ok(child))
			}
		}
		$next
	} else {
		add_candidate(
			coverer,
			rest,
			probe,
			interior,
			Ok({ ..candidate, is_terminal: Bool.True }),
		)
	}
}

## The cells the search starts from, upstream's `GetInitialCandidates`.
##
## A small covering of the region's bound, of at most four cells, is a much
## better start than the six faces.
initial_candidates : S2RegionCoverer, Probe, Bool -> Search
initial_candidates = |coverer, probe, interior| {
	fast : S2RegionCoverer
	fast = {
		min_level: 0,
		max_level: coverer.max_level,
		level_mod: 1,
		max_cells: coverer.max_cells.min(4),
	}
	cells = adjust_cell_levels(
		coverer,
		canonicalize_covering(fast, cell_union_bound(probe.cap)),
	)
	var $search = { result: [], queue: [] }
	for cell_id in cells {
		$search = add_candidate(
			coverer,
			$search,
			probe,
			interior,
			new_candidate(coverer, probe, interior, S2Cell.from_cell_id(cell_id)),
		)
	}
	$search
}

## A few cells that together cover a cap, upstream's `S2Cap::GetCellUnionBound`.
##
## Upstream bounds every region except `S2Cap`, `S2Cell` and `S2Polygon` by
## the cells that cover its cap bound, so this is the bound of all of them but
## `S2Polygon`. Upstream bounds a polygon by the cells of its spatial index,
## which this port does not have, and a cell by the cell itself. A cell is not
## a region in this port.
##
## The cells are the four at the finest level at which the cap contains at
## most one cell vertex, around the vertex nearest the centre. A cap too large
## for that gets the six faces.
cell_union_bound : S2Cap -> List(S2CellId)
cell_union_bound = |cap| {
	level = S2Metric.min_width.max_level_for(cap.radius_angle().radians())
	if level == 0 {
		[0, 1, 2, 3, 4, 5].map(S2CellId.from_face)
	} else {
		S2CellId.from_point(cap.center()).vertex_neighbors(level - 1)
	}
}

## Upstream's `CanonicalizeCovering`: makes a covering satisfy the coverer's
## level constraints and, where it can, its budget.
##
## Cells that are too fine, or not on a level that `level_mod` allows, are
## replaced by ancestors. Then, while there are too many cells, the two
## adjacent cells with the finest common ancestor are replaced by that
## ancestor.
##
## Upstream runs a full covering instead when the covering is very large.
## The only caller passes a cell union bound, which has at most six cells, so
## that branch is not ported.
canonicalize_covering : S2RegionCoverer, List(S2CellId) -> List(S2CellId)
canonicalize_covering = |coverer, covering| {
	coarsened =
		if coverer.max_level < S2CellId.max_level or coverer.level_mod > 1 {
			covering.map(
				|cell_id| {
					level = cell_id.level()
					new_level = adjust_level(coverer, level.min(coverer.max_level))
					if (new_level != level) cell_id.parent_at_level(new_level) else cell_id
				},
			)
		} else {
			covering
		}
	normalized = S2CellUnion.from_cell_ids(coarsened)
	var $cells =
		if coverer.min_level > 0 or coverer.level_mod > 1 {
			normalized.denormalize(coverer.min_level, coverer.level_mod)
		} else {
			normalized.cell_ids()
		}
	if $cells.len() <= coverer.max_cells or is_canonical(coverer, $cells) {
		return $cells
	}
	while $cells.len() > coverer.max_cells {
		var $best = Err(NoPair)
		for index in (0.U64).until($cells.len() - 1) {
			a = $cells.get(index) ?? S2CellId.none()
			b = $cells.get(index + 1) ?? S2CellId.none()
			match a.common_ancestor_level(b) {
				Ok(common) => {
					level = adjust_level(coverer, common)
					better =
						match $best {
							Ok((_, best_level)) => level > best_level
							Err(NoPair) => Bool.True
						}
					if better {
						$best = Ok((index, level))
					}
				}
				Err(NoCommonAncestor) => {}
			}
		}
		match $best {
			Ok((best_index, best_level)) if best_level >= coverer.min_level => {
				var $level = best_level
				var $ancestor = ($cells.get(best_index) ?? S2CellId.none()).parent_at_level($level)
				$cells = replace_cells_with_ancestor($cells, $ancestor)

				# The new cell may complete a set of siblings at a coarser
				# level, and so on upward.
				var $merging = Bool.True
				while $merging and $level > coverer.min_level {
					$level = $level - coverer.level_mod
					$ancestor = $ancestor.parent_at_level($level)
					if contains_all_children(coverer, $cells, $ancestor) {
						$cells = replace_cells_with_ancestor($cells, $ancestor)
					} else {
						$merging = Bool.False
					}
				}
			}
			_ => {
				# No two cells can merge without breaking min_level.
				return $cells
			}
		}
	}
	$cells
}

## Upstream's `IsCanonical`: true when a covering already satisfies the
## coverer's level constraints and could not use fewer cells.
is_canonical : S2RegionCoverer, List(S2CellId) -> Bool
is_canonical = |coverer, covering| {
	min_level = coverer.min_level
	max_level = true_max_level(coverer)
	level_mod = coverer.level_mod
	too_many_cells = covering.len() > coverer.max_cells
	var $same_parent_count = 1.U64
	var $prev = S2CellId.none()
	for cell_id in covering {
		if !cell_id.is_valid() {
			return Bool.False
		}
		level = cell_id.level()
		if level < min_level or level > max_level {
			return Bool.False
		}
		if level_mod > 1 and (level - min_level) % level_mod != 0 {
			return Bool.False
		}
		if $prev != S2CellId.none() {
			# Sorted and not overlapping.
			if $prev.range_max().id() >= cell_id.range_min().id() {
				return Bool.False
			}

			# With too many cells, no two adjacent cells may share an
			# ancestor that min_level allows.
			if too_many_cells {
				match cell_id.common_ancestor_level($prev) {
					Ok(common) if common >= min_level => return Bool.False
					_ => {}
				}
			}

			# No complete set of 4 ** level_mod siblings.
			if level < min_level + level_mod
				or level != $prev.level()
				or cell_id.parent_at_level(level - level_mod) != $prev.parent_at_level(level - level_mod) {
				$same_parent_count = 1
			} else {
				$same_parent_count = $same_parent_count + 1
				if $same_parent_count == (1.U64).shl_wrap((2 * level_mod).to_u8_wrap()) {
					return Bool.False
				}
			}
		}
		$prev = cell_id
	}
	Bool.True
}

## The finest level a covering may use: `max_level`, lowered if necessary to
## a level that `level_mod` allows.
true_max_level : S2RegionCoverer -> U64
true_max_level = |coverer|
	if coverer.level_mod == 1 or coverer.max_level < coverer.min_level {
		coverer.max_level
	} else {
		coverer.max_level - (coverer.max_level - coverer.min_level) % coverer.level_mod
	}

## The finest level at or above `level` that `level_mod` allows.
adjust_level : S2RegionCoverer, U64 -> U64
adjust_level = |coverer, level|
	if coverer.level_mod > 1 and level > coverer.min_level {
		level - (level - coverer.min_level) % coverer.level_mod
	} else {
		level
	}

## Upstream's `AdjustCellLevels`: replaces each cell of a sorted list by its
## ancestor at the finest level `level_mod` allows, then drops the cells that
## an ancestor now contains.
adjust_cell_levels : S2RegionCoverer, List(S2CellId) -> List(S2CellId)
adjust_cell_levels = |coverer, cells| {
	if coverer.level_mod == 1 {
		return cells
	}
	var $out = []
	for original in cells {
		level = original.level()
		new_level = adjust_level(coverer, level)
		cell_id = if (new_level != level) original.parent_at_level(new_level) else original
		last = $out.last() ?? S2CellId.none()
		if $out.is_empty() or !last.contains(cell_id) {
			while !$out.is_empty() and cell_id.contains($out.last() ?? S2CellId.none()) {
				$out = $out.drop_last(1)
			}
			$out = $out.append(cell_id)
		}
	}
	$out
}

## True when a sorted covering holds every child of `ancestor` at the next
## level that `level_mod` allows.
contains_all_children : S2RegionCoverer, List(S2CellId), S2CellId -> Bool
contains_all_children = |coverer, covering, ancestor| {
	level = ancestor.level() + coverer.level_mod
	var $index = lower_bound(covering, ancestor.range_min().id())
	var $child = ancestor.child_begin_at_level(level)
	end = ancestor.child_end_at_level(level)
	while $child != end {
		match covering.get($index) {
			Ok(found) if found == $child => {
				$index = $index + 1
				$child = $child.next()
			}
			_ => return Bool.False
		}
	}
	Bool.True
}

## Replaces the cells of a sorted covering that `ancestor` contains by
## `ancestor` itself.
replace_cells_with_ancestor : List(S2CellId), S2CellId -> List(S2CellId)
replace_cells_with_ancestor = |covering, ancestor| {
	begin = lower_bound(covering, ancestor.range_min().id())
	end = lower_bound(covering, ancestor.range_max().id().plus_wrap(1))
	covering.take_first(begin).append(ancestor).concat(covering.drop_first(end))
}

## The index of the first cell of a sorted list whose id is at least `target`.
lower_bound : List(S2CellId), U64 -> U64
lower_bound = |cells, target| {
	var $low = 0
	var $high = cells.len()
	while $low < $high {
		mid = $low + ($high - $low) / 2
		if (cells.get(mid) ?? S2CellId.none()).id() < target {
			$low = mid + 1
		} else {
			$high = mid
		}
	}
	$low
}

## A candidate for one cell, upstream's `NewCandidate`, or `Err(Rejected)`
## when the cell cannot contribute to the covering.
new_candidate : S2RegionCoverer, Probe, Bool, S2Cell -> Try(Candidate, [Rejected])
new_candidate = |coverer, probe, interior, cell| {
	may_intersect = probe.may_intersect_cell
	if !may_intersect(cell) {
		return Err(Rejected)
	}
	if cell.level() < coverer.min_level {
		return Ok({ cell: cell, is_terminal: Bool.False, children: [] })
	}
	contains = probe.contains_cell
	if interior {
		if contains(cell) {
			Ok({ cell: cell, is_terminal: Bool.True, children: [] })
		} else if cell.level() + coverer.level_mod > coverer.max_level {
			Err(Rejected)
		} else {
			Ok({ cell: cell, is_terminal: Bool.False, children: [] })
		}
	} else {
		terminal = cell.level() + coverer.level_mod > coverer.max_level or contains(cell)
		Ok({ cell: cell, is_terminal: terminal, children: [] })
	}
}

## Upstream's `AddCandidate`: accepts a terminal candidate into the result,
## or refines it and queues it for later.
add_candidate : S2RegionCoverer, Search, Probe, Bool, Try(Candidate, [Rejected]) -> Search
add_candidate = |coverer, search, probe, interior, maybe| {
	candidate =
		match maybe {
			Ok(c) => c
			Err(Rejected) => return search
		}
	if candidate.is_terminal {
		return { ..search, result: search.result.append(candidate.cell.id()) }
	}

	# Expand one level at a time until min_level, so as not to skip over it.
	num_levels = if candidate.cell.level() < coverer.min_level {
		1
	} else {
		coverer.level_mod
	}
	(children, num_terminals) =
		expand_children(coverer, probe, interior, candidate.cell, num_levels)
	shift = (2 * coverer.level_mod).to_u8_wrap()

	if children.is_empty() {
		search
	} else if !interior
		and num_terminals == (1.U64).shl_wrap(shift)
		and candidate.cell.level() >= coverer.min_level {
		# Every descendant is terminal, so the cell itself will do. An
		# interior covering cannot do this: its children only meet the
		# region and may need refining.
		add_candidate(
			coverer,
			search,
			probe,
			interior,
			Ok({ ..candidate, is_terminal: Bool.True }),
		)
	} else {
		# Larger cells first, since they promise the most improvement. Among
		# cells of one size, fewer children first, and then fewer children
		# that cannot be refined further.
		priority = candidate.cell
			.level()
			.shl_wrap(shift)
			.plus_wrap(children.len())
			.shl_wrap(shift)
			.plus_wrap(num_terminals)
		{
			..search,
			queue: queue_push(search.queue, (priority, { ..candidate, children: children })),
		}
	}
}

## Upstream's `ExpandChildren`: subdivides a cell `num_levels` deep,
## collecting the candidates found at the bottom and counting how many of
## them need no further refinement.
expand_children : S2RegionCoverer, Probe, Bool, S2Cell, U64 -> (List(Candidate), U64)
expand_children = |coverer, probe, interior, cell, num_levels| {
	remaining = num_levels - 1
	may_intersect = probe.may_intersect_cell
	var $children = []
	var $num_terminals = 0
	for child_cell in cell.subdivide() {
		if remaining > 0 {
			if may_intersect(child_cell) {
				(deeper, deeper_terminals) =
					expand_children(coverer, probe, interior, child_cell, remaining)
				$children = $children.concat(deeper)
				$num_terminals = $num_terminals + deeper_terminals
			}
		} else {
			match new_candidate(coverer, probe, interior, child_cell) {
				Ok(child) => {
					$children = $children.append(child)
					if child.is_terminal {
						$num_terminals = $num_terminals + 1
					}
				}
				Err(Rejected) => {}
			}
		}
	}
	($children, $num_terminals)
}

# The queue is a binary heap that pops and pushes exactly as libc++'s
# std::priority_queue does. Candidates of equal priority leave the heap in
# an order that depends on the heap algorithm, and that order decides which
# of them the budget allows, so following one standard library exactly is
# what makes the coverings match upstream's cell for cell. libstdc++ breaks
# ties between two children the other way, so an upstream build against it
# can give a different covering when two candidates have equal priority.

## True when `a` is refined after `b`: the heap's "less than".
heap_less : Entry, Entry -> Bool
heap_less = |(pa, _ca), (pb, _cb)| pa > pb

## Adds an entry to the heap, as `std::push_heap` does.
queue_push : List(Entry), Entry -> List(Entry)
queue_push = |heap, entry| {
	pushed = heap.append(entry)
	sift_up(pushed, pushed.len())
}

## Removes the entry with the lowest priority, as `std::pop_heap` does.
queue_pop : List(Entry) -> Try((Candidate, List(Entry)), [Empty])
queue_pop = |heap| {
	len = heap.len()
	(_priority, top) =
		match heap.first() {
			Ok(entry) => entry
			Err(_) => return Err(Empty)
		}
	if len == 1 {
		return Ok((top, []))
	}

	# Floyd's method: move the hole at the root down to a leaf, always to
	# the child that comes first, preferring the left child on a tie.
	var $heap = heap
	var $hole = 0
	var $child = 0
	var $descending = Bool.True
	while $descending {
		$child = 2 * $child + 1
		left = $heap.get($child) ?? (0, top)
		right = $heap.get($child + 1) ?? left
		if $child + 1 < len and heap_less(left, right) {
			$child = $child + 1
		}
		$heap = put($heap, $hole, $heap.get($child) ?? left)
		$hole = $child
		if $child > (len - 2) / 2 {
			$descending = Bool.False
		}
	}

	# Fill the hole with the last entry and sift it back up.
	last = len - 1
	if $hole == last {
		Ok((top, $heap.drop_last(1)))
	} else {
		moved = $heap.get(last) ?? (0, top)
		Ok((top, sift_up(put($heap, $hole, moved).drop_last(1), $hole + 1)))
	}
}

## Moves the entry at `len - 1` up toward the root of the heap's first `len`
## entries until its parent comes before it, as libc++'s `__sift_up` does.
sift_up : List(Entry), U64 -> List(Entry)
sift_up = |heap, len| {
	if len <= 1 {
		return heap
	}
	var $hole = len - 1
	moving =
		match heap.get($hole) {
			Ok(entry) => entry
			Err(_) => return heap
		}
	var $parent = ($hole - 1) / 2
	if !heap_less(heap.get($parent) ?? moving, moving) {
		return heap
	}
	var $heap = heap
	var $rising = Bool.True
	while $rising {
		$heap = put($heap, $hole, $heap.get($parent) ?? moving)
		$hole = $parent
		if $parent == 0 {
			$rising = Bool.False
		} else {
			$parent = ($parent - 1) / 2
			if !heap_less($heap.get($parent) ?? moving, moving) {
				$rising = Bool.False
			}
		}
	}
	put($heap, $hole, moving)
}

## Replaces the entry at `index`, which the callers keep in bounds.
put : List(Entry), U64, Entry -> List(Entry)
put = |heap, index, entry| heap.set(index, entry) ?? heap

expect S2RegionCoverer.default().max_cells() == 8
expect S2RegionCoverer.default().min_level() == 0
expect S2RegionCoverer.default().max_level() == 30
expect S2RegionCoverer.default().level_mod() == 1
expect S2RegionCoverer.default().with_max_cells(20).max_cells() == 20
expect S2RegionCoverer.default().with_level_mod(7).level_mod() == 3
expect S2RegionCoverer.default().with_level_mod(0).level_mod() == 1
expect S2RegionCoverer.default().with_min_level(40).min_level() == 30
expect {
	# A covering of the whole sphere is the six face cells.
	cells = S2RegionCoverer.default().covering(S2Cap.full())
	cells.len() == 6
}
expect {
	# Every cell of a covering meets the region.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(37.77, -122.42).to_point(),
		S1Angle.from_degrees(1.0),
	)
	cells = S2RegionCoverer.default().with_max_cells(12).covering(cap)
	failures : U64
	failures = cells.fold(
		0,
		|acc, cell_id| if (cap.may_intersect_cell(S2Cell.from_cell_id(cell_id))) acc else acc + 1,
	)
	failures == 0 and cells.len() > 0
}
expect {
	# The covering really does cover: the cap's centre is inside it.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(37.77, -122.42).to_point(),
		S1Angle.from_degrees(1.0),
	)
	u = S2RegionCoverer.default().with_max_cells(12).cell_union_covering(cap)
	u.contains_point(cap.center())
}
expect {
	# Every cell of an interior covering lies inside the region.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(10.0, 20.0).to_point(),
		S1Angle.from_degrees(5.0),
	)
	cells = S2RegionCoverer.default().with_max_cells(20).with_max_level(12).interior_covering(cap)
	failures : U64
	failures = cells.fold(
		0,
		|acc, cell_id| if (cap.contains_cell(S2Cell.from_cell_id(cell_id))) acc else acc + 1,
	)
	failures == 0
}
expect {
	# An interior covering is contained by the exterior covering.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(10.0, 20.0).to_point(),
		S1Angle.from_degrees(5.0),
	)
	coverer = S2RegionCoverer.default().with_max_cells(20).with_max_level(12)
	outer = coverer.cell_union_covering(cap)
	inner = coverer.cell_union_interior_covering(cap)
	outer.contains_union(inner)
}
expect {
	# A larger budget tracks the region at least as closely.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(-33.87, 151.21).to_point(),
		S1Angle.from_degrees(2.0),
	)
	coarse = S2RegionCoverer.default().with_max_cells(4).cell_union_covering(cap)
	fine = S2RegionCoverer.default().with_max_cells(64).cell_union_covering(cap)
	fine.exact_area() <= coarse.exact_area() + 1e-12
}
expect {
	# min_level forces cells no coarser than requested.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S1Angle.from_degrees(10.0),
	)
	cells = S2RegionCoverer.default().with_max_cells(8).with_min_level(4).covering(cap)
	failures : U64
	failures = cells.fold(0, |acc, cell_id| if (cell_id.level() >= 4) acc else acc + 1)
	failures == 0
}
expect {
	# max_level forces cells no finer than requested.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S1Angle.from_degrees(0.001),
	)
	cells = S2RegionCoverer.default().with_max_cells(8).with_max_level(10).covering(cap)
	failures : U64
	failures = cells.fold(0, |acc, cell_id| if (cell_id.level() <= 10) acc else acc + 1)
	failures == 0
}
expect {
	# level_mod restricts the covering to every third level.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S1Angle.from_degrees(1.0),
	)
	cells = S2RegionCoverer.default()
		.with_max_cells(8)
		.with_min_level(2)
		.with_level_mod(3)
		.covering(cap)
	failures : U64
	failures = cells.fold(0, |acc, cell_id| if ((cell_id.level() - 2) % 3 == 0) acc else acc + 1)
	failures == 0 and cells.len() > 0
}
expect {
	# A rectangle is a region too.
	rect = S2LatLngRect.from_bounds(
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(10.0, 10.0),
	)
	u = S2RegionCoverer.default().with_max_cells(16).cell_union_covering(rect)
	u.contains_point(S2LatLng.from_degrees(5.0, 5.0).to_point())
}
expect {
	# So is a cell union.
	region = S2CellUnion.from_cell_ids([S2CellId.from_face(0).child_begin_at_level(4)])
	u = S2RegionCoverer.default().with_max_cells(8).cell_union_covering(region)
	u.contains_union(region)
}
expect {
	# An empty region covers nothing.
	S2RegionCoverer.default().covering(S2Cap.empty()).is_empty()
}
expect {
	# A point region gives a single cell containing that point.
	p = S2LatLng.from_degrees(37.77, -122.42).to_point()
	cap = S2Cap.from_point(p)
	cells = S2RegionCoverer.default().with_max_cells(1).with_max_level(12).covering(cap)
	cells.len() == 1 and (cells.get(0) ?? S2CellId.none()).contains(S2CellId.from_point(p))
}
expect {
	# The expected cells in this and the next five tests come from upstream's
	# C++ S2RegionCoverer at v0.14.0, through tools/cover_oracle.cc, with the
	# input line given in each comment. Here: capll 10 20 5 12 0 30 1.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(10.0, 20.0).to_point(),
		S1Angle.from_degrees(5.0),
	)
	S2RegionCoverer.default().with_max_cells(12).covering(cap).map(S2CellId.id)
		== [
			1211468299762663424,
			1217097799296876544,
			1218505174180429824,
			1231664129341652992,
			1232860397992673280,
			1238489897526886400,
			1642687964083388416,
			1644939763897073664,
			1669709561847611392,
			1671679886684585984,
			1672154875707785216,
		]
}
expect {
	# An interior covering refines a candidate even when not all of its
	# children fit the budget, and uses the ones that do, so it fills all 12
	# cells. The older algorithm drops such a candidate and returns fewer.
	# capll 10 20 5 12 0 12 1.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(10.0, 20.0).to_point(),
		S1Angle.from_degrees(5.0),
	)
	S2RegionCoverer.default()
		.with_max_cells(12)
		.with_max_level(12)
		.interior_covering(cap)
		.map(S2CellId.id)
		== [
			1208372075018846208,
			1210623874832531456,
			1211186824785952768,
			1212594199669506048,
			1214845999483191296,
			1235112197806358528,
			1237363997620043776,
			1238771372503597056,
			1239334322457018368,
			1241586122270703616,
			1644658288920363008,
			1669428086870900736,
		]
}
expect {
	# The interior covering with a max_level. capll 10 20 5 20 0 12 1.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(10.0, 20.0).to_point(),
		S1Angle.from_degrees(5.0),
	)
	S2RegionCoverer.default()
		.with_max_cells(20)
		.with_max_level(12)
		.interior_covering(cap)
		.map(S2CellId.id)
		== [
			1208372075018846208,
			1210623874832531456,
			1211186824785952768,
			1212594199669506048,
			1214845999483191296,
			1231945604318363648,
			1235112197806358528,
			1237363997620043776,
			1238771372503597056,
			1239334322457018368,
			1241586122270703616,
			1242078703479947264,
			1643039807804276736,
			1644658288920363008,
			1645221238873784320,
			1645573082594672640,
			1645713820083027968,
			1669076243150012416,
			1669428086870900736,
			1671609517940408320,
		]
}
expect {
	# A rectangle region. rect 0 0 10 10 16 0 30 1.
	rect = S2LatLngRect.from_point_pair(
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(10.0, 10.0),
	)
	S2RegionCoverer.default().with_max_cells(16).covering(rect).map(S2CellId.id)
		== [
			384307168202282325,
			1140536605631578112,
			1142788405445263360,
			1145040205258948608,
			1151795604700004352,
			1170935903116328960,
			1910652141911932928,
			1917407541352988672,
			1919659341166673920,
			1921911140980359168,
		]
}
expect {
	# min_level 4 needs 16 cells, four of which are siblings. The cell union
	# keeps them as they are, as upstream's FromVerbatim does, instead of
	# normalizing them into their level-3 parent. capll 0 0 10 8 4 30 1.
	cap = S2Cap.from_center_angle(
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S1Angle.from_degrees(10.0),
	)
	expected = [
		364791569817010176,
		373798769071751168,
		382805968326492160,
		391813167581233152,
		1121396307215253504,
		1130403506469994496,
		1139410705724735488,
		1148417904979476480,
		1157425104234217472,
		1166432303488958464,
		1175439502743699456,
		1184446701998440448,
		1914029841632460800,
		1923037040887201792,
		1932044240141942784,
		1941051439396683776,
	]
	coverer = S2RegionCoverer.default().with_max_cells(8).with_min_level(4)
	coverer.covering(cap).map(S2CellId.id) == expected
		and coverer.cell_union_covering(cap).cell_ids().map(S2CellId.id) == expected
}
expect {
	# A cell union region is covered by its own cell.
	# cells 1 4503599627370496 8 0 30 1.
	region = S2CellUnion.from_cell_ids([S2CellId.from_face(0).child_begin_at_level(4)])
	S2RegionCoverer.default().with_max_cells(8).covering(region).map(S2CellId.id)
		== [4503599627370496]
}

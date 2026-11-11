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

	## One cell under consideration, with the children it was refined into.
	Candidate := { cell : S2Cell, is_terminal : Bool, children : List(Candidate) }

	## A queue entry: the refinement priority, the cell id used to break ties,
	## and the candidate itself.
	Entry : (U64, U64, Candidate)

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

	min_level : S2RegionCoverer -> U64
	min_level = |coverer| coverer.min_level

	max_level : S2RegionCoverer -> U64
	max_level = |coverer| coverer.max_level

	level_mod : S2RegionCoverer -> U64
	level_mod = |coverer| coverer.level_mod

	max_cells : S2RegionCoverer -> U64
	max_cells = |coverer| coverer.max_cells

	## Cells that together cover the whole region.
	covering : S2RegionCoverer, r -> List(S2CellId)
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	covering = |coverer, region| coverer.run(S2RegionCoverer.probe_of(region), Bool.False)

	## Cells that all lie within the region, together covering as much of it as
	## the budget allows.
	interior_covering : S2RegionCoverer, r -> List(S2CellId)
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	interior_covering = |coverer, region| coverer.run(S2RegionCoverer.probe_of(region), Bool.True)

	## `covering` as a normalized cell union.
	##
	## Normalizing may merge four sibling cells into their parent, so the
	## union can have fewer cells than `covering` returns, and its cells may
	## be coarser than `min_level`.
	cell_union_covering : S2RegionCoverer, r -> S2CellUnion
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	cell_union_covering = |coverer, region| S2CellUnion.from_cell_ids(coverer.covering(region))

	## `interior_covering` as a normalized cell union.
	cell_union_interior_covering : S2RegionCoverer, r -> S2CellUnion
		where [
			r.cap_bound : r -> S2Cap,
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	cell_union_interior_covering = |coverer, region|
		S2CellUnion.from_cell_ids(coverer.interior_covering(region))

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

	## The main loop: refine the most promising candidate until the budget is
	## spent, then apply the level constraints.
	run : S2RegionCoverer, Probe, Bool -> List(S2CellId)
	run = |coverer, probe, interior| {
		var $search = coverer.initial_candidates(probe, interior)
		while !$search.queue.is_empty() {
			if interior and $search.result.len() >= coverer.max_cells {
				break
			}
			entry = $search.queue.get(0) ?? (0, 0, { cell: S2Cell.from_face(0), is_terminal: Bool.True, children: [] })
			(_priority, _tie, candidate) = entry
			rest = { ..$search, queue: $search.queue.drop_first(1) }

			# An interior covering does not need room for the cells still
			# queued, since queued cells are not part of the result.
			pending = if interior {
				0
			} else {
				rest.queue.len()
			}
			if candidate.cell.level() < coverer.min_level
				or candidate.children.len() == 1
				or rest.result.len() + pending + candidate.children.len() <= coverer.max_cells {
				var $next = rest
				for child in candidate.children {
					$next = coverer.add_candidate($next, probe, interior, Ok(child))
				}
				$search = $next
			} else if interior {
				$search = rest
			} else {
				$search = coverer.add_candidate(
					rest,
					probe,
					interior,
					Ok({ ..candidate, is_terminal: Bool.True }),
				)
			}
		}
		S2CellUnion.from_cell_ids($search.result)
			.denormalize(coverer.min_level, coverer.level_mod)
	}

	## The cells the search starts from.
	##
	## When the budget allows at least four cells, the four cells around the
	## bounding cap's centre are a much better start than the six faces.
	initial_candidates : S2RegionCoverer, Probe, Bool -> Search
	initial_candidates = |coverer, probe, interior| {
		empty : Search
		empty = { result: [], queue: [] }

		if coverer.max_cells >= 4 {
			from_cap = S2Metric.min_width.max_level_for(2.0 * probe.cap.radius_angle().radians())
			capped = from_cap.min(coverer.max_level).min(S2CellId.max_level - 1)
			level =
				if coverer.level_mod > 1 and capped > coverer.min_level {
					capped - (capped - coverer.min_level) % coverer.level_mod
				} else {
					capped
				}
			if level > 0 {
				var $search = empty
				for neighbor in S2CellId.from_point(probe.cap.center()).vertex_neighbors(level) {
					$search = coverer.add_candidate(
						$search,
						probe,
						interior,
						coverer.new_candidate(probe, interior, S2Cell.from_cell_id(neighbor)),
					)
				}
				return $search
			}
		}

		var $search = empty
		for face_index in (0.U64).until(6) {
			$search = coverer.add_candidate(
				$search,
				probe,
				interior,
				coverer.new_candidate(probe, interior, S2Cell.from_face(face_index)),
			)
		}
		$search
	}

	## A candidate for one cell, or `Err(Rejected)` when the cell cannot
	## contribute to the covering.
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

	## Accepts a terminal candidate into the result, or refines it and queues
	## it for later.
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

		num_levels = if candidate.cell.level() < coverer.min_level {
			1
		} else {
			coverer.level_mod
		}
		(children, num_terminals) =
			coverer.expand_children(probe, interior, candidate.cell, num_levels)

		if children.is_empty() {
			search
		} else if !interior
			and num_terminals == (1.U64).shl_wrap((2 * coverer.level_mod).to_u8_wrap())
			and candidate.cell.level() >= coverer.min_level {
			# Every descendant is terminal, so the cell itself will do.
			coverer.add_candidate(
				search,
				probe,
				interior,
				Ok({ ..candidate, is_terminal: Bool.True }),
			)
		} else {
			shift = (2 * coverer.level_mod).to_u8_wrap()
			priority = candidate.cell
				.level()
				.shl_wrap(shift)
				.plus_wrap(children.len())
				.shl_wrap(shift)
				.plus_wrap(num_terminals)
			{
				..search,
				queue: S2RegionCoverer.queue_insert(
					search.queue,
					(priority, candidate.cell.id().id(), { ..candidate, children: children }),
				),
			}
		}
	}

	## Subdivides a cell `num_levels` deep, collecting the candidates found at
	## the bottom and counting how many of them need no further refinement.
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
						coverer.expand_children(probe, interior, child_cell, remaining)
					$children = $children.concat(deeper)
					$num_terminals = $num_terminals + deeper_terminals
				}
			} else {
				match coverer.new_candidate(probe, interior, child_cell) {
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

	## Inserts an entry into the queue, which is kept ordered by priority and
	## then by cell id so that the search is deterministic.
	queue_insert : List(Entry), Entry -> List(Entry)
	queue_insert = |queue, entry| {
		var $low = 0
		var $high = queue.len()
		while $low < $high {
			mid = $low + ($high - $low) / 2
			existing = queue.get(mid) ?? entry
			if S2RegionCoverer.entry_before(existing, entry) {
				$low = mid + 1
			} else {
				$high = mid
			}
		}
		queue.take_first($low).append(entry).concat(queue.drop_first($low))
	}

	## True when `a` should be refined before `b`.
	entry_before : Entry, Entry -> Bool
	entry_before = |(pa, ia, _ca), (pb, ib, _cb)| if pa != pb {
		pa < pb
	} else {
		ia < ib
	}
}

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
	# Matches upstream's own covering of a 5 degree cap, cell for cell.
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
	# The same for an interior covering, which exercises the other branch of
	# the refinement loop.
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
			1218704529382440960,
			1231688249877987328,
			1231945604318363648,
			1232198423273275392,
			1235112197806358528,
			1237363997620043776,
			1238771372503597056,
			1239334322457018368,
			1241586122270703616,
			1242078703479947264,
			1643039807804276736,
			1644658288920363008,
			1645221238873784320,
			1669076243150012416,
			1669428086870900736,
		]
}
expect {
	# And for a rectangle region.
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

import S2LatLng
import S2Point
import S2Polyline

## Vertex alignments between polylines, and a representative polyline of a
## collection. Upstream's `s2polyline_alignment`.
##
## A vertex alignment, or warp, of polylines `a` and `b` pairs each vertex of
## `a` with at least one vertex of `b`, in order. Its cost is the sum of the
## chord distances between the paired vertices, and an optimal alignment is
## one of least cost. The functions here find one with dynamic time warping.
## Optimal alignments are not always unique.
##
## For example, take `a` with the vertices `(1, 0)`, `(5, 0)`, `(6, 0)` and
## `(9, 0)`, and `b` with `(2, 0)`, `(7, 0)` and `(8, 0)`, in a plane for
## simplicity. The optimal warp path is `(0, 0)`, `(1, 1)`, `(2, 1)`,
## `(3, 2)`, with the cost 1 + 2 + 1 + 1 = 5.
##
## The exact alignment uses time and memory in proportion to the product of
## the two vertex counts. The approximate one is FastDTW, by Stan Salvador
## and Philip Chan: it aligns polylines of half the resolution, and then
## searches only near the projected path.
##
## `get_medoid_polyline` and `get_consensus_polyline` find a representative
## of a collection. The medoid is a member of the collection. The consensus
## is a new polyline, made with Dynamic Time Warping Barycenter Averaging by
## F. Petitjean, A. Ketterlin and P. Gancarski.
##
## Upstream stops the program when a polyline is empty or a collection has
## no polyline. Here these functions return `Err(EmptyPolyline)` and
## `Err(NoPolylines)`.
S2PolylineAlignment := [].{

	## The result of an alignment. `alignment_cost` is the sum of the chord
	## distances (not squared) between the paired vertices. Each pair
	## `(i, j)` of `warp_path` pairs vertex `i` of `a` with vertex `j` of
	## `b`. The path starts at `(0, 0)` and ends at the last vertex of each
	## polyline.
	VertexAlignment : { alignment_cost : F64, warp_path : List((U64, U64)) }

	## The options of `get_medoid_polyline`. When `approx` is true, the
	## costs come from `get_approx_vertex_alignment` with its default
	## radius. When false, they are exact.
	MedoidOptions : { approx : Bool }

	## The options of `get_consensus_polyline`.
	##
	## - `approx`: when true, the alignments come from
	##   `get_approx_vertex_alignment` with its default radius. When false,
	##   they are exact.
	## - `seed_medoid`: when true, the start is the medoid of the collection,
	##   which costs more alignments but can give a better result. When
	##   false, the start is the first polyline.
	## - `iteration_cap`: the largest number of refinement steps.
	ConsensusOptions : { approx : Bool, seed_medoid : Bool, iteration_cap : U64 }

	## Upstream's default medoid options: `approx` is true.
	default_medoid_options : () -> MedoidOptions
	default_medoid_options = || { approx: Bool.True }

	## Upstream's default consensus options: `approx` is true, `seed_medoid`
	## is false, and `iteration_cap` is 5.
	default_consensus_options : () -> ConsensusOptions
	default_consensus_options = || { approx: Bool.True, seed_medoid: Bool.False, iteration_cap: 5 }

	## The optimal alignment of two polylines. It uses time and memory in
	## proportion to the product of the vertex counts.
	get_exact_vertex_alignment : S2Polyline, S2Polyline -> Try(VertexAlignment, [EmptyPolyline])
	get_exact_vertex_alignment = |a, b| {
		a_n = a.num_vertices()
		b_n = b.num_vertices()
		if a_n == 0 or b_n == 0 {
			return Err(EmptyPolyline)
		}
		strides = List.repeat({ start: 0, end: b_n.to_i64_wrap() }, a_n)
		Ok(dynamic_timewarp(a, b, strides))
	}

	## The cost of the optimal alignment of two polylines, without the warp
	## path. It uses time in proportion to the product of the vertex counts,
	## but memory only in proportion to the vertex count of `b`.
	get_exact_vertex_alignment_cost : S2Polyline, S2Polyline -> Try(F64, [EmptyPolyline])
	get_exact_vertex_alignment_cost = |a, b| {
		va = a.vertices()
		vb = b.vertices()
		if va.is_empty() or vb.is_empty() {
			return Err(EmptyPolyline)
		}
		var $cost = List.repeat(double_max, vb.len())
		var $left_diag_min_cost = 0.0
		for pa in va {
			var $col = 0
			for pb in vb {
				up_cost = $cost.get($col) ?? double_max
				here = $left_diag_min_cost.min(up_cost) + (pa - pb).norm()
				$cost = put($cost, $col, here)
				$left_diag_min_cost = here.min(up_cost)
				$col = $col + 1
			}
			$left_diag_min_cost = double_max
		}
		Ok($cost.last() ?? double_max)
	}

	## An approximately optimal alignment with FastDTW, with the default
	## radius: the fourth root of the larger vertex count, rounded down.
	get_approx_vertex_alignment : S2Polyline, S2Polyline -> Try(VertexAlignment, [EmptyPolyline])
	get_approx_vertex_alignment = |a, b| {
		max_length = a.num_vertices().max(b.num_vertices())
		S2PolylineAlignment.get_approx_vertex_alignment_with_radius(a, b, fourth_root(max_length))
	}

	## An approximately optimal alignment with FastDTW. The `radius` is how
	## far from the projected warp path the search goes: a smaller radius
	## is faster and less accurate.
	##
	## For short polylines, and when the search window would be nearly
	## full, this gives the exact alignment, as upstream does.
	get_approx_vertex_alignment_with_radius : S2Polyline, S2Polyline, U64 -> Try(VertexAlignment, [EmptyPolyline])
	get_approx_vertex_alignment_with_radius = |a, b, radius| {
		if a.num_vertices() == 0 or b.num_vertices() == 0 {
			return Err(EmptyPolyline)
		}
		Ok(approx_alignment(a, b, radius.to_i64_wrap()))
	}

	## The index of the medoid of the polylines: the one with the least sum
	## of alignment costs to all the others. A tie goes to the lowest index,
	## so of two polylines the result is always 0.
	##
	## It takes up to (N^2 - N) / 2 alignments of N polylines.
	get_medoid_polyline : List(S2Polyline), MedoidOptions -> Try(U64, [NoPolylines, EmptyPolyline])
	get_medoid_polyline = |polylines, options| {
		n = polylines.len()
		if n == 0 {
			return Err(NoPolylines)
		}
		var $costs = List.repeat(0.0, n)
		var $i = 0
		while $i < n {
			a = polylines.get($i) ?? S2Polyline.empty()
			var $j = $i + 1
			while $j < n {
				b = polylines.get($j) ?? S2Polyline.empty()
				cost = cost_fn(a, b, options.approx)?
				$costs = put($costs, $i, ($costs.get($i) ?? 0.0) + cost)
				$costs = put($costs, $j, ($costs.get($j) ?? 0.0) + cost)
				$j = $j + 1
			}
			$i = $i + 1
		}
		var $best = 0
		var $k = 1
		while $k < n {
			if ($costs.get($k) ?? 0.0) < ($costs.get($best) ?? 0.0) {
				$best = $k
			}
			$k = $k + 1
		}
		Ok($best)
	}

	## A consensus polyline of the collection, with Dynamic Time Warping
	## Barycenter Averaging. Each step aligns the current consensus with
	## every polyline, and moves each consensus vertex to the normalized sum
	## of the vertices paired with it. The steps stop when no vertex moves
	## by more than 1e-15 radians, or after `iteration_cap` steps.
	##
	## The result has as many vertices as the start polyline, and is
	## unlikely to equal any polyline of the collection. When the vertex
	## counts vary a lot, it can help to resample the polylines first.
	get_consensus_polyline : List(S2Polyline), ConsensusOptions -> Try(S2Polyline, [NoPolylines, EmptyPolyline])
	get_consensus_polyline = |polylines, options| {
		if polylines.is_empty() {
			return Err(NoPolylines)
		}
		seed_index =
			if options.seed_medoid {
				S2PolylineAlignment.get_medoid_polyline(polylines, { approx: options.approx })?
			} else {
				0
			}
		var $consensus = polylines.get(seed_index) ?? S2Polyline.empty()
		num_consensus_vertices = $consensus.num_vertices()
		var $converged = Bool.False
		var $iterations = 0
		while !$converged and $iterations < options.iteration_cap {
			var $points = List.repeat(S2Point.zero(), num_consensus_vertices)
			for polyline in polylines {
				alignment = alignment_fn($consensus, polyline, options.approx)?
				vertices = polyline.vertices()
				for (ci, pi) in alignment.warp_path {
					sum = ($points.get(ci) ?? S2Point.zero()) + (vertices.get(pi) ?? S2Point.zero())
					$points = put($points, ci, sum)
				}
			}
			new_consensus = S2Polyline.from_points($points.map(S2Point.normalize))
			$iterations = $iterations + 1
			$converged = new_consensus.approx_eq($consensus, 1.0e-15)
			$consensus = new_consensus
		}
		Ok($consensus)
	}
}

# A stride is the range of columns [start, end) of one row of a search
# window. A window is a list of strides, one per row, that starts at column
# 0, ends at the last column, and whose starts and ends never decrease.
Stride : { start : I64, end : I64 }

# The stride that holds every column.
all_columns : Stride
all_columns = { start: -1, end: 2147483647 }

# The largest finite double, upstream's DOUBLE_MAX.
double_max : F64
double_max = 1.7976931348623157e308

in_range : Stride, I64 -> Bool
in_range = |stride, index| stride.start <= index and index < stride.end

# The stride of the row, or every column for a row before 0. As upstream
# does, row 0 also gives every column; only the walk back reads it.
checked_stride : List(Stride), I64 -> Stride
checked_stride = |strides, row|
	if row > 0 {
		strides.get(row.to_u64_wrap()) ?? all_columns
	} else {
		all_columns
	}

# Upstream's BoundsCheckedTableCost, on a table of `cols` columns stored by
# rows.
table_cost : List(F64), I64, I64, I64, Stride -> F64
table_cost = |table, cols, row, col, stride|
	if row < 0 and col < 0 {
		0.0
	} else if row < 0 or col < 0 or !in_range(stride, col) {
		double_max
	} else {
		table.get((row * cols + col).to_u64_wrap()) ?? double_max
	}

# Dynamic time warping on the cells of the window. The table covers every
# cell, as upstream's does, and cells outside the window stay zero.
dynamic_timewarp : S2Polyline, S2Polyline, List(Stride) -> VertexAlignment
dynamic_timewarp = |a, b, strides| {
	va = a.vertices()
	vb = b.vertices()
	rows = va.len().to_i64_wrap()
	cols = vb.len().to_i64_wrap()
	var $costs = List.repeat(0.0, va.len() * vb.len())
	var $prev = all_columns
	var $row = 0
	while $row < rows {
		curr = strides.get($row.to_u64_wrap()) ?? all_columns
		pa = va.get($row.to_u64_wrap()) ?? S2Point.zero()
		var $col = curr.start
		while $col < curr.end {
			d_cost = table_cost($costs, cols, $row - 1, $col - 1, $prev)
			u_cost = table_cost($costs, cols, $row - 1, $col, $prev)
			l_cost = table_cost($costs, cols, $row, $col - 1, curr)
			pb = vb.get($col.to_u64_wrap()) ?? S2Point.zero()
			here = d_cost.min(u_cost).min(l_cost) + (pa - pb).norm()
			$costs = put($costs, ($row * cols + $col).to_u64_wrap(), here)
			$col = $col + 1
		}
		$prev = curr
		$row = $row + 1
	}

	# Walk back from the last cell to recover the warp path.
	var $path = []
	var $r = rows - 1
	var $c = cols - 1
	var $curr_stride = checked_stride(strides, $r)
	var $prev_stride = checked_stride(strides, $r - 1)
	while $r >= 0 and $c >= 0 {
		$path = $path.append(($r.to_u64_wrap(), $c.to_u64_wrap()))
		d_cost = table_cost($costs, cols, $r - 1, $c - 1, $prev_stride)
		u_cost = table_cost($costs, cols, $r - 1, $c, $prev_stride)
		l_cost = table_cost($costs, cols, $r, $c - 1, $curr_stride)
		if d_cost <= u_cost and d_cost <= l_cost {
			$r = $r - 1
			$c = $c - 1
			$curr_stride = checked_stride(strides, $r)
			$prev_stride = checked_stride(strides, $r - 1)
		} else if u_cost <= l_cost {
			$r = $r - 1
			$curr_stride = checked_stride(strides, $r)
			$prev_stride = checked_stride(strides, $r - 1)
		} else {
			$c = $c - 1
		}
	}
	{ alignment_cost: $costs.last() ?? 0.0, warp_path: $path.rev() }
}

# FastDTW on two polylines that are not empty.
approx_alignment : S2Polyline, S2Polyline, I64 -> VertexAlignment
approx_alignment = |a, b, radius| {
	# Upstream's switchover points to the exact computation, found by
	# benchmarks.
	size_switchover = 32
	density_switchover = 0.85
	a_n = a.num_vertices().to_i64_wrap()
	b_n = b.num_vertices().to_i64_wrap()
	exact = |_| dynamic_timewarp(a, b, List.repeat({ start: 0, end: b_n }, a.num_vertices()))
	if a_n - radius < size_switchover or b_n - radius < size_switchover {
		return exact({})
	}
	if (a_n.max(b_n) * (2 * radius + 1)).to_f64() > (a_n * b_n).to_f64() * density_switchover {
		return exact({})
	}
	proj = approx_alignment(half_resolution(a), half_resolution(b), radius)
	window = window_from_warp_path(proj.warp_path) |> upsample(a_n, b_n) |> dilate(radius)
	dynamic_timewarp(a, b, window)
}

# The window of the rows and columns a warp path visits.
window_from_warp_path : List((U64, U64)) -> List(Stride)
window_from_warp_path = |path| {
	var $strides = []
	var $prev_row = 0
	var $start = 0
	var $stop = 0
	for (row_u, col_u) in path {
		row = row_u.to_i64_wrap()
		col = col_u.to_i64_wrap()
		if row > $prev_row {
			$strides = $strides.append({ start: $start, end: $stop })
			$start = col
			$prev_row = row
		}
		$stop = col + 1
	}
	$strides.append({ start: $start, end: $stop })
}

# The window scaled up to `new_rows` rows and `new_cols` columns.
upsample : List(Stride), I64, I64 -> List(Stride)
upsample = |strides, new_rows, new_cols| {
	rows = strides.len().to_i64_wrap()
	cols = (strides.last() ?? { start: 0, end: 0 }).end
	row_scale = new_rows.to_f64() / rows.to_f64()
	col_scale = new_cols.to_f64() / cols.to_f64()
	var $out = []
	var $row = 0
	while $row < new_rows {
		from = strides.get(truncate(($row.to_f64() + 0.5) / row_scale)) ?? all_columns
		$out = $out.append({
			start: truncate(col_scale * from.start.to_f64() + 0.5).to_i64_wrap(),
			end: truncate(col_scale * from.end.to_f64() + 0.5).to_i64_wrap(),
		})
		$row = $row + 1
	}
	$out
}

# The window dilated by a square of half-width `radius`.
dilate : List(Stride), I64 -> List(Stride)
dilate = |strides, radius| {
	rows = strides.len().to_i64_wrap()
	cols = (strides.last() ?? { start: 0, end: 0 }).end
	var $out = []
	var $row = 0
	while $row < rows {
		prev_row = ($row - radius).max(0)
		next_row = ($row + radius).min(rows - 1)
		prev = strides.get(prev_row.to_u64_wrap()) ?? all_columns
		next = strides.get(next_row.to_u64_wrap()) ?? all_columns
		$out = $out.append({ start: (prev.start - radius).max(0), end: (next.end + radius).min(cols) })
		$row = $row + 1
	}
	$out
}

# The list with the item at `index` replaced, as upstream assigns in place.
put : List(a), U64, a -> List(a)
put = |list, index, value| list.set(index, value) ?? list

# A non-negative double rounded toward zero, as a C++ cast to int does.
truncate : F64 -> U64
truncate = |x| x.to_u64_wrap()

# The polyline of the vertices at even indices.
half_resolution : S2Polyline -> S2Polyline
half_resolution = |line| {
	vertices = line.vertices()
	var $kept = []
	var $i = 0
	while $i < vertices.len() {
		$kept = $kept.append(vertices.get($i) ?? S2Point.zero())
		$i = $i + 2
	}
	S2Polyline.from_points($kept)
}

# The largest r with r^4 <= n. Upstream casts pow(n, 0.25) to int. That pow
# is within one ulp of the exact root, and the root of a whole number that is
# not a fourth power is further than that below the next whole number, so the
# two agree.
fourth_root : U64 -> U64
fourth_root = |n| {
	var $r = 0
	while ($r + 1) * ($r + 1) * ($r + 1) * ($r + 1) <= n {
		$r = $r + 1
	}
	$r
}

cost_fn : S2Polyline, S2Polyline, Bool -> Try(F64, [EmptyPolyline])
cost_fn = |a, b, approx|
	if approx {
		S2PolylineAlignment.get_approx_vertex_alignment(a, b).map_ok(|v| v.alignment_cost)
	} else {
		S2PolylineAlignment.get_exact_vertex_alignment_cost(a, b)
	}

alignment_fn : S2Polyline, S2Polyline, Bool -> Try(VertexAlignment, [EmptyPolyline])
alignment_fn = |a, b, approx|
	if approx {
		S2PolylineAlignment.get_approx_vertex_alignment(a, b)
	} else {
		S2PolylineAlignment.get_exact_vertex_alignment(a, b)
	}

# Helpers of the tests below.
line : List((F64, F64)) -> S2Polyline
line = |points| S2Polyline.from_lat_lngs(points.map(|(lat, lng)| S2LatLng.from_degrees(lat, lng)))

# Three wiggly polylines of 40, 36 and 48 vertices, long enough for FastDTW
# to recurse. tools/s2_oracle.cc was given the same coordinates.
wiggle : U64, U64, U64, F64, F64, F64 -> S2Polyline
wiggle = |n, factor, modulus, lat_step, lat_offset, lng_step| {
	var $points = []
	var $i = 0
	while $i < n {
		lat = (($i * factor) % modulus).to_f64() * lat_step + lat_offset
		$points = $points.append(S2LatLng.from_degrees(lat, $i.to_f64() * lng_step))
		$i = $i + 1
	}
	S2Polyline.from_lat_lngs($points)
}

line_a : S2Polyline
line_a = wiggle(40, 37, 11, 0.3, 0.0, 0.5)

line_b : S2Polyline
line_b = wiggle(36, 23, 7, 0.4, 0.0, 0.55)

line_c : S2Polyline
line_c = wiggle(48, 5, 3, 0.2, 0.1, 0.45)

line_5 : S2Polyline
line_5 = line([(5.0, 0.0), (5.0, 1.0), (5.0, 2.0)])

line_3 : S2Polyline
line_3 = line([(3.0, 0.0), (3.0, 1.0), (3.0, 2.0)])

line_1 : S2Polyline
line_1 = line([(1.0, 0.0), (1.0, 1.0), (1.0, 2.0)])

line_3_long : S2Polyline
line_3_long = line([(3.0, 0.0), (3.0, 0.5), (3.0, 1.0), (3.0, 2.0)])

line_1_long : S2Polyline
line_1_long = line([(1.0, 0.0), (1.0, 0.5), (1.0, 1.0), (1.0, 1.5), (1.0, 2.0)])

# Both exact functions, against one cost and path.
exact_is : S2Polyline, S2Polyline, F64, List((U64, U64)) -> Bool
exact_is = |a, b, cost, path|
	match (S2PolylineAlignment.get_exact_vertex_alignment(a, b), S2PolylineAlignment.get_exact_vertex_alignment_cost(a, b)) {
		(Ok(v), Ok(c)) => v.alignment_cost == cost and c == cost and v.warp_path == path
		_ => Bool.False
	}

approx_is : Try(VertexAlignment, [EmptyPolyline]), F64, List((U64, U64)) -> Bool
approx_is = |result, cost, path|
	match result {
		Ok(v) => v.alignment_cost == cost and v.warp_path == path
		Err(_) => Bool.False
	}

consensus_is : List(S2Polyline), ConsensusOptions, List(S2Point) -> Bool
consensus_is = |polylines, options, expected|
	match S2PolylineAlignment.get_consensus_polyline(polylines, options) {
		Ok(result) => result.vertices() == expected
		Err(_) => Bool.False
	}

medoid : List(S2Polyline), Bool -> Try(U64, [NoPolylines, EmptyPolyline])
medoid = |polylines, approx| S2PolylineAlignment.get_medoid_polyline(polylines, { approx: approx })

consensus_options : Bool, Bool, U64 -> ConsensusOptions
consensus_options = |approx, seed_medoid, cap| { approx: approx, seed_medoid: seed_medoid, iteration_cap: cap }

# The window helpers, against the expected windows of upstream's
# s2polyline_alignment_test.cc. A stride is written (start, end).
strides_of : List((I64, I64)) -> List(Stride)
strides_of = |pairs| pairs.map(|(start, end)| { start: start, end: end })

# CreatesWindowFromWarpPath.
expect window_from_warp_path([(0, 0), (1, 0), (1, 1), (2, 1), (3, 1), (3, 2), (3, 3), (4, 4), (4, 5)]) == strides_of([(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)])
# UpsamplesWindowByFactorOfTwo.
expect upsample(strides_of([(0, 3), (1, 4), (2, 4), (3, 6), (4, 6)]), 10, 12) == strides_of([(0, 6), (0, 6), (2, 8), (2, 8), (4, 8), (4, 8), (6, 12), (6, 12), (8, 12), (8, 12)])
# UpsamplesWindowXAxisByFactorOfThree.
expect upsample(strides_of([(0, 3), (1, 4), (2, 4), (3, 6), (4, 6)]), 5, 18) == strides_of([(0, 9), (3, 12), (6, 12), (9, 18), (12, 18)])
# UpsamplesWindowYAxisByFactorOfThree.
expect upsample(strides_of([(0, 3), (1, 4), (2, 4), (3, 6), (4, 6)]), 15, 6) == strides_of([(0, 3), (0, 3), (0, 3), (1, 4), (1, 4), (1, 4), (2, 4), (2, 4), (2, 4), (3, 6), (3, 6), (3, 6), (4, 6), (4, 6), (4, 6)])
# UpsamplesWindowByNonInteger.
expect upsample(strides_of([(0, 3), (1, 4), (2, 4), (3, 6), (4, 6)]), 19, 23) == strides_of([(0, 12), (0, 12), (0, 12), (0, 12), (4, 15), (4, 15), (4, 15), (4, 15), (8, 15), (8, 15), (8, 15), (12, 23), (12, 23), (12, 23), (12, 23), (15, 23), (15, 23), (15, 23), (15, 23)])
# DilatesWindowByRadiusZero, RadiusOne, RadiusTwo and VeryLargeRadius.
expect dilate(strides_of([(0, 3), (2, 3), (2, 3), (2, 4), (3, 6)]), 0) == strides_of([(0, 3), (2, 3), (2, 3), (2, 4), (3, 6)])
expect dilate(strides_of([(0, 3), (2, 3), (2, 3), (2, 4), (3, 6)]), 1) == strides_of([(0, 4), (0, 4), (1, 5), (1, 6), (1, 6)])
expect dilate(strides_of([(0, 3), (2, 3), (2, 3), (2, 4), (3, 6)]), 2) == strides_of([(0, 5), (0, 6), (0, 6), (0, 6), (0, 6)])
expect dilate(strides_of([(0, 3), (2, 3), (2, 3), (2, 4), (3, 6)]), 100) == strides_of([(0, 6), (0, 6), (0, 6), (0, 6), (0, 6)])
# HalvesZeroLengthPolyline, HalvesEvenLengthPolyline and
# HalvesOddLengthPolyline.
expect half_resolution(S2Polyline.empty()) == S2Polyline.empty()
expect half_resolution(line([(0.0, 0.0), (0.0, 1.0), (0.0, 2.0), (1.0, 2.0)])) == line([(0.0, 0.0), (0.0, 2.0)])
expect half_resolution(line([(0.0, 0.0), (0.0, 1.0), (0.0, 2.0), (1.0, 2.0), (3.0, 5.0)])) == line([(0.0, 0.0), (0.0, 2.0), (3.0, 5.0)])
# The default radius is the fourth root of the larger vertex count, rounded
# down.
expect [fourth_root(0), fourth_root(1), fourth_root(15), fourth_root(16), fourth_root(80), fourth_root(81), fourth_root(1024)] == [0, 1, 1, 2, 2, 3, 5]

# The expected values below come from upstream's s2polyline_alignment,
# through the "al_exact", "al_approx", "al_medoid" and "al_consensus" queries
# of tools/s2_oracle.cc. The cases come from s2polyline_alignment_test.cc,
# under the test names in the comments, unless they say otherwise.
# ExactLengthZeroInputs, ExactLengthZeroInputA and ExactLengthZeroInputB:
# upstream stops the program.
expect S2PolylineAlignment.get_exact_vertex_alignment(S2Polyline.empty(), S2Polyline.empty()) == Err(EmptyPolyline)
expect S2PolylineAlignment.get_exact_vertex_alignment(S2Polyline.empty(), line_1) == Err(EmptyPolyline)
expect S2PolylineAlignment.get_exact_vertex_alignment_cost(line_1, S2Polyline.empty()) == Err(EmptyPolyline)
expect S2PolylineAlignment.get_approx_vertex_alignment(line_1, S2Polyline.empty()) == Err(EmptyPolyline)
expect S2PolylineAlignment.get_approx_vertex_alignment_with_radius(S2Polyline.empty(), line_1, 1) == Err(EmptyPolyline)
# ExactLengthOneInputs, ExactLengthOneInputA and ExactLengthOneInputB.
expect exact_is(line([(1.0, 1.0)]), line([(2.0, 2.0)]), 0.024677671064644264, [(0, 0)])
expect exact_is(line([(0.0, 0.0)]), line([(0.0, 0.0), (1.0, 1.0), (2.0, 2.0)]), 0.07403677143632582, [(0, 0), (0, 1), (0, 2)])
expect exact_is(line([(0.0, 0.0), (1.0, 1.0), (2.0, 2.0)]), line([(0.0, 0.0)]), 0.07403677143632582, [(0, 0), (1, 0), (2, 0)])
# ExactHeaderFileExample.
expect exact_is(line([(1.0, 0.0), (5.0, 0.0), (6.0, 0.0), (9.0, 0.0)]), line([(2.0, 0.0), (7.0, 0.0), (8.0, 0.0)]), 0.08726402586481065, [(0, 0), (1, 1), (2, 1), (3, 2)])
# DifferentPathForDistanceVersusSquaredDistance.
expect exact_is(line([(0.1, -0.1), (0.1, 0.0), (0.1, 0.1), (-0.1, 0.1)]), line([(0.1, -0.1), (-0.1, -0.1), (-0.1, 0.1)]), 0.0066818567044952554, [(0, 0), (1, 0), (2, 1), (3, 2)])
# Not from upstream's tests: identical polylines, and two long ones.
expect exact_is(line_1, line_1, 0.0, [(0, 0), (1, 1), (2, 2)])
expect exact_is(line_a, line_b, 0.5348443886085926, [(0, 0), (1, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 5), (6, 5), (7, 6), (8, 6), (9, 7), (9, 8), (10, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 15), (17, 15), (18, 16), (19, 17), (20, 18), (20, 19), (21, 20), (22, 21), (23, 22), (24, 22), (25, 22), (26, 23), (27, 24), (28, 25), (29, 26), (30, 27), (31, 28), (32, 29), (33, 29), (34, 30), (35, 31), (36, 32), (37, 33), (38, 34), (39, 35)])
# Not from upstream's tests: FastDTW where it recurses. With radius 1 the
# window misses the optimal path, and with the default radius, 2, it finds
# it.
expect approx_is(S2PolylineAlignment.get_approx_vertex_alignment_with_radius(line_a, line_b, 1), 0.5631745395444621, [(0, 0), (1, 1), (1, 2), (2, 3), (3, 4), (4, 4), (5, 5), (6, 5), (7, 6), (8, 6), (9, 7), (9, 8), (10, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 15), (17, 15), (18, 16), (19, 17), (20, 18), (21, 19), (22, 19), (23, 20), (24, 20), (25, 21), (25, 22), (26, 23), (27, 24), (28, 25), (29, 26), (30, 27), (31, 28), (32, 29), (33, 29), (34, 30), (35, 31), (36, 32), (37, 33), (38, 34), (39, 35)])
expect approx_is(S2PolylineAlignment.get_approx_vertex_alignment(line_a, line_b), 0.5348443886085926, [(0, 0), (1, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 5), (6, 5), (7, 6), (8, 6), (9, 7), (9, 8), (10, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 15), (17, 15), (18, 16), (19, 17), (20, 18), (20, 19), (21, 20), (22, 21), (23, 22), (24, 22), (25, 22), (26, 23), (27, 24), (28, 25), (29, 26), (30, 27), (31, 28), (32, 29), (33, 29), (34, 30), (35, 31), (36, 32), (37, 33), (38, 34), (39, 35)])
expect approx_is(S2PolylineAlignment.get_approx_vertex_alignment_with_radius(line_a, line_c, 0), 1.0500416027166277, [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (6, 7), (6, 8), (7, 9), (8, 10), (9, 11), (10, 12), (11, 13), (12, 14), (13, 15), (14, 16), (15, 17), (16, 18), (17, 19), (18, 20), (19, 21), (20, 22), (21, 23), (22, 24), (23, 25), (24, 26), (25, 27), (26, 28), (27, 29), (28, 30), (28, 31), (28, 32), (29, 33), (30, 34), (31, 35), (32, 36), (33, 37), (34, 38), (35, 39), (36, 40), (36, 41), (36, 42), (37, 43), (37, 44), (37, 45), (38, 46), (39, 47)])
expect approx_is(S2PolylineAlignment.get_approx_vertex_alignment_with_radius(line_c, line_a, 2), 0.9508934564467393, [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 6), (8, 7), (9, 8), (10, 9), (11, 10), (12, 11), (13, 12), (14, 13), (15, 14), (16, 14), (17, 15), (18, 16), (19, 17), (20, 18), (21, 19), (22, 20), (23, 21), (24, 22), (25, 23), (26, 24), (27, 25), (28, 25), (29, 26), (30, 27), (31, 28), (32, 29), (33, 30), (34, 31), (35, 32), (36, 33), (37, 34), (38, 35), (39, 36), (40, 36), (41, 37), (42, 38), (43, 39), (44, 39), (45, 39), (46, 39), (47, 39)])
# Short polylines take the exact path.
expect approx_is(S2PolylineAlignment.get_approx_vertex_alignment(line([(1.0, 0.0), (5.0, 0.0), (6.0, 0.0), (9.0, 0.0)]), line([(2.0, 0.0), (7.0, 0.0), (8.0, 0.0)])), 0.08726402586481065, [(0, 0), (1, 1), (2, 1), (3, 2)])
# MedoidPolylineNoPolylines: upstream stops the program.
expect medoid([], Bool.True) == Err(NoPolylines)
# MedoidPolylineOnePolyline, MedoidPolylineTwoPolylines,
# MedoidPolylineFewSmallPolylines (also exact),
# MedoidPolylineOverlappingPolylines and
# MedoidPolylineDifferentLengthPolylines.
expect medoid([line_5], Bool.True) == Ok(0)
expect medoid([line_5, line_1], Bool.True) == Ok(0)
expect medoid([line_5, line_3, line_1], Bool.True) == Ok(1)
expect medoid([line_5, line_3, line_1], Bool.False) == Ok(1)
expect medoid([line_1, line_1], Bool.True) == Ok(0)
expect medoid([line_5, line_3_long, line_1_long], Bool.True) == Ok(1)
# Not from upstream's tests: the medoid of the three long polylines, and an
# empty polyline in the collection.
expect medoid([line_a, line_b, line_c], Bool.True) == Ok(1)
expect medoid([line_a, line_b, line_c], Bool.False) == Ok(1)
expect medoid([line_5, S2Polyline.empty()], Bool.True) == Err(EmptyPolyline)
# The default options are upstream's.
expect S2PolylineAlignment.default_medoid_options() == { approx: Bool.True }
expect S2PolylineAlignment.default_consensus_options() == consensus_options(Bool.True, Bool.False, 5)
# ConsensusPolylineNoPolylines: upstream stops the program.
expect S2PolylineAlignment.get_consensus_polyline([], S2PolylineAlignment.default_consensus_options()) == Err(NoPolylines)
# ConsensusPolylineOnePolyline, ConsensusPolylineTwoPolylines and
# ConsensusPolylineOverlappingPolylines.
expect consensus_is([line_3], S2PolylineAlignment.default_consensus_options(), [S2Point.new(0.998629534754574, 0.0, 0.05233595624294385), S2Point.new(0.9984774386394601, 0.017428488520812167, 0.05233595624294385), S2Point.new(0.9980211966240684, 0.034851668155187324, 0.052335956242943835)])
expect consensus_is([line_3, line_1], S2PolylineAlignment.default_consensus_options(), [S2Point.new(0.9993908270190959, 0.0, 0.03489949670250097), S2Point.new(0.9992386149554826, 0.01744177490283016, 0.03489949670250097), S2Point.new(0.9987820251299122, 0.03487823687206265, 0.03489949670250097)])
expect consensus_is([line_1, line_1], S2PolylineAlignment.default_consensus_options(), [S2Point.new(0.9998476951563913, 0.0, 0.01745240643728351), S2Point.new(0.9996954135095479, 0.017449748351250485, 0.01745240643728351), S2Point.new(0.9992386149554826, 0.03489418134011367, 0.01745240643728351)])
# Not from upstream's tests: polylines of different lengths, exact and
# seeded with the medoid, approximate and seeded with the medoid, with one
# step, and with no step; then the three long polylines.
expect consensus_is([line_5, line_3_long, line_1_long], consensus_options(Bool.False, Bool.True, 5), [S2Point.new(0.9986295347545738, 0.0, 0.05233595624294383), S2Point.new(0.998612577262695, 0.005815671668272905, 0.05233639742860303), S2Point.new(0.9988556669355845, 0.01961765401418452, 0.04361770605669974), S2Point.new(0.9980211966240683, 0.03485166815518732, 0.05233595624294382)])
expect consensus_is([line_5, line_3_long, line_1_long], consensus_options(Bool.True, Bool.True, 5), [S2Point.new(0.9986295347545738, 0.0, 0.05233595624294383), S2Point.new(0.998612577262695, 0.005815671668272905, 0.05233639742860303), S2Point.new(0.9988556669355845, 0.01961765401418452, 0.04361770605669974), S2Point.new(0.9980211966240683, 0.03485166815518732, 0.05233595624294382)])
expect consensus_is([line_5, line_3_long, line_1_long], consensus_options(Bool.True, Bool.False, 1), [S2Point.new(0.9989645038406285, 0.0034891785970899173, 0.045362381982920315), S2Point.new(0.9988556669355845, 0.01961765401418452, 0.04361770605669974), S2Point.new(0.9980211966240683, 0.03485166815518732, 0.05233595624294382)])
expect consensus_is([line_3, line_1], consensus_options(Bool.True, Bool.False, 0), line_3.vertices())
expect consensus_is([line_a, line_b, line_c], consensus_options(Bool.True, Bool.True, 5), [S2Point.new(0.9999998307681431, 0.0, 0.0005817763188763098), S2Point.new(0.9998561591681981, 0.008725595231475555, 0.014543897733251671), S2Point.new(0.9998461301875838, 0.011343606037835827, 0.01338052880014917), S2Point.new(0.9993503275951983, 0.022242070812497686, 0.028358649850468248), S2Point.new(0.9994068947955894, 0.03380859647928259, 0.006545031637724205), S2Point.new(0.9987519745127732, 0.04517926590837052, 0.0212914851247529), S2Point.new(0.9976419272181578, 0.06079736924436077, 0.031847526582212494), S2Point.new(0.9975480195550835, 0.0697550937844657, 0.005672351615612597), S2Point.new(0.9968811517222571, 0.07787272717221226, 0.01279873836236612), S2Point.new(0.9963606590280362, 0.08366661079870708, 0.016289118413077293), S2Point.new(0.9953681196317405, 0.0923376653176439, 0.026759334529466425), S2Point.new(0.9946442377107481, 0.10322511474798324, 0.0052360361028857315), S2Point.new(0.9935651178483422, 0.11232462922620898, 0.014544217552155042), S2Point.new(0.9922486036045681, 0.12095551226385416, 0.02850390671071181), S2Point.new(0.991182031783919, 0.13247207458511603, 0.003054394181798076), S2Point.new(0.9897997955212232, 0.14042986741607322, 0.023996189773559357), S2Point.new(0.988212686331686, 0.1523947550043729, 0.014543906637144192), S2Point.new(0.9862846142495745, 0.16195177605031325, 0.03184779315301314), S2Point.new(0.9846525462093636, 0.17428541161431504, 0.009162889383051289), S2Point.new(0.9834383113056362, 0.18079069073193318, 0.012798984373348653), S2Point.new(0.9815518148693874, 0.189314505889303, 0.0267591589273822), S2Point.new(0.9802121456828006, 0.19794217137076228, 0.0017453506661350468), S2Point.new(0.9778284067283683, 0.2087364397125236, 0.016754275012687104), S2Point.new(0.9751284615745169, 0.22064879589735484, 0.020942595263325075), S2Point.new(0.9728992359827047, 0.22908597786813822, 0.03141164383581991), S2Point.new(0.971110628528131, 0.23852758442871008, 0.006981305486997724), S2Point.new(0.9684047013707454, 0.24864390182615456, 0.01919751149765597), S2Point.new(0.9659508815943925, 0.25701901519617776, 0.029666819421752096), S2Point.new(0.9636622190874443, 0.26702079809870954, 0.007417606500134149), S2Point.new(0.9603936405181437, 0.2783392274398003, 0.013089297938452907), S2Point.new(0.9575623214421897, 0.2875862528250729, 0.019197597252730084), S2Point.new(0.9547720380171676, 0.29585507003688855, 0.029667034803160863), S2Point.new(0.9521807517594751, 0.3054826355934308, 0.005672330178322508), S2Point.new(0.9489149378538294, 0.31504896420541934, 0.017452531935381713), S2Point.new(0.9459047785165031, 0.32324061584112695, 0.02792228948875742), S2Point.new(0.9396772023504798, 0.3420144221548261, 0.005735017077192027)])

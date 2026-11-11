import S1Angle
import S1ChordAngle
import S2Cap
import S1Interval
import S2Cell
import S2CellId
import S2Edge
import S2LatLng
import S2LatLngRect
import Internal/S2Boundary
import Internal/S2Math
import S2Point
import S2Predicates
import Internal/S2Coder

## A sequence of points joined by geodesic edges.
##
## A polyline has no interior, so as a region it contains nothing and only ever
## reports intersection.
S2Polyline := { vertices : List(S2Point) }.{

	## The polyline through the given points, which should be unit length.
	from_points : List(S2Point) -> S2Polyline
	from_points = |vertices| { vertices: vertices }

	## The polyline through the given positions.
	from_lat_lngs : List(S2LatLng) -> S2Polyline
	from_lat_lngs = |points| { vertices: points.map(S2LatLng.to_point) }

	## The polyline with no vertex.
	empty : () -> S2Polyline
	empty = || { vertices: [] }

	## The vertices of the polyline, in order.
	vertices : S2Polyline -> List(S2Point)
	vertices = |line| line.vertices

	## The number of vertices.
	num_vertices : S2Polyline -> U64
	num_vertices = |line| line.vertices.len()

	## The `index`-th vertex, or `OutOfBounds` when there is no such vertex.
	vertex : S2Polyline, U64 -> Try(S2Point, [OutOfBounds])
	vertex = |line, index| line.vertices.get(index)

	## The number of edges, one fewer than the number of vertices.
	num_edges : S2Polyline -> U64
	num_edges = |line| if line.vertices.is_empty() {
		0
	} else {
		line.vertices.len() - 1
	}

	## True when the polyline is well formed: when `find_validation_error`
	## finds nothing.
	is_valid : S2Polyline -> Bool
	is_valid = |line| line.find_validation_error().is_ok()

	## The first reason the polyline is not well formed, if there is one.
	## Upstream's `S2Polyline::FindValidationError`, in its order:
	##
	## - `NotUnitLength(i)`: vertex `i` is not unit length.
	## - `DuplicateVertices(i, j)`: adjacent vertices `i` and `j` are
	##   identical, which makes a degenerate edge.
	## - `AntipodalVertices(i, j)`: adjacent vertices `i` and `j` are
	##   antipodal, which leaves the edge between them undefined.
	find_validation_error : S2Polyline -> Try({}, [NotUnitLength(U64), DuplicateVertices(U64, U64), AntipodalVertices(U64, U64)])
	find_validation_error = |line| {
		n = line.vertices.len()
		var $k = 0
		while $k < n {
			if !at(line, $k).is_unit_length() {
				return Err(NotUnitLength($k))
			}
			$k = $k + 1
		}
		var $i = 1
		while $i < n {
			if at(line, $i - 1) == at(line, $i) {
				return Err(DuplicateVertices($i - 1, $i))
			}
			if at(line, $i - 1) == -at(line, $i) {
				return Err(AntipodalVertices($i - 1, $i))
			}
			$i = $i + 1
		}
		Ok({})
	}

	## The level of the cells whose centres all the vertices are, or
	## `NotSnapped` when there is no such level or no vertex. Upstream's
	## `GetSnapLevel`.
	snap_level : S2Polyline -> Try(U64, [NotSnapped])
	snap_level = |line| S2Boundary.snap_level(line.vertices)

	## The total length of the polyline.
	length : S2Polyline -> S1Angle
	length = |line| {
		var $total = 0.0
		var $i = 1
		while $i < line.vertices.len() {
			previous = line.vertices.get($i - 1) ?? S2Point.zero()
			current = line.vertices.get($i) ?? S2Point.zero()
			$total = $total + previous.angle_to(current).radians()
			$i = $i + 1
		}
		S1Angle.from_radians($total)
	}

	## The centroid of the polyline, scaled by its length so that centroids of
	## several polylines can be summed.
	##
	## Each edge adds upstream's `S2::TrueCentroid(a, b)`: a vector towards
	## the edge's midpoint whose length is twice the sine of half the edge
	## angle. That is the chord length, not the arc length. The result is not
	## a unit vector; normalize it to get a direction.
	centroid : S2Polyline -> S2Point
	centroid = |line| {
		var $sum = S2Point.zero()
		var $i = 1
		while $i < line.vertices.len() {
			previous = line.vertices.get($i - 1) ?? S2Point.zero()
			current = line.vertices.get($i) ?? S2Point.zero()
			$sum = $sum + S2Point.edge_true_centroid(previous, current)
			$i = $i + 1
		}
		$sum
	}

	## The polyline with its vertices in the opposite order.
	reversed : S2Polyline -> S2Polyline
	reversed = |line| { vertices: line.vertices.rev() }

	## The point a fraction `t` of the way along the polyline by arc length.
	## Upstream's `Interpolate`.
	##
	## `t` is clamped to `[0, 1]`. An empty polyline gives the zero vector.
	interpolate : S2Polyline, F64 -> S2Point
	interpolate = |line, t| line.suffix(t).0

	## `interpolate`, together with the index of the next vertex after the
	## point. Upstream's `GetSuffix`.
	##
	## The point followed by the vertices from that index on is the part of
	## the polyline after `t`. The index is between 1 and `num_vertices`, and
	## the point is never equal to the vertex at the index, so that suffix
	## has no repeated vertex. At `t >= 1` the index is `num_vertices`. For
	## the part before `t`, take the vertices before the index and add the
	## point if it differs from the last of them. An empty polyline gives
	## the zero vector and 0.
	suffix : S2Polyline, F64 -> (S2Point, U64)
	suffix = |line, fraction| {
		n = line.vertices.len()
		if n == 0 {
			return (S2Point.zero(), 0)
		}
		if fraction <= 0.0 {
			return (at(line, 0), 1)
		}
		# The case `fraction >= 1` goes through the loop, which has to handle
		# rounding near the end in any case.
		var $target = line.length().times(fraction)
		var $i = 1
		while $i < n {
			a = at(line, $i - 1)
			b = at(line, $i)
			edge_length = a.angle_to(b)
			if $target < edge_length {
				result = S2Edge.point_on_line(a, b, $target)
				return (result, if (result == b) $i + 1 else $i)
			}
			$target = $target - edge_length
			$i = $i + 1
		}
		(at(line, n - 1), n)
	}

	## The fraction of the polyline's length from its start to `point`, the
	## inverse of `suffix`. Upstream's `UnInterpolate`.
	##
	## `next_vertex` is the index of the vertex after `point`, as `suffix`
	## and `project` return it, and is clamped to `[1, num_vertices]`. The
	## result is at most 1, and can exceed the fraction of a point that is
	## not exactly on the polyline. A polyline with fewer than two vertices
	## gives 0.
	un_interpolate : S2Polyline, S2Point, U64 -> F64
	un_interpolate = |line, point, next_vertex| {
		n = line.vertices.len()
		if n < 2 {
			return 0.0
		}
		next = next_vertex.max(1).min(n)
		var $sum = S1Angle.zero()
		var $i = 1
		while $i < next {
			$sum = $sum + at(line, $i - 1).angle_to(at(line, $i))
			$i = $i + 1
		}
		to_point = $sum + at(line, next - 1).angle_to(point)
		while $i < n {
			$sum = $sum + at(line, $i - 1).angle_to(at(line, $i))
			$i = $i + 1
		}
		(to_point.radians() / $sum.radians()).min(1.0)
	}

	## The point of the polyline closest to `p`, with the index of the vertex
	## after it. Upstream's `Project`.
	##
	## The index means what it means for `suffix`, but for the projected
	## point: it is the end of the nearest edge, or one more when the point
	## is that end vertex. The first nearest edge wins a tie. A polyline with
	## one vertex gives that vertex and 1, and an empty one the zero vector
	## and 0.
	project : S2Polyline, S2Point -> (S2Point, U64)
	project = |line, p| {
		n = line.vertices.len()
		if n == 0 {
			return (S2Point.zero(), 0)
		}
		if n == 1 {
			return (at(line, 0), 1)
		}
		var $min_distance = S1Angle.from_radians(10.0)
		var $min_index = 1
		var $i = 1
		while $i < n {
			distance = S2Edge.distance_to_edge(p, at(line, $i - 1), at(line, $i)).to_angle()
			if distance < $min_distance {
				$min_distance = distance
				$min_index = $i
			}
			$i = $i + 1
		}
		closest = S2Edge.project(p, at(line, $min_index - 1), at(line, $min_index))
		(closest, if (closest == at(line, $min_index)) $min_index + 1 else $min_index)
	}

	## The distance from `p` to the closest point of the polyline, the one
	## `project` finds.
	distance_to_point : S2Polyline, S2Point -> S1ChordAngle
	distance_to_point = |line, p| {
		(closest, _next) = line.project(p)
		S1ChordAngle.from_points(p, closest)
	}

	## True when `point` is on the right of the polyline. Upstream's
	## `IsOnRight`.
	##
	## The side is decided locally, by the edge nearest to the point. When
	## the nearest point of the polyline is an interior vertex, the point is
	## on the right when the previous vertex, the point and the next vertex
	## turn counterclockwise around that vertex. A vertex of the polyline is
	## not on its right. The polyline must have at least two vertices.
	is_on_right : S2Polyline, S2Point -> Bool
	is_on_right = |line, point| {
		n = line.vertices.len()
		(closest, next) = line.project(point)
		if closest == at(line, next - 1) and next > 1 and next < n {
			if point == at(line, next - 1) {
				return Bool.False
			}
			return S2Predicates.ordered_ccw(at(line, next - 2), point, at(line, next), at(line, next - 1))
		}
		edge_end = if (next == n) next - 1 else next
		S2Predicates.sign(point, at(line, edge_end), at(line, edge_end - 1)) > 0
	}

	## The indices of a subsequence of the vertices such that the polyline
	## through them is never further than `tolerance` from this one.
	## Upstream's `SubsampleVertices`.
	##
	## The first and last vertices are kept when they differ. The result is
	## a valid polyline: adjacent kept vertices are never identical or
	## antipodal. The simplification is parametric, so a polyline that
	## doubles back keeps the doubling back, to within the tolerance. It runs
	## in linear time and is not optimal. A negative tolerance counts as
	## zero.
	subsample_vertices : S2Polyline, S1Angle -> List(U64)
	subsample_vertices = |line, tolerance| {
		n = line.vertices.len()
		if n == 0 {
			return []
		}
		clamped = tolerance.max(S1Angle.zero())
		var $indices = [0]
		var $index = 0
		while $index + 1 < n {
			next_index = find_end_vertex(line, clamped, $index)
			if at(line, next_index) != at(line, $index) {
				$indices = $indices.append(next_index)
			}
			$index = next_index
		}
		$indices
	}

	## True when `covered` stays within `max_error` of a contiguous part of
	## this polyline along its whole length. Upstream's `NearlyCovers`.
	##
	## Picture one car driving along `covered` and another along some part
	## of this polyline, neither going backwards: the answer is true when
	## they can always stay within `max_error` of each other. Any polyline
	## covers the empty polyline, and the empty polyline covers no other.
	## Repeated vertices are allowed.
	##
	## The search visits pairs of positions, one on each polyline, and
	## remembers the ones it has seen, so the cost is about the product of
	## the vertex counts at worst.
	nearly_covers : S2Polyline, S2Polyline, S1Angle -> Bool
	nearly_covers = |line, covered, max_error| {
		n = line.vertices.len()
		m = covered.vertices.len()
		if m == 0 {
			return Bool.True
		}
		if n == 0 {
			return Bool.False
		}
		start = at(covered, 0)
		key = |state| (state.i * (m + 1) + state.j) * 2 + (if (state.in_progress) 1 else 0)

		# Every edge of this polyline near the start of `covered` is a place
		# to begin. The end of each edge is skipped, except for the last edge,
		# so that no start is found twice.
		var $pending = []
		var $i = 0
		var $next_i = next_distinct_vertex(line, 0)
		while $next_i < n {
			next_next_i = next_distinct_vertex(line, $next_i)
			closest = S2Edge.project(start, at(line, $i), at(line, $next_i))
			if (next_next_i == n or closest != at(line, $next_i)) and closest.angle_to(start) <= max_error {
				$pending = $pending.append({ i: $i, j: 0, in_progress: Bool.True })
			}
			$i = $next_i
			$next_i = next_next_i
		}

		var $done = Set.empty()
		while !$pending.is_empty() {
			state = $pending.last() ?? { i: 0, j: 0, in_progress: Bool.True }
			$pending = $pending.drop_last(1)
			if !$done.contains(key(state)) {
				$done = $done.insert(key(state))
				next_i = next_distinct_vertex(line, state.i)
				next_j = next_distinct_vertex(covered, state.j)
				if next_j == m {
					return Bool.True
				}
				if next_i < n {
					(i_begin, j_begin) =
						if state.in_progress {
							(S2Edge.project(at(covered, state.j), at(line, state.i), at(line, next_i)), at(covered, state.j))
						} else {
							(at(line, state.i), S2Edge.project(at(line, state.i), at(covered, state.j), at(covered, next_j)))
						}
					if S2Edge.is_edge_b_near_edge_a(j_begin, at(covered, next_j), i_begin, at(line, next_i), max_error) {
						$pending = $pending.append({ i: next_i, j: state.j, in_progress: Bool.False })
					}
					if S2Edge.is_edge_b_near_edge_a(i_begin, at(line, next_i), j_begin, at(covered, next_j), max_error) {
						$pending = $pending.append({ i: state.i, j: next_j, in_progress: Bool.True })
					}
				}
			}
		}
		Bool.False
	}

	## True when any edge of this polyline crosses or touches any edge of the
	## other.
	##
	## Polylines that share a vertex, or where an endpoint of one lies on the
	## other, intersect.
	intersects_polyline : S2Polyline, S2Polyline -> Bool
	intersects_polyline = |line, other| {
		if line.vertices.is_empty() or other.vertices.is_empty() {
			return Bool.False
		}
		if !line.rect_bound().intersects_rect(other.rect_bound()) {
			return Bool.False
		}
		var $hit = Bool.False
		var $i = 1
		while $i < line.vertices.len() {
			a = line.vertices.get($i - 1) ?? S2Point.zero()
			b = line.vertices.get($i) ?? S2Point.zero()
			var $j = 1
			while $j < other.vertices.len() {
				c = other.vertices.get($j - 1) ?? S2Point.zero()
				d = other.vertices.get($j) ?? S2Point.zero()
				if S2Edge.crossing_sign(a, b, c, d) >= 0 {
					$hit = Bool.True
				}
				$j = $j + 1
			}
			$i = $i + 1
		}
		$hit
	}

	## The bounding rectangle of the polyline, valid for its edges as well as
	## its vertices.
	##
	## A geodesic edge bulges polewards of its endpoints, so the rectangle
	## includes the highest and lowest latitude each edge reaches.
	rect_bound : S2Polyline -> S2LatLngRect
	rect_bound = |line| S2Boundary.chain_bound(line.vertices)

	## The bounding cap of the polyline: the cap around its rectangle bound,
	## as upstream computes it.
	cap_bound : S2Polyline -> S2Cap
	cap_bound = |line| line.rect_bound().cap_bound()

	## A few cells that cover the polyline: those of its bounding cap, as
	## upstream's `S2Polyline::GetCellUnionBound` gives them.
	cell_union_bound : S2Polyline -> List(S2CellId)
	cell_union_bound = |line| line.cap_bound().cell_union_bound()

	## Always false: a polyline has no area, so it contains no point.
	## Upstream's `S2Polyline::Contains(const S2Point&)` does the same.
	contains_point : S2Polyline, S2Point -> Bool
	contains_point = |_line, _p| Bool.False

	## Always false: a polyline has no interior, so it contains no cell.
	contains_cell : S2Polyline, S2Cell -> Bool
	contains_cell = |_line, _cell| Bool.False

	## True when the polyline touches the cell.
	may_intersect_cell : S2Polyline, S2Cell -> Bool
	may_intersect_cell = |line, cell| {
		var $hit = Bool.False
		for v in line.vertices {
			if cell.contains_point(v) {
				$hit = Bool.True
			}
		}
		if $hit {
			return Bool.True
		}
		var $i = 1
		while $i < line.vertices.len() {
			a = line.vertices.get($i - 1) ?? S2Point.zero()
			b = line.vertices.get($i) ?? S2Point.zero()
			var $k = 0
			while $k < 4 {
				if S2Edge.crossing_sign(a, b, cell.vertex($k), cell.vertex(($k + 1) % 4)) >= 0 {
					$hit = Bool.True
				}
				$k = $k + 1
			}
			$i = $i + 1
		}
		$hit
	}

	## True when the two polylines have the same number of vertices and each
	## pair is within `max_error` radians.
	approx_eq : S2Polyline, S2Polyline, F64 -> Bool
	approx_eq = |line, other, max_error| {
		if line.vertices.len() != other.vertices.len() {
			return Bool.False
		}
		var $ok = Bool.True
		var $i = 0
		while $i < line.vertices.len() {
			a = line.vertices.get($i) ?? S2Point.zero()
			b = other.vertices.get($i) ?? S2Point.zero()
			if !a.approx_eq(b, max_error) {
				$ok = Bool.False
			}
			$i = $i + 1
		}
		$ok
	}

	is_eq : S2Polyline, S2Polyline -> Bool
	is_eq = |a, b| a.vertices == b.vertices

	to_inspect : S2Polyline -> Str
	to_inspect = |line| "S2Polyline(${line.vertices.len().to_str()} vertices)"

	## The bytes that upstream's `S2Polyline::EncodeUncompressed` writes: the
	## version byte 1, the number of vertices as a little-endian 32-bit
	## integer, and the vertices as three little-endian IEEE 754 doubles each.
	## This is the lossless format. `EncodeMostCompact` is not ported.
	encode : S2Polyline -> List(U8)
	encode = |line|
		line.vertices.fold(
			[1] |> S2Coder.put_u32(line.vertices.len()),
			|out, p| out.concat(p.encode()),
		)

	## The polyline that `encode` writes. Bytes after the vertices are
	## ignored. The polyline is not checked, so `is_valid` tells whether it is
	## well formed.
	##
	## The version byte 2 is upstream's compressed format, which this port does
	## not read: that is `UnsupportedCompressedEncoding`. Any other version
	## byte than 1 is `UnsupportedVersion`.
	decode : List(U8) -> Try(S2Polyline, [Truncated, UnsupportedVersion(U8), UnsupportedCompressedEncoding])
	decode = |bytes| {
		version = S2Coder.get_u8(bytes, 0)?
		if version == 2 {
			return Err(UnsupportedCompressedEncoding)
		}
		if version != 1 {
			return Err(UnsupportedVersion(version))
		}
		count = S2Coder.get_u32(bytes, 1)?
		var $vertices = []
		for i in 0..<count {
			$vertices = $vertices.append(S2Point.decode(bytes.drop_first(5 + i * 24))?)
		}
		Ok({ vertices: $vertices })
	}
}

## The `index`-th vertex, or the zero vector when there is none.
at : S2Polyline, U64 -> S2Point
at = |line, index| line.vertices.get(index) ?? S2Point.zero()

## The first index after `index` whose vertex differs from the vertex at
## `index`, or the vertex count when there is none. Upstream's
## `NextDistinctVertex`.
next_distinct_vertex : S2Polyline, U64 -> U64
next_distinct_vertex = |line, index| {
	initial = at(line, index)
	var $k = index + 1
	while $k < line.vertices.len() and at(line, $k) == initial {
		$k = $k + 1
	}
	$k
}

## Upstream's `FindEndVertex`: the last index such that the edge from vertex
## `index` to it passes within `tolerance` of every vertex between them, in
## order.
##
## The rays from the start vertex that pass within `tolerance` of every
## vertex so far form a wedge, kept as an interval of angles in the tangent
## plane. Each vertex narrows the wedge. The walk stops at the first vertex
## outside the wedge, at one that goes backwards along the ray beyond the
## tolerance, and at an edge longer than 90 degrees that is not the first.
find_end_vertex : S2Polyline, S1Angle, U64 -> U64
find_end_vertex = |line, tolerance, start| {
	origin = at(line, start)
	frame = origin.frame()
	var $wedge = S1Interval.full()
	var $last_distance = 0.0
	var $index = start + 1
	var $stopped = Bool.False
	while !$stopped and $index < line.vertices.len() {
		candidate = at(line, $index)
		distance = origin.angle_to(candidate).radians()
		if (distance > F64.pi / 2.0 and $last_distance > 0.0)
			or (distance < $last_distance and $last_distance > tolerance.radians()) {
			$stopped = Bool.True
		} else {
			$last_distance = distance
			# Vertices within the tolerance of the start do not constrain
			# the direction of the ray.
			if distance > tolerance.radians() {
				direction = S2Point.to_frame(frame, candidate)
				center = S2Math.atan2(direction.y(), direction.x())
				if !$wedge.contains_point(center) {
					$stopped = Bool.True
				} else {
					half_angle = F64.asin(tolerance.radians().sin() / distance.sin())
					$wedge = $wedge.intersection(S1Interval.from_point(center).expanded(half_angle))
				}
			}
			if !$stopped {
				$index = $index + 1
			}
		}
	}
	$index - 1
}

expect S2Polyline.empty().num_vertices() == 0
expect S2Polyline.empty().num_edges() == 0
expect S2Polyline.empty().length().radians() == 0.0
expect S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0)]).num_edges() == 0
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	line.num_vertices() == 2 and line.num_edges() == 1 and (line.length().degrees() - 90.0).abs() < 1e-13
}
expect {
	line = S2Polyline.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 45.0),
		S2LatLng.from_degrees(0.0, 90.0),
	])
	(line.length().degrees() - 90.0).abs() < 1e-13
}
expect S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(10.0, 10.0)]).is_valid()
expect !S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)]).is_valid()
expect !S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0)]).is_valid()
expect !S2Polyline.from_points([S2Point.new(2.0, 0.0, 0.0)]).is_valid()
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	line.reversed().vertices() == line.vertices().rev()
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	mid = line.interpolate(0.5)
	S2LatLng.from_point(mid).approx_eq(S2LatLng.from_degrees(0.0, 45.0), 1e-13)
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	line.interpolate(0.0) == (line.vertex(0) ?? S2Point.zero())
		and line.interpolate(1.0) == (line.vertex(1) ?? S2Point.zero())
		and line.interpolate(-5.0) == (line.vertex(0) ?? S2Point.zero())
		and line.interpolate(5.0) == (line.vertex(1) ?? S2Point.zero())
}
expect {
	# Interpolation on a three-vertex polyline crosses into the second edge.
	line = S2Polyline.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 10.0),
		S2LatLng.from_degrees(0.0, 40.0),
	])
	(point, next_vertex) = line.suffix(0.5)
	next_vertex == 2 and S2LatLng.from_point(point).approx_eq(S2LatLng.from_degrees(0.0, 20.0), 1e-13)
}
expect {
	line = S2Polyline.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 10.0),
		S2LatLng.from_degrees(0.0, 40.0),
	])
	(point, next_vertex) = line.suffix(0.3)
	(line.un_interpolate(point, next_vertex) - 0.3).abs() < 1e-13
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	(closest, next_vertex) = line.project(S2LatLng.from_degrees(10.0, 45.0).to_point())
	next_vertex == 1 and S2LatLng.from_point(closest).approx_eq(S2LatLng.from_degrees(0.0, 45.0), 1e-13)
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	d = line.distance_to_point(S2LatLng.from_degrees(10.0, 45.0).to_point())
	(d.degrees() - 10.0).abs() < 1e-12
}
expect {
	a = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(-10.0, 0.0), S2LatLng.from_degrees(10.0, 0.0)])
	b = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, -10.0), S2LatLng.from_degrees(0.0, 10.0)])
	a.intersects_polyline(b) and b.intersects_polyline(a)
}
expect {
	a = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(-10.0, 0.0), S2LatLng.from_degrees(10.0, 0.0)])
	b = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(20.0, -10.0), S2LatLng.from_degrees(20.0, 10.0)])
	!a.intersects_polyline(b)
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(10.0, 10.0)])
	rect = line.rect_bound()
	cap = line.cap_bound()
	rect.contains_point(line.vertex(0) ?? S2Point.zero())
		and rect.contains_point(line.vertex(1) ?? S2Point.zero())
		and cap.contains_point(line.vertex(1) ?? S2Point.zero())
}
expect S2Polyline.empty().rect_bound().is_empty()
expect S2Polyline.empty().cap_bound().is_empty()
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0)])
	!line.contains_cell(S2Cell.from_face(0)) and line.may_intersect_cell(S2Cell.from_face(0))
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0)])
	!line.may_intersect_cell(S2Cell.from_face(3))
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	c = line.centroid()
	# A 90-degree edge adds a vector of length 2 sin(45 degrees), so its
	# squared length is 2.
	(c.norm2() - 2.0).abs() < 1e-13
		and S2LatLng.from_point(c).approx_eq(S2LatLng.from_degrees(0.0, 45.0), 1e-13)
}
expect {
	a = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0)])
	a.approx_eq(a, 1e-15) and !a.approx_eq(S2Polyline.empty(), 1e-15)
}
expect {
	# Polylines that only share a vertex, or where one ends on the other,
	# still intersect.
	a = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0)])
	b = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0)])
	c = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(-10.0, -10.0)])
	a.intersects_polyline(b) and b.intersects_polyline(a) and a.intersects_polyline(c)
		and !b.intersects_polyline(c)
		and !a.intersects_polyline(S2Polyline.empty())
}
expect {
	# An edge along the 10th parallel bulges north of it between its ends.
	# The bounds must hold the edge's midpoint, not only its vertices.
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(10.0, -20.0), S2LatLng.from_degrees(10.0, 20.0)])
	mid = line.interpolate(0.5)
	line.rect_bound().contains_point(mid)
		and line.rect_bound().lat_hi().degrees() > 10.5
		and line.cap_bound().contains_point(mid)
}

# Upstream's S2Polyline.Interpolate and UnInterpolate. Each suffix point and
# next vertex is from upstream's GetSuffix, and each fraction from its
# UnInterpolate of that point, through tools/s2_oracle.cc.
expect {
	line = S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 1.0).normalize(), S2Point.new(0.0, 0.0, 1.0)])
	check = |fraction, expected_point, expected_next| {
		(p, next_vertex) = line.suffix(fraction)
		p.approx_eq(expected_point, 1e-15) and next_vertex == expected_next and line.interpolate(fraction) == p
	}
	check(-0.1, S2Point.new(1.0, 0.0, 0.0), 1)
		and check(0.1, S2Point.new(0.95105651629515375, 0.30901699437494745, 0.0), 1)
		and check(0.25, S2Point.new(0.70710678118654757, 0.70710678118654746, 0.0), 1)
		and check(0.5, S2Point.new(0.0, 1.0, 0.0), 2)
		and check(0.75, S2Point.new(0.0, 0.70710678118654757, 0.70710678118654757), 3)
		and check(1.1, S2Point.new(0.0, 0.0, 1.0), 4)
}
expect {
	line = S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 1.0).normalize(), S2Point.new(0.0, 0.0, 1.0)])
	round_trip = |fraction, expected| {
		(p, next_vertex) = line.suffix(fraction)
		(line.un_interpolate(p, next_vertex) - expected).abs() <= 1e-15
	}
	round_trip(-0.1, 0.0)
		and round_trip(0.1, 0.10000000000000001)
		and round_trip(0.25, 0.25)
		and round_trip(0.5, 0.5)
		and round_trip(0.75, 0.75)
		and round_trip(1.1, 1.0)
		and line.un_interpolate(S2Point.new(0.0, 1.0, 0.0), 4) == 1.0
		and S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0)]).un_interpolate(S2Point.new(0.0, 1.0, 0.0), 1) == 0.0
}
# Upstream's Interpolate test: a fraction so close to 1 that the point is the
# last vertex gives next vertex 3.
expect {
	line = S2Polyline.from_points([S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 1.0 + 1e-15).normalize(), S2Point.new(1.0, 1.0, 1.0 + 2e-15).normalize()])
	line.suffix(1.0 - 2e-16) == (S2Point.new(1.0, 1.0, 1.0 + 2e-15).normalize(), 3)
}
# Upstream's S2Polyline.Project, the points and next vertices from upstream.
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(1.0, 2.0)])
	single = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(1.0, 1.0)])
	check = |l, lat, lng, expected_point, expected_next| {
		(p, next_vertex) = l.project(S2LatLng.from_degrees(lat, lng).to_point())
		p.approx_eq(expected_point, 1e-15) and next_vertex == expected_next
	}
	check(line, 0.5, -0.5, S2Point.new(1.0, 0.0, 0.0), 1)
		and check(line, 0.5, 0.5, S2Point.new(0.9999619230641712, 0.0087265354983739347, 0.0), 1)
		and check(line, 0.5, 1.0, S2Point.new(0.99984769515639127, 0.017452406437283512, 0.0), 2)
		and check(line, -0.5, 2.5, S2Point.new(0.99939082701909576, 0.034899496702500969, 0.0), 3)
		and check(line, 2.0, 2.0, S2Point.new(0.99923861495548261, 0.03489418134011367, 0.017452406437283512), 4)
		and check(single, 2.0, 2.0, S2Point.new(0.99969541350954794, 0.017449748351250485, 0.017452406437283512), 1)
		and check(single, -1.0, 0.0, S2Point.new(0.99969541350954794, 0.017449748351250485, 0.017452406437283512), 1)
}
# Upstream's S2Polyline.IsOnRight. The answers are upstream's, and the oracle
# agrees with them.
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(1.0, 2.0)])
	line2 = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(-1.0, 0.0)])
	right = |l, lat, lng| l.is_on_right(S2LatLng.from_degrees(lat, lng).to_point())
	right(line, -0.5, 0.5)
		and !right(line, 0.5, -0.5)
		and !right(line, 0.5, 0.5)
		and !right(line, 0.5, 1.0)
		and right(line, -0.5, 2.5)
		and right(line, 1.5, 2.5)
		and !right(line2, -0.5, 5.0)
		and !right(line2, 5.5, 5.0)
}
# Upstream's SubsampleVerticesTrivialInputs, SubsampleVerticesSimpleExample and
# SubsampleVerticesGuarantees, with upstream's expected indices.
expect {
	sub = |points, degrees| S2Polyline.from_lat_lngs(points).subsample_vertices(S1Angle.from_degrees(degrees))
	sub([], 1.0) == []
		and sub([S2LatLng.from_degrees(0.0, 1.0)], 1.0) == [0]
		and sub([S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(11.0, 11.0)], 5.0) == [0, 1]
		and sub([S2LatLng.from_degrees(-1.0, 0.0), S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.0, 0.0)], 1e-15) == [0, 2]
		and sub([S2LatLng.from_degrees(-1.0, 0.0), S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.0, 1.0)], 0.0) == [0, 1, 2]
		and sub([S2LatLng.from_degrees(-1.0, 0.0), S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.0, 1.0)], -1.0) == [0, 1, 2]
		and sub([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(0.0, 5.0)], 1.0) == [0, 4]
		and sub([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0)], 0.0) == [0, 3]
		and sub([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(-1.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.5), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(3.5, 4.0), S2LatLng.from_degrees(4.0, 4.0)], 3.0) == [0, 9]
		and sub([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(-1.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.5), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(3.5, 4.0), S2LatLng.from_degrees(4.0, 4.0)], 2.0) == [0, 6, 9]
		and sub([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(-1.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.5), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(3.5, 4.0), S2LatLng.from_degrees(4.0, 4.0)], 0.9) == [0, 2, 6, 9]
		and sub([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(-1.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.5), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(3.5, 4.0), S2LatLng.from_degrees(4.0, 4.0)], 0.4) == [0, 1, 2, 3, 4, 6, 9]
		and sub([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(-1.0, 2.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(1.0, 4.0), S2LatLng.from_degrees(2.0, 4.5), S2LatLng.from_degrees(3.0, 4.0), S2LatLng.from_degrees(3.5, 4.0), S2LatLng.from_degrees(4.0, 4.0)], 0.0) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
		and sub([S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(12.0, 12.0), S2LatLng.from_degrees(10.0, 10.0)], 5.0) == [0]
		and sub([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 120.0), S2LatLng.from_degrees(0.0, 130.0)], 5.0) == [0, 3, 4]
		and sub([S2LatLng.from_degrees(90.0, 0.0), S2LatLng.from_degrees(50.0, 180.0), S2LatLng.from_degrees(20.0, 180.0), S2LatLng.from_degrees(-20.0, 180.0), S2LatLng.from_degrees(-50.0, 180.0), S2LatLng.from_degrees(-90.0, 0.0), S2LatLng.from_degrees(30.0, 0.0), S2LatLng.from_degrees(90.0, 0.0)], 5.0) == [0, 2, 4, 5, 6, 7]
		and sub([S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 20.0), S2LatLng.from_degrees(10.0, 30.0), S2LatLng.from_degrees(10.0, 15.0), S2LatLng.from_degrees(10.0, 40.0)], 5.0) == [0, 2, 3, 4]
		and sub([S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 20.0), S2LatLng.from_degrees(10.0, 30.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 30.0), S2LatLng.from_degrees(10.0, 40.0)], 5.0) == [0, 2, 3, 5]
		and sub([S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(12.0, 12.0), S2LatLng.from_degrees(9.0, 9.0), S2LatLng.from_degrees(10.0, 20.0), S2LatLng.from_degrees(10.0, 30.0)], 5.0) == [0, 4]
}
# Upstream's S2PolylineCoveringTest cases, with upstream's answers: for each
# pair (a, b), whether b covers a and whether a covers b.
expect {
	covers = |a, b, degrees| {
		la = S2Polyline.from_lat_lngs(a)
		lb = S2Polyline.from_lat_lngs(b)
		(lb.nearly_covers(la, S1Angle.from_degrees(degrees)), la.nearly_covers(lb, S1Angle.from_degrees(degrees)))
	}
	covers([S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(-1.0, 10.0)], [S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(-1.0, 10.0)], 1e-10) == (Bool.True, Bool.True)
		and covers([S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(-1.0, 10.0)], [S2LatLng.from_degrees(-1.0, 10.0), S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(1.0, 1.0)], 1e-10) == (Bool.False, Bool.False)
		and covers([S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(2.0, 1.0)], [S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(1.5, 1.0), S2LatLng.from_degrees(2.0, 1.0)], 1e-10) == (Bool.True, Bool.True)
		and covers([S2LatLng.from_degrees(-5.0, 1.0), S2LatLng.from_degrees(10.0, 1.0), S2LatLng.from_degrees(10.0, 5.0), S2LatLng.from_degrees(5.0, 10.0)], [S2LatLng.from_degrees(9.0, 1.0), S2LatLng.from_degrees(9.9995, 1.0), S2LatLng.from_degrees(10.0005, 5.0)], 0.001) == (Bool.False, Bool.True)
		and covers([S2LatLng.from_degrees(-5.0, 1.0), S2LatLng.from_degrees(10.0, 1.0)], [S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(20.0, 1.0)], 1.0) == (Bool.False, Bool.False)
		and covers([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(0.0, 5.0)], [S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 5.0)], 1.5) == (Bool.True, Bool.True)
		and covers([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(0.0, 5.0)], [S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 4.0), S2LatLng.from_degrees(0.0, 3.0), S2LatLng.from_degrees(0.0, 5.0)], 0.5) == (Bool.False, Bool.False)
		and covers([S2LatLng.from_degrees(5.0, 1.0), S2LatLng.from_degrees(-5.0, 1.0)], [S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(3.0, 1.0)], 1.0) == (Bool.False, Bool.False)
		and covers([S2LatLng.from_degrees(5.0, 1.0), S2LatLng.from_degrees(-5.0, 1.0)], [S2LatLng.from_degrees(1.0, 1.0), S2LatLng.from_degrees(3.0, 1.0)], 2.5) == (Bool.False, Bool.True)
		and covers([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 3.0)], [S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 3.0)], 1e-10) == (Bool.True, Bool.True)
		and covers([S2LatLng.from_degrees(0.0, 11.0), S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 9.0), S2LatLng.from_degrees(0.0, 20.0)], [S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(0.0, 15.0)], 1.5) == (Bool.False, Bool.True)
		and covers([S2LatLng.from_degrees(40.0, 1.0), S2LatLng.from_degrees(20.0, 1.0)], [S2LatLng.from_degrees(39.9, 0.9), S2LatLng.from_degrees(40.0, 1.1), S2LatLng.from_degrees(30.0, 1.15), S2LatLng.from_degrees(29.0, 0.95), S2LatLng.from_degrees(28.0, 1.1), S2LatLng.from_degrees(27.0, 1.15), S2LatLng.from_degrees(26.0, 1.05), S2LatLng.from_degrees(25.0, 0.85), S2LatLng.from_degrees(24.0, 1.1), S2LatLng.from_degrees(23.0, 0.9), S2LatLng.from_degrees(20.0, 0.99)], 0.2) == (Bool.True, Bool.True)
		and covers([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0)], [S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 3.0)], 1.5) == (Bool.False, Bool.True)
		and covers([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 2.0)], [S2LatLng.from_degrees(0.0, 2.0), S2LatLng.from_degrees(0.0, 3.0)], 1.5) == (Bool.False, Bool.True)
		and covers([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 2.0)], [], 0.0) == (Bool.False, Bool.True)
		and covers([], [], 0.0) == (Bool.True, Bool.True)
}
# Upstream's FindValidationError messages, through tools/s2_oracle.cc:
# 2 Vertices 0 and 1 are identical.
# 3 Vertices 0 and 1 are antipodal.
# 1 Vertex 0 is not unit length.
# 2 Vertices 1 and 2 are identical.
# ok.
expect S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)]).find_validation_error() == Err(DuplicateVertices(0, 1))
expect S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 0.0, 0.0)]).find_validation_error() == Err(AntipodalVertices(0, 1))
expect S2Polyline.from_points([S2Point.new(2.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)]).find_validation_error() == Err(NotUnitLength(0))
expect S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 1.0, 0.0)]).find_validation_error() == Err(DuplicateVertices(1, 2))
expect S2Polyline.empty().find_validation_error() == Ok({})
# Upstream's S2Polyline.GetSnapLevel.
expect {
	center = |lat, lng, level| S2CellId.from_lat_lng(S2LatLng.from_degrees(lat, lng)).parent_at_level(level).to_point()
	S2Polyline.from_points([center(10.0, 10.0, 20), center(20.0, 20.0, 20)]).snap_level() == Ok(20)
		and S2Polyline.from_points([center(10.0, 10.0, 20), center(20.0, 20.0, 22)]).snap_level() == Err(NotSnapped)
		and S2Polyline.from_lat_lngs([S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(20.0, 20.0)]).snap_level() == Err(NotSnapped)
		and S2Polyline.empty().snap_level() == Err(NotSnapped)
}
# GetCellUnionBound, from upstream.
expect S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 20.0)]).cell_union_bound() == [1441151880758558720, 864691128455135232, 2017612633061982208, 288230376151711744].map(S2CellId.from_id)

# A polyline has no area, so it contains no point, not even a vertex.
expect {
	line = S2Polyline.from_points([S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()])
	!line.contains_point(S2LatLng.from_degrees(0.0, 0.0).to_point()) and !line.contains_point(S2LatLng.from_degrees(0.0, 5.0).to_point())
}

# S2Polyline encoding against upstream's `Encode`, and decoding it back.
expect S2Coder.to_hex(S2Polyline.empty().encode()) == "0100000000"
expect S2Polyline.decode(S2Coder.from_hex("0100000000")) == Ok(S2Polyline.empty())
expect S2Coder.to_hex(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0)]).encode()) == "0101000000000000000000f03f00000000000000000000000000000000"
expect S2Polyline.decode(S2Coder.from_hex("0101000000000000000000f03f00000000000000000000000000000000")) == Ok(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0)]))
expect S2Coder.to_hex(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]).encode()) == "0103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f"
expect S2Polyline.decode(S2Coder.from_hex("0103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f")) == Ok(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]))

# The compressed format is not read, and any other version is not known.
expect S2Polyline.decode(S2Coder.from_hex("021e0000")) == Err(UnsupportedCompressedEncoding)
expect S2Polyline.decode(S2Coder.from_hex("0203000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f")) == Err(UnsupportedCompressedEncoding)
expect S2Polyline.decode(S2Coder.from_hex("0303000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f")) == Err(UnsupportedVersion(3))
expect S2Polyline.decode(S2Coder.from_hex("0003000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f")) == Err(UnsupportedVersion(0))
expect S2Polyline.decode([]) == Err(Truncated)
expect S2Polyline.decode(S2Coder.from_hex("0103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f0")) == Err(Truncated)
expect S2Polyline.decode(S2Coder.from_hex("01ffffffff")) == Err(Truncated)
expect S2Polyline.decode(S2Coder.from_hex("0103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03fff")) == S2Polyline.decode(S2Coder.from_hex("0103000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f"))

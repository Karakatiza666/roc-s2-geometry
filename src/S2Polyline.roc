import S1Angle
import S1ChordAngle
import S2Cap
import S2Cell
import S2Edge
import S2LatLng
import S2LatLngRect
import Internal/S2Boundary
import S2Point

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

	## True when every vertex is unit length and no two adjacent vertices are
	## identical or antipodal.
	##
	## Adjacent identical vertices make a degenerate edge, and antipodal ones
	## leave the edge between them undefined, since there is no shorter arc.
	is_valid : S2Polyline -> Bool
	is_valid = |line| {
		var $ok = Bool.True
		for v in line.vertices {
			if !v.is_unit_length() {
				$ok = Bool.False
			}
		}
		var $i = 1
		while $i < line.vertices.len() {
			previous = line.vertices.get($i - 1) ?? S2Point.zero()
			current = line.vertices.get($i) ?? S2Point.zero()
			if previous.dot(current) <= -1.0 {
				$ok = Bool.False
			}
			if previous == current {
				$ok = Bool.False
			}
			$i = $i + 1
		}
		$ok
	}

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
			# |a - b| is 2 sin(theta) and |a + b| is 2 cos(theta), where theta
			# is half the edge angle, so this scales a + b to length
			# 2 sin(theta). An antipodal edge has no midpoint and adds nothing.
			sum = previous + current
			cos2 = sum.norm2()
			if cos2 != 0.0 {
				sin2 = (previous - current).norm2()
				$sum = $sum + sum * (sin2 / cos2).sqrt()
			}
			$i = $i + 1
		}
		$sum
	}

	## The polyline with its vertices in the opposite order.
	reversed : S2Polyline -> S2Polyline
	reversed = |line| { vertices: line.vertices.rev() }

	## The point a fraction `t` of the way along the polyline by arc length.
	##
	## `t` is clamped to `[0, 1]`. An empty polyline gives the zero vector.
	interpolate : S2Polyline, F64 -> S2Point
	interpolate = |line, t| line.interpolate_with_edge(t).0

	## `interpolate` together with the index of the edge the point lies on,
	## which lets a caller split the polyline there.
	interpolate_with_edge : S2Polyline, F64 -> (S2Point, U64)
	interpolate_with_edge = |line, t| {
		if line.vertices.is_empty() {
			return (S2Point.zero(), 0)
		}
		first = line.vertices.get(0) ?? S2Point.zero()
		last = line.vertices.get(line.vertices.len() - 1) ?? first
		if t <= 0.0 {
			return (first, 0)
		}
		if t >= 1.0 {
			return (last, line.num_edges())
		}

		target = t * line.length().radians()
		var $walked = 0.0
		var $result = last
		var $index = line.num_edges()
		var $done = Bool.False
		var $i = 1
		while $i < line.vertices.len() {
			if !$done {
				previous = line.vertices.get($i - 1) ?? S2Point.zero()
				current = line.vertices.get($i) ?? S2Point.zero()
				edge_length = previous.angle_to(current).radians()
				if $walked + edge_length >= target {
					fraction = if edge_length == 0.0 {
						0.0
					} else {
						(target - $walked) / edge_length
					}
					$result = S2Edge.interpolate(previous, current, fraction)
					$index = $i - 1
					$done = Bool.True
				} else {
					$walked = $walked + edge_length
				}
			}
			$i = $i + 1
		}
		($result, $index)
	}

	## The fraction along the polyline of the point closest to `p`, the
	## inverse of `interpolate`.
	un_interpolate : S2Polyline, S2Point -> F64
	un_interpolate = |line, p| {
		total = line.length().radians()
		if total == 0.0 {
			return 0.0
		}
		(_closest, edge_index) = line.project(p)
		var $walked = 0.0
		var $i = 1
		while $i <= edge_index {
			previous = line.vertices.get($i - 1) ?? S2Point.zero()
			current = line.vertices.get($i) ?? S2Point.zero()
			$walked = $walked + previous.angle_to(current).radians()
			$i = $i + 1
		}
		a = line.vertices.get(edge_index) ?? S2Point.zero()
		b = line.vertices.get(edge_index + 1) ?? a
		on_edge = S2Edge.project(p, a, b)
		(($walked + a.angle_to(on_edge).radians()) / total).max(0.0).min(1.0)
	}

	## The point of the polyline closest to `p`, with the index of the edge it
	## lies on.
	project : S2Polyline, S2Point -> (S2Point, U64)
	project = |line, p| {
		if line.vertices.is_empty() {
			return (S2Point.zero(), 0)
		}
		if line.vertices.len() == 1 {
			return (line.vertices.get(0) ?? S2Point.zero(), 0)
		}
		var $best = S1ChordAngle.infinity()
		var $point = line.vertices.get(0) ?? S2Point.zero()
		var $index = 0
		var $i = 1
		while $i < line.vertices.len() {
			a = line.vertices.get($i - 1) ?? S2Point.zero()
			b = line.vertices.get($i) ?? S2Point.zero()
			candidate = S2Edge.project(p, a, b)
			distance = S1ChordAngle.from_points(p, candidate)
			if distance < $best {
				$best = distance
				$point = candidate
				$index = $i - 1
			}
			$i = $i + 1
		}
		($point, $index)
	}

	## The distance from `p` to the closest point of the polyline.
	distance_to_point : S2Polyline, S2Point -> S1ChordAngle
	distance_to_point = |line, p| {
		(closest, _index) = line.project(p)
		S1ChordAngle.from_points(p, closest)
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
	(point, edge_index) = line.interpolate_with_edge(0.5)
	edge_index == 1 and S2LatLng.from_point(point).approx_eq(S2LatLng.from_degrees(0.0, 20.0), 1e-13)
}
expect {
	line = S2Polyline.from_lat_lngs([
		S2LatLng.from_degrees(0.0, 0.0),
		S2LatLng.from_degrees(0.0, 10.0),
		S2LatLng.from_degrees(0.0, 40.0),
	])
	(line.un_interpolate(line.interpolate(0.3)) - 0.3).abs() < 1e-13
}
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 90.0)])
	(closest, edge_index) = line.project(S2LatLng.from_degrees(10.0, 45.0).to_point())
	edge_index == 0 and S2LatLng.from_point(closest).approx_eq(S2LatLng.from_degrees(0.0, 45.0), 1e-13)
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

import S1Angle
import S2Cap
import S2CellId
import S2Edge
import S2LatLng
import S2LatLngRect
import S2Loop
import S2Point
import S2Polygon
import S2Polyline
import S2Predicates

## The smallest convex loop that contains a set of points, polylines, loops
## and polygons. Upstream's `S2ConvexHullQuery`.
##
## A loop is convex when it runs counterclockwise and every interior angle is
## at most 180 degrees. Points that are all within a hemisphere have a convex
## hull. Otherwise the hull is the full loop. The geometry is collected
## first and the hull computed at the end:
##
##     S2ConvexHullQuery.new()
##         .add_polyline(line)
##         .add_point(p)
##         .convex_hull()
##
## A query is a value, so each `add_` returns a new query and the old one is
## unchanged.
##
## The hull is found with Andrew's monotone chain algorithm, a variant of the
## Graham scan, in O(n log n) time for `n` vertices. Its vertices are a
## subset of the input vertices, apart from the special cases of one or two
## points. Points on the hull boundary are dropped, and so are duplicates.
## A point of the input on an edge of the hull can be found outside it by
## `S2Loop.contains_point`, since the edge is not exactly where the
## arithmetic puts it.
S2ConvexHullQuery := { bound : S2LatLngRect, points : List(S2Point) }.{

	## A query with no geometry. Its hull is the empty loop.
	new : () -> S2ConvexHullQuery
	new = || { bound: S2LatLngRect.empty(), points: [] }

	## The query with one more point.
	add_point : S2ConvexHullQuery, S2Point -> S2ConvexHullQuery
	add_point = |query, p| { bound: query.bound.add_point(p), points: query.points.append(p) }

	## The query with the vertices of the polyline added. A polyline adds
	## the same as its vertices would.
	add_polyline : S2ConvexHullQuery, S2Polyline -> S2ConvexHullQuery
	add_polyline = |query, line| {
		bound: query.bound.union(line.rect_bound()),
		points: query.points.concat(line.vertices()),
	}

	## The query with the loop added. The empty loop adds nothing, and the
	## full loop makes the hull full. Neither adds its marker vertex.
	add_loop : S2ConvexHullQuery, S2Loop -> S2ConvexHullQuery
	add_loop = |query, boundary| {
		bound = query.bound.union(boundary.rect_bound())
		if boundary.is_empty_or_full() {
			{ bound: bound, points: query.points }
		} else {
			{ bound: bound, points: query.points.concat(boundary.vertices()) }
		}
	}

	## The query with the polygon added. Only its shells at depth 0 can
	## reach the hull, so only they are added.
	add_polygon : S2ConvexHullQuery, S2Polygon -> S2ConvexHullQuery
	add_polygon = |query, polygon|
		polygon.loops().fold(
			query,
			|acc, entry| if (entry.depth == 0) acc.add_loop(entry.boundary) else acc,
		)

	## A cap that contains the hull: the cap bound of the rectangle that
	## bounds everything added. Upstream's `GetCapBound`, which keeps a
	## rectangle because the bound of a union of rectangles is easy to make
	## tight, and that of a union of caps is not.
	cap_bound : S2ConvexHullQuery -> S2Cap
	cap_bound = |query| query.bound.cap_bound()

	## The smallest convex loop that contains everything added. Upstream's
	## `GetConvexHull`.
	##
	## With no geometry the hull is the empty loop. When the bounding cap is
	## at least a hemisphere, after a small allowance for rounding, it is the
	## full loop. One point gives a tiny triangle with that point as a
	## vertex, which need not contain the point. Two points give a
	## degenerate triangle along the edge between them, through its
	## midpoint, or the full loop when they are antipodal.
	convex_hull : S2ConvexHullQuery -> S2Loop
	convex_hull = |query| {
		cap = query.cap_bound()
		if cap.height() >= 1.0 - 10.0 * 1.1102230246251565e-16 {
			return S2Loop.full()
		}
		# Sorting counterclockwise around a point outside the hull keeps the
		# chains monotone: every point is on one side of a great circle
		# through it.
		origin = vector_ortho(cap.center())
		sorted = query.points.sort_with(
			|x, y|
				if x == y {
					Same
				} else if S2Predicates.sign(origin, x, y) > 0 {
					Before
				} else {
					After
				},
		)
		points = dedup(sorted)
		match points {
			[] => S2Loop.empty()
			[p] => single_point_loop(p)
			[a, b] => single_edge_loop(a, b)
			_ => {
				lower = monotone_chain(points)
				upper = monotone_chain(points.rev())
				# Each chain ends where the other starts.
				S2Loop.from_points(lower.drop_last(1).concat(upper.drop_last(1)))
			}
		}
	}
}

## Upstream's `Vector3::Ortho`, which `GetConvexHull` uses in place of
## `S2::Ortho`: the cross product with the unit axis before the largest
## component, normalized.
vector_ortho : S2Point -> S2Point
vector_ortho = |a| {
	largest = a.largest_abs_component()
	k = if (largest == 0) 2 else largest - 1
	a.cross(S2Point.zero().with_coord(k, 1.0)).normalize()
}

## The list without its runs of equal points, each run reduced to one.
dedup : List(S2Point) -> List(S2Point)
dedup = |points|
	points.fold(
		[],
		|acc, p|
			match acc.last() {
				Ok(q) if q == p => acc
				_ => acc.append(p)
			},
	)

## The longest chain through the points, in order, that only turns left:
## each point drops the ones before it that would make a clockwise turn.
monotone_chain : List(S2Point) -> List(S2Point)
monotone_chain = |points| {
	var $chain = []
	for p in points {
		var $popping = Bool.True
		while $popping and $chain.len() >= 2 {
			a = $chain.get($chain.len() - 2) ?? p
			b = $chain.last() ?? p
			if S2Predicates.sign(a, b, p) <= 0 {
				$chain = $chain.drop_last(1)
			} else {
				$popping = Bool.False
			}
		}
		$chain = $chain.append(p)
	}
	$chain
}

## A triangle of `p` and two points 1e-15 away from it.
single_point_loop : S2Point -> S2Loop
single_point_loop = |p| {
	offset = 1e-15
	d0 = p.ortho()
	d1 = p.cross(d0)
	S2Loop.from_points([p, (p + d0 * offset).normalize(), (p + d1 * offset).normalize()])
}

## The degenerate triangle of `a`, `b` and the midpoint of the edge between
## them, normalized. Antipodal points give the full loop, since the edge
## between them has no defined direction.
single_edge_loop : S2Point, S2Point -> S2Loop
single_edge_loop = |a, b|
	if a == -b {
		S2Loop.full()
	} else {
		S2Loop.from_points([a, b, S2Edge.interpolate(a, b, 0.5)]).normalized()
	}

# Upstream's S2ConvexHullQuery tests NoPoints, EmptyLoop, FullLoop,
# EmptyPolygon and TwoAntipodalPoints.
expect S2ConvexHullQuery.new().convex_hull().is_empty()
expect S2ConvexHullQuery.new().add_loop(S2Loop.empty()).convex_hull().is_empty()
expect S2ConvexHullQuery.new().add_loop(S2Loop.full()).convex_hull().is_full()
expect S2ConvexHullQuery.new().add_polygon(S2Polygon.empty()).convex_hull().is_empty()
expect
	S2ConvexHullQuery.new()
		.add_point(S2Point.new(0.0, 0.0, 1.0))
		.add_point(S2Point.new(0.0, 0.0, -1.0))
		.convex_hull()
		.is_full()

# Upstream's S2ConvexHullQuery.SimplePolyline. The hull's vertices, in order,
# are from upstream through tools/s2_oracle.cc, and have the same boundary as
# the loop upstream's test expects.
expect {
	hull = S2ConvexHullQuery.new().add_polyline(S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 9.0), S2LatLng.from_degrees(1.0, 6.0), S2LatLng.from_degrees(2.0, 6.0), S2LatLng.from_degrees(3.0, 10.0), S2LatLng.from_degrees(4.0, 10.0), S2LatLng.from_degrees(5.0, 5.0), S2LatLng.from_degrees(4.0, 0.0), S2LatLng.from_degrees(3.0, 0.0), S2LatLng.from_degrees(2.0, 5.0), S2LatLng.from_degrees(1.0, 5.0)])).convex_hull()
	hull.vertices() == [
		S2Point.new(0.99984769515639127, 0.017452406437283512, 0.0),
		S2Point.new(0.98768834059513777, 0.15643446504023087, 0.0),
		S2Point.new(0.9834581082132785, 0.17341019887450621, 0.052335956242943835),
		S2Point.new(0.98240881082213483, 0.17322517943366056, 0.069756473744125302),
		S2Point.new(0.99240387650610407, 0.086824088833465166, 0.087155742747658166),
		S2Point.new(0.9975640502598242, 0.0, 0.069756473744125302),
		S2Point.new(0.99862953475457383, 0.0, 0.052335956242943835),
	]
		and hull.boundary_equals(S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 9.0), S2LatLng.from_degrees(3.0, 10.0), S2LatLng.from_degrees(4.0, 10.0), S2LatLng.from_degrees(5.0, 5.0), S2LatLng.from_degrees(4.0, 0.0), S2LatLng.from_degrees(3.0, 0.0)]))
}
# Upstream's OnePoint and TwoPoints: a tiny triangle at the point, and a
# degenerate triangle along the edge, the same when points repeat. The
# vertices are from upstream.
expect {
	query = S2ConvexHullQuery.new().add_point(S2Point.new(0.0, 0.0, 1.0))
	hull = query.convex_hull()
	hull.vertices() == [
		S2Point.new(0.0, 0.0, 1.0),
		S2Point.new(-9.9992800777506695e-16, 1.1999136093300805e-17, 1.0),
		S2Point.new(-1.1999136093300805e-17, -9.9992800777506695e-16, 1.0),
	]
		and hull.is_normalized()
		and query.add_point(S2Point.new(0.0, 0.0, 1.0)).convex_hull() == hull
}
expect {
	query = S2ConvexHullQuery.new().add_point(S2Point.new(0.0, 0.0, 1.0)).add_point(S2Point.new(0.0, 1.0, 0.0))
	hull = query.convex_hull()
	hull.vertices() == [
		S2Point.new(0.0, 0.0, 1.0),
		S2Point.new(0.0, 1.0, 0.0),
		S2Point.new(0.0, 0.70710678118654746, 0.70710678118654757),
	]
		and hull.is_normalized()
		and query.add_point(S2Point.new(0.0, 0.0, 1.0)).add_point(S2Point.new(0.0, 1.0, 0.0)).convex_hull() == hull
}
# Upstream's NonConvexPoints (the six face centres) and
# CapBoundExpandedToHemisphere: both give the full loop (full, full).
expect [0, 1, 2, 3, 4, 5].fold(S2ConvexHullQuery.new(), |q, face| q.add_point(S2CellId.from_face(face).to_point())).convex_hull().is_full()
expect
	S2ConvexHullQuery.new()
		.add_point(S2LatLng.from_degrees(0.0, 0.0).to_point())
		.add_point(S2LatLng.from_degrees(0.0, 45.0).to_point())
		.add_point(S2LatLng.from_degrees(0.0, -135.0).to_point())
		.convex_hull()
		.is_full()
# Only a polygon's shells reach the hull. From upstream.
expect {
	polygon = S2Polygon.from_loops([S2Loop.from_lat_lngs([S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(0.0, 10.0), S2LatLng.from_degrees(10.0, 10.0), S2LatLng.from_degrees(10.0, 0.0)]), S2Loop.from_lat_lngs([S2LatLng.from_degrees(2.0, 2.0), S2LatLng.from_degrees(2.0, 8.0), S2LatLng.from_degrees(8.0, 8.0), S2LatLng.from_degrees(8.0, 2.0)])])
	S2ConvexHullQuery.new().add_polygon(polygon).convex_hull().vertices() == [
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(0.98480775301220802, 0.17364817766693033, 0.0),
		S2Point.new(0.9698463103929541, 0.17101007166283433, 0.17364817766693033),
		S2Point.new(0.98480775301220802, 0.0, 0.17364817766693033),
	]
}
# Upstream's LoopsAroundNorthPole: a regular loop is its own hull up to 90
# degrees, and beyond that the hull is full.
expect {
	north = |degrees, n| {
		loop = S2Loop.make_regular_loop(S2Point.new(0.0, 0.0, 1.0), S1Angle.from_degrees(degrees), n)
		hull = S2ConvexHullQuery.new().add_loop(loop).convex_hull()
		if (degrees > 90.0) hull.is_full() else hull.boundary_equals(loop)
	}
	north(1.0, 3) and north(89.0, 3) and north(91.0, 3) and north(179.0, 3) and north(10.0, 100) and north(89.0, 1000)
}
# The cap bound is that of the rectangle bound of everything added.
expect {
	line = S2Polyline.from_lat_lngs([S2LatLng.from_degrees(0.0, 1.0), S2LatLng.from_degrees(0.0, 9.0), S2LatLng.from_degrees(1.0, 6.0), S2LatLng.from_degrees(2.0, 6.0), S2LatLng.from_degrees(3.0, 10.0), S2LatLng.from_degrees(4.0, 10.0), S2LatLng.from_degrees(5.0, 5.0), S2LatLng.from_degrees(4.0, 0.0), S2LatLng.from_degrees(3.0, 0.0), S2LatLng.from_degrees(2.0, 5.0), S2LatLng.from_degrees(1.0, 5.0)])
	S2ConvexHullQuery.new().add_polyline(line).cap_bound() == line.rect_bound().cap_bound()
}

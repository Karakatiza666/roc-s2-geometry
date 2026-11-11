import s2.S2Cell
import s2.S2CellId
import s2.S2LatLng
import s2.S2Loop
import s2.S2Point
import s2.S2Polygon
import s2.S2RegionCoverer
import PolygonCorpus

## Checks the polygon predicates against upstream's relation table.
##
## `PolygonCorpus` carries the polygons and the answers from
## `s2polygon_test.cc`: for every interesting pair, whether A contains B,
## whether B contains A, and whether the two intersect. The polygons are the
## ones upstream chose to be awkward, which is why the table is worth reusing:
## rings nested five deep, shapes whose hole is exactly where the other
## polygon sits, and rectangles arranged to touch at shared vertices without
## any edge crossing another.
##
## Upstream also checks each relation against the polygons' complements, which
## needs the boolean operations this port leaves out. What is checked here is
## the three relations themselves, plus the nesting and point containment
## from upstream's other two tables.
S2PolygonTest := [].{

	loop_of : List((F64, F64)) -> S2Loop
	loop_of = |points| S2Loop.from_points(
		points.map(|(lat, lng)| S2LatLng.from_degrees(lat, lng).to_point()),
	)

	polygon_of : List(List((F64, F64))), Bool -> S2Polygon
	polygon_of = |loops, is_full| if is_full {
		S2Polygon.full()
	} else {
		S2Polygon.from_loops(loops.map(S2PolygonTest.loop_of))
	}

	## 0 when the claim holds, 1 when it does not.
	fault : Bool -> U64
	fault = |ok| if ok {
		0
	} else {
		1
	}

	failures_of : PolygonCorpus.Case -> U64
	failures_of = |case| {
		a = S2PolygonTest.polygon_of(case.a, case.a_full)
		b = S2PolygonTest.polygon_of(case.b, case.b_full)
		S2PolygonTest.fault(a.contains_polygon(b) == case.contains)
			+ S2PolygonTest.fault(b.contains_polygon(a) == case.contained)
			+ S2PolygonTest.fault(a.intersects_polygon(b) == case.intersects)
			+ S2PolygonTest.fault(b.intersects_polygon(a) == case.intersects)
	}

	## The cases that fail any of their claims.
	failures : () -> U64
	failures = || PolygonCorpus.cases.fold(0, |acc, case| if (S2PolygonTest.failures_of(case) > 0) acc + 1 else acc)

	## Pairs upstream states are nested, checked both ways round.
	nesting_failures : () -> U64
	nesting_failures = || {
		var $count = 0
		for (outer, inner) in PolygonCorpus.nested {
			a = S2PolygonTest.polygon_of(outer, Bool.False)
			b = S2PolygonTest.polygon_of(inner, Bool.False)
			if !a.contains_polygon(b) or !a.intersects_polygon(b) {
				$count = $count + 1
			}
			# Only the empty polygon is contained by something it contains.
			if b.contains_polygon(a) {
				$count = $count + 1
			}
		}
		$count
	}

	## A polygon out of one cell's boundary, with a smaller loop inside it
	## punched out as a hole.
	##
	## The hole runs through the four child centres, so it shares no vertex
	## and no edge with the cell's own boundary: a child cell's boundary would
	## have run along its parent's, which is not nesting.
	ring_of : S2Cell -> S2Polygon
	ring_of = |cell| S2Polygon.from_loops(
		[S2PolygonTest.loop_of_cell(cell), S2PolygonTest.hole_of(cell)],
	)

	## Normalized, because the Hilbert order the children come back in runs
	## clockwise on some faces.
	hole_of : S2Cell -> S2Loop
	hole_of = |cell| S2Loop.from_points(cell.subdivide().map(S2Cell.center)).normalized()

	## A point close to one corner of the cell, well outside the hole.
	corner_of : S2Cell -> S2Point
	corner_of = |cell| cell.vertex(0).times(7.0).plus(cell.center()).normalize()

	loop_of_cell : S2Cell -> S2Loop
	loop_of_cell = |cell| S2Loop.from_points(
		[cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3)],
	)

	## Positions upstream states are inside their polygon.
	point_failures : () -> U64
	point_failures = || {
		var $count = 0
		for (loops, lat, lng) in PolygonCorpus.points {
			polygon = S2PolygonTest.polygon_of(loops, Bool.False)
			if !polygon.contains_lat_lng(S2LatLng.from_degrees(lat, lng)) {
				$count = $count + 1
			}
		}
		$count
	}
}

expect PolygonCorpus.cases.len() == 61
expect S2PolygonTest.failures() == 0
expect S2PolygonTest.nesting_failures() == 0
expect S2PolygonTest.point_failures() == 0

# A ring is its outer loop less the hole, and the hole is a hole.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	ring = S2PolygonTest.ring_of(cell)
	expected = S2PolygonTest.loop_of_cell(cell).area() - S2PolygonTest.hole_of(cell).area()
	ring.num_loops() == 2
		and ring.depth_at(0) == 0
		and ring.depth_at(1) == 1
		and (ring.area() - expected).abs() < 1e-12 * expected
}

# The outer loop of the ring is the cell, whose area is measured against
# upstream elsewhere.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	outer = S2PolygonTest.loop_of_cell(cell).area()
	(outer - cell.exact_area()).abs() < 1e-12 * cell.exact_area()
}

# The hole is outside the ring, and the corner of the cell is inside it.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	ring = S2PolygonTest.ring_of(cell)
	!ring.contains_point(cell.center())
		and ring.contains_point(S2PolygonTest.corner_of(cell))
}

# A ring meets the cell it was cut from, and misses the far side of the sphere.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	ring = S2PolygonTest.ring_of(cell)
	near_corner = S2Cell.from_cell_id(
		S2CellId.from_point(S2PolygonTest.corner_of(cell)).parent_at_level(12),
	)
	far_side = S2Cell.from_cell_id(S2CellId.from_point(cell.center().negate()).parent_at_level(6))
	ring.may_intersect_cell(near_corner)
		and !ring.may_intersect_cell(far_side)
		and !ring.contains_cell(far_side)
}

# A cell well inside the ring is contained by it.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	ring = S2PolygonTest.ring_of(cell)
	inside = S2Cell.from_cell_id(
		S2CellId.from_point(S2PolygonTest.corner_of(cell)).parent_at_level(14),
	)
	ring.contains_cell(inside) and ring.may_intersect_cell(inside)
}

# A polygon is a region, so the coverer takes one.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	ring = S2PolygonTest.ring_of(cell)
	covering = S2RegionCoverer.default().with_max_level(10).covering(ring)
	var $ok = !covering.is_empty()
	for id in covering {
		if !ring.may_intersect_cell(S2Cell.from_cell_id(id)) {
			$ok = Bool.False
		}
	}
	$ok
}

# The empty and full polygons behave as the identities of containment.
expect S2Polygon.empty().is_empty()
expect S2Polygon.full().is_full()
expect S2Polygon.empty().area() == 0.0
expect (S2Polygon.full().area() - 4.0 * F64.pi).abs() < 1e-12
expect S2Polygon.full().contains_polygon(S2Polygon.empty())
expect !S2Polygon.empty().contains_polygon(S2Polygon.full())
expect !S2Polygon.empty().intersects_polygon(S2Polygon.full())
expect S2Polygon.full().intersects_polygon(S2Polygon.full())
expect S2Polygon.from_loops([]).is_empty()
expect S2Polygon.from_loops([S2Loop.empty()]).is_empty()

# A polygon holds the loop it was built from, and every loop that one holds.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	outer = S2PolygonTest.loop_of_cell(cell)
	inner = S2PolygonTest.hole_of(cell)
	polygon = S2Polygon.from_loop(outer)
	polygon.contains_loop(inner)
		and polygon.intersects_loop(inner)
		and polygon.is_valid()
		and polygon.approx_eq(S2Polygon.from_loop(outer), 0.0)
}

# A hole makes the loop that fills it no longer contained.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face_pos_level(2, 0, 6))
	ring = S2PolygonTest.ring_of(cell)
	!ring.contains_loop(S2PolygonTest.hole_of(cell))
		and ring.intersects_loop(S2PolygonTest.loop_of_cell(cell))
}

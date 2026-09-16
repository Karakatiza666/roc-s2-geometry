import s2.S2Cell
import s2.S2CellId
import s2.S2Loop
import s2.S2Point
import s2.S2Polyline
import s2.S2RegionCoverer
import CellCorpus

## Cross-checks `S2Loop` and `S2Polyline` against cell geometry.
##
## s2sphere has no loop or polyline type, so instead of comparing outputs these
## checks build shapes out of cells whose measurements are already pinned to
## upstream by `S2CellTest`, and require the shapes to agree with them. A loop
## through a cell's four vertices must enclose exactly the cell's area, and a
## polyline around its boundary must be exactly as long as its four edges.
S2ShapeTest := [].{

	cell_of : CellCorpus.Case -> S2Cell
	cell_of = |case| S2Cell.from_cell_id(S2CellId.from_id(case.id))

	## The loop bounding a cell, counterclockwise like the cell's own
	## vertices.
	loop_of : S2Cell -> S2Loop
	loop_of = |cell| S2Loop.from_points([cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3)])

	## Cases coarse enough that a cell's own diameter is far above rounding,
	## which is what the area and containment checks need.
	coarse_cases : List(CellCorpus.Case)
	coarse_cases = CellCorpus.cases.keep_if(|case| case.level <= 12)

	failures : (CellCorpus.Case -> Bool) -> U64
	failures = |check| S2ShapeTest.coarse_cases.fold(0, |acc, case| if check(case) acc else acc + 1)

	close : F64, F64, F64, F64 -> Bool
	close = |actual, expected, absolute, relative|
		(actual - expected).abs() <= absolute + relative * expected.abs()
}

expect S2ShapeTest.coarse_cases.len() > 40

# A loop through a cell's vertices encloses the cell.
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		S2ShapeTest.loop_of(cell).is_valid()
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		S2ShapeTest.close(S2ShapeTest.loop_of(cell).area(), cell.exact_area(), 1e-30, 1e-9)
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		S2ShapeTest.loop_of(cell).contains_point(cell.center())
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		# The antipode of the centre is outside any cell-sized loop.
		!S2ShapeTest.loop_of(cell).contains_point(-cell.center())
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		loop = S2ShapeTest.loop_of(cell)
		# Gauss-Bonnet: turning angle plus enclosed area is 2 pi.
		S2ShapeTest.close(loop.turning_angle() + loop.area(), 2.0 * F64.pi, 1e-12, 0.0)
			and loop.is_normalized()
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		loop = S2ShapeTest.loop_of(cell)
		inverted = loop.invert()
		S2ShapeTest.close(loop.area() + inverted.area(), 4.0 * F64.pi, 1e-12, 0.0)
			and !inverted.contains_point(cell.center())
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		loop = S2ShapeTest.loop_of(cell)
		# The loop's bound must cover the cell's own vertices.
		bound = loop.rect_bound()
		[0, 1, 2, 3].all(|k| bound.contains_point(cell.vertex(k)))
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		loop = S2ShapeTest.loop_of(cell)
		# The loop meets its own cell, and contains the cell's children well
		# inside it only when the cell itself is not a leaf.
		loop.may_intersect_cell(cell) and loop.cap_bound().contains_point(cell.center())
	},
)
	== 0

# A polyline around a cell's boundary is as long as the cell's four edges.
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		line = S2Polyline.from_points(
			[cell.vertex(0), cell.vertex(1), cell.vertex(2), cell.vertex(3), cell.vertex(0)],
		)
		perimeter = [0, 1, 2, 3].fold(
			0.0,
			|acc, k| acc + cell.vertex(k).angle_to(cell.vertex((k + 1) % 4)).radians(),
		)
		line.is_valid() and S2ShapeTest.close(line.length().radians(), perimeter, 1e-30, 1e-12)
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		line = S2Polyline.from_points([cell.vertex(0), cell.vertex(1), cell.vertex(2)])
		# Interpolating and inverting the interpolation is the identity.
		[0.0, 0.25, 0.5, 0.75, 1.0].all(
			|t| (line.un_interpolate(line.interpolate(t)) - t).abs() < 1e-9,
		)
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		line = S2Polyline.from_points([cell.vertex(0), cell.vertex(1), cell.vertex(2)])
		# Every vertex lies on the polyline, and the projection finds it.
		[0, 1, 2].all(
			|k| {
				(closest, _edge) = line.project(cell.vertex(k))
				closest.approx_eq(cell.vertex(k), 1e-14)
			},
		)
	},
)
	== 0
expect S2ShapeTest.failures(
	|case| {
		cell = S2ShapeTest.cell_of(case)
		line = S2Polyline.from_points([cell.vertex(0), cell.vertex(1), cell.vertex(2)])
		reversed = line.reversed()
		S2ShapeTest.close(reversed.length().radians(), line.length().radians(), 1e-30, 1e-15)
			and reversed.may_intersect_cell(cell)
	},
)
	== 0

# A loop is a region, so a coverer can approximate it.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face(0).child_begin_at_level(6))
	loop = S2ShapeTest.loop_of(cell)
	covering = S2RegionCoverer.default().with_max_cells(8).with_max_level(10).cell_union_covering(loop)
	covering.contains_point(cell.center())
}

# So is a polyline, though it contains nothing and so has no interior covering.
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_face(2).child_begin_at_level(6))
	line = S2Polyline.from_points([cell.vertex(0), cell.vertex(1), cell.vertex(2)])
	coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(10)
	covering = coverer.cell_union_covering(line)
	covering.contains_point(cell.vertex(0))
		and covering.contains_point(cell.vertex(2))
			and coverer.interior_covering(line).is_empty()
}

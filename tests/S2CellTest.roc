import s2.R1Interval
import s2.S1Interval
import s2.S2Cap
import s2.S2Cell
import s2.S2CellId
import s2.S2LatLngRect
import s2.S2Point
import CellCorpus

## Checks `S2Cell` geometry, and the cell bounds that live on `S2LatLngRect`
## and `S2Cap`, against a corpus generated from s2sphere.
S2CellTest := [].{

	cell_of : CellCorpus.Case -> S2Cell
	cell_of = |case| S2Cell.from_cell_id(S2CellId.from_id(case.id))

	failures : (CellCorpus.Case -> Bool) -> U64
	failures = |check| CellCorpus.cases.fold(0, |acc, case| if (check(case)) acc else acc + 1)

	## True when the two values agree to within an absolute and a relative
	## tolerance.
	close : F64, F64, F64, F64 -> Bool
	close = |actual, expected, absolute, relative|
		(actual - expected).abs() <= absolute + relative * expected.abs()
}

# The decoded cell's identity.
expect S2CellTest.failures(|case| S2CellTest.cell_of(case).face() == case.face) == 0
expect S2CellTest.failures(|case| S2CellTest.cell_of(case).level() == case.level) == 0
expect S2CellTest.failures(|case| S2CellTest.cell_of(case).orientation() == case.orientation) == 0

# The four vertices, in order.
expect S2CellTest.failures(
	|case| {
		cell = S2CellTest.cell_of(case)
		case.vertices.map2(
			[0, 1, 2, 3],
			|(x, y, z), k| cell.vertex(k).approx_eq(S2Point.new(x, y, z), 1e-15),
		)
			.all(|ok| ok)
	},
)
	== 0

# Areas, by all three methods.
#
# The tolerance is 1e-7 relative rather than machine precision because a leaf
# cell's area is about 1e-18 steradians, and l'Huilier's formula amplifies
# rounding at that scale. Upstream documents `exact_area` as good to six
# digits; the two implementations agree to about eight.
expect S2CellTest.failures(
	|case| S2CellTest.close(S2CellTest.cell_of(case).exact_area(), case.exact_area, 1e-30, 1e-7),
)
	== 0
expect S2CellTest.failures(
	|case| S2CellTest.close(S2CellTest.cell_of(case).approx_area(), case.approx_area, 1e-30, 1e-7),
)
	== 0
expect S2CellTest.failures(
	|case| S2CellTest.close(S2CellTest.cell_of(case).average_area(), case.average_area, 0.0, 1e-15),
)
	== 0

# The bounding rectangle.
expect S2CellTest.failures(
	|case| {
		expected = S2LatLngRect.new(
			R1Interval.new(case.rect_lat_lo, case.rect_lat_hi),
			S1Interval.new(case.rect_lng_lo, case.rect_lng_hi),
		)
		S2LatLngRect.from_cell(S2CellTest.cell_of(case)).approx_eq(expected, 1e-14)
	},
)
	== 0

# The bounding cap.
expect S2CellTest.failures(
	|case| {
		cap = S2Cap.from_cell(S2CellTest.cell_of(case))
		(axis_x, axis_y, axis_z) = case.cap_axis
		cap.center().approx_eq(S2Point.new(axis_x, axis_y, axis_z), 1e-14)
			and S2CellTest.close(cap.height(), case.cap_height, 1e-30, 1e-7)
	},
)
	== 0

# Properties that must hold for every cell, over the same corpus.
expect S2CellTest.failures(
	|case| {
		cell = S2CellTest.cell_of(case)
		cell.contains_point(cell.center())
			and S2LatLngRect.from_cell(cell).contains_point(cell.center())
			and S2Cap.from_cell(cell).contains_point(cell.center())
	},
)
	== 0
expect S2CellTest.failures(
	|case| {
		cell = S2CellTest.cell_of(case)
		bound = S2LatLngRect.from_cell(cell)
		cap = S2Cap.from_cell(cell)
		[0, 1, 2, 3].all(
			|k| bound.contains_point(cell.vertex(k)) and cap.contains_point(cell.vertex(k)),
		)
	},
)
	== 0
expect S2CellTest.failures(
	|case| {
		cell = S2CellTest.cell_of(case)
		[0, 1, 2, 3].all(
			|k| {
				normal = cell.edge(k)
				normal.dot(cell.vertex(k)).abs() < 1e-14
					and normal.dot(cell.vertex((k + 1) % 4)).abs() < 1e-14
			},
		)
	},
)
	== 0
expect S2CellTest.failures(
	|case| {
		cell = S2CellTest.cell_of(case)
		if cell.is_leaf() {
			cell.subdivide().is_empty()
		} else {
			children = cell.subdivide()
			total = children.fold(0.0, |acc, child| acc + child.exact_area())
			children.len() == 4 and S2CellTest.close(total, cell.exact_area(), 1e-30, 1e-7)
		}
	},
)
	== 0
expect S2CellTest.failures(
	|case| {
		cell = S2CellTest.cell_of(case)
		cell.distance_to_point(cell.center()).is_zero()
			and cell.max_distance_to_point(cell.center()) >= cell.distance_to_point(cell.center())
	},
)
	== 0

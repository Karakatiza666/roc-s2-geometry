import s2.R1Interval
import s2.S1Angle
import s2.S1Interval
import s2.S2Cap
import s2.S2Cell
import s2.S2CellId
import s2.S2LatLngRect
import s2.S2Point
import RegionCorpus

## Checks the two bounding regions, `S2Cap` and `S2LatLngRect`, against
## s2sphere: their own measures, the bounds they produce for each other, and
## the predicates the region coverer relies on.
S2RegionTest := [].{

	cap_of : RegionCorpus.Case -> S2Cap
	cap_of = |case| {
		(x, y, z) = case.cap_center
		S2Cap.from_center_angle(S2Point.new(x, y, z), S1Angle.from_degrees(case.cap_radius_degrees))
	}

	rect_of : RegionCorpus.Case -> S2LatLngRect
	rect_of = |case|
		S2LatLngRect.new(
			R1Interval.new(case.rect_lat_lo, case.rect_lat_hi),
			S1Interval.new(case.rect_lng_lo, case.rect_lng_hi),
		)

	cell_of : RegionCorpus.Case -> S2Cell
	cell_of = |case| S2Cell.from_cell_id(S2CellId.from_id(case.cell_id))

	failures : (RegionCorpus.Case -> Bool) -> U64
	failures = |check| RegionCorpus.cases.fold(0, |acc, case| if check(case) acc else acc + 1)

	close : F64, F64, F64, F64 -> Bool
	close = |actual, expected, absolute, relative|
		(actual - expected).abs() <= absolute + relative * expected.abs()
}

# Cap measures and the rectangle that bounds a cap.
expect S2RegionTest.failures(
	|case| S2RegionTest.close(S2RegionTest.cap_of(case).area(), case.cap_area, 1e-30, 1e-12),
)
	== 0
expect S2RegionTest.failures(
	|case| {
		expected = S2LatLngRect.new(
			R1Interval.new(case.cap_rect_lat_lo, case.cap_rect_lat_hi),
			S1Interval.new(case.cap_rect_lng_lo, case.cap_rect_lng_hi),
		)
		S2LatLngRect.from_cap(S2RegionTest.cap_of(case)).approx_eq(expected, 1e-14)
	},
)
	== 0

# The two predicates a region coverer asks of a cap.
expect S2RegionTest.failures(
	|case| S2RegionTest.cap_of(case).contains_cell(S2RegionTest.cell_of(case)) == case.cap_contains_cell,
)
	== 0
expect S2RegionTest.failures(
	|case|
		S2RegionTest.cap_of(case).may_intersect_cell(S2RegionTest.cell_of(case))
			== case.cap_may_intersect_cell,
)
	== 0

# Rectangle measures and the cap that bounds a rectangle.
expect S2RegionTest.failures(
	|case| S2RegionTest.close(S2RegionTest.rect_of(case).area(), case.rect_area, 1e-30, 1e-12),
)
	== 0
expect S2RegionTest.failures(
	|case| {
		cap = S2RegionTest.rect_of(case).cap_bound()
		(x, y, z) = case.rect_cap_axis
		cap.center().approx_eq(S2Point.new(x, y, z), 1e-13)
			and S2RegionTest.close(cap.height(), case.rect_cap_height, 1e-15, 1e-12)
	},
)
	== 0

# Rectangle against cell, both the exact test and the cheap one.
expect S2RegionTest.failures(
	|case|
		S2RegionTest.rect_of(case).contains_cell(S2RegionTest.cell_of(case)) == case.rect_contains_cell,
)
	== 0
expect S2RegionTest.failures(
	|case|
		S2RegionTest.rect_of(case).intersects_cell(S2RegionTest.cell_of(case))
			== case.rect_intersects_cell,
)
	== 0
expect S2RegionTest.failures(
	|case|
		S2RegionTest.rect_of(case).may_intersect_cell(S2RegionTest.cell_of(case))
			== case.rect_may_intersect_cell,
)
	== 0

# Relationships that must hold between the predicates themselves.
expect S2RegionTest.failures(
	|case| {
		cap = S2RegionTest.cap_of(case)
		cell = S2RegionTest.cell_of(case)
		!cap.contains_cell(cell) or cap.may_intersect_cell(cell)
	},
)
	== 0
expect S2RegionTest.failures(
	|case| {
		rect = S2RegionTest.rect_of(case)
		cell = S2RegionTest.cell_of(case)
		# The exact test never reports an intersection the cheap one misses.
		!rect.intersects_cell(cell) or rect.may_intersect_cell(cell)
	},
)
	== 0
expect S2RegionTest.failures(
	|case| {
		cap = S2RegionTest.cap_of(case)
		S2LatLngRect.from_cap(cap).contains_point(cap.center()) or cap.is_empty()
	},
)
	== 0

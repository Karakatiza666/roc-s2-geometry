import s2.S1Angle
import s2.S2Cap
import s2.S2CellId
import s2.S2Point
import s2.S2RegionCoverer
import CoverCorpus

## Checks `S2RegionCoverer` against coverings generated from s2sphere.
##
## The comparison is cell for cell and in order, so it pins down the
## refinement order and the tie-breaking as well as the final set.
S2RegionCovererTest := [].{

	cap_of : CoverCorpus.Case -> S2Cap
	cap_of = |case| {
		(x, y, z) = case.center
		S2Cap.from_center_angle(S2Point.new(x, y, z), S1Angle.from_degrees(case.radius_degrees))
	}

	coverer_of : CoverCorpus.Case -> S2RegionCoverer
	coverer_of = |case|
		S2RegionCoverer.default()
			.with_max_cells(case.max_cells)
			.with_min_level(case.min_level)
			.with_max_level(case.max_level)
			.with_level_mod(case.level_mod)

	failures : (CoverCorpus.Case -> Bool) -> U64
	failures = |check| CoverCorpus.cases.fold(0, |acc, case| if check(case) acc else acc + 1)
}

expect S2RegionCovererTest.failures(
	|case|
		S2RegionCovererTest.coverer_of(case)
			.covering(S2RegionCovererTest.cap_of(case))
			.map(S2CellId.id)
			== case.covering,
)
	== 0

expect S2RegionCovererTest.failures(
	|case|
		S2RegionCovererTest.coverer_of(case)
			.interior_covering(S2RegionCovererTest.cap_of(case))
			.map(S2CellId.id)
			== case.interior_covering,
)
	== 0

# Properties the covering must have regardless of what upstream produced.
expect S2RegionCovererTest.failures(
	|case| {
		cap = S2RegionCovererTest.cap_of(case)
		S2RegionCovererTest.coverer_of(case)
			.cell_union_covering(cap)
			.contains_point(cap.center())
	},
)
	== 0

expect S2RegionCovererTest.failures(
	|case| {
		cap = S2RegionCovererTest.cap_of(case)
		coverer = S2RegionCovererTest.coverer_of(case)
		coverer.cell_union_covering(cap).contains_union(coverer.cell_union_interior_covering(cap))
	},
)
	== 0

# Level constraints are honoured by every cell of the covering.
expect S2RegionCovererTest.failures(
	|case|
		S2RegionCovererTest.coverer_of(case)
			.covering(S2RegionCovererTest.cap_of(case))
			.all(
				|cell_id| {
					level = cell_id.level()
					level >= case.min_level
						and level <= case.max_level
							and (level - case.min_level) % case.level_mod == 0
				},
			),
)
	== 0

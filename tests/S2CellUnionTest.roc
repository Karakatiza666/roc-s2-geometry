import s2.S2CellId
import s2.S2CellUnion
import CellUnionCorpus

## Checks `S2CellUnion` normalization and set operations against s2sphere.
S2CellUnionTest := [].{

	union_of : List(U64) -> S2CellUnion
	union_of = |ids| S2CellUnion.from_ids(ids)

	failures : (CellUnionCorpus.Case -> Bool) -> U64
	failures = |check| CellUnionCorpus.cases.fold(0, |acc, case| if (check(case)) acc else acc + 1)
}

# Normalization: sorting, absorbing contained cells, and folding four siblings
# into their parent.
expect S2CellUnionTest.failures(
	|case| S2CellUnionTest.union_of(case.raw_a).cell_ids().map(S2CellId.id) == case.normalized_a,
)
	== 0
expect S2CellUnionTest.failures(
	|case| S2CellUnionTest.union_of(case.raw_b).cell_ids().map(S2CellId.id) == case.normalized_b,
)
	== 0

# Normalization is idempotent.
expect S2CellUnionTest.failures(
	|case| S2CellUnionTest.union_of(case.normalized_a).cell_ids().map(S2CellId.id) == case.normalized_a,
)
	== 0

# The three set operations.
expect S2CellUnionTest.failures(
	|case|
		S2CellUnionTest.union_of(case.raw_a)
			.union(S2CellUnionTest.union_of(case.raw_b))
			.cell_ids()
			.map(S2CellId.id)
			== case.union,
)
	== 0
expect S2CellUnionTest.failures(
	|case|
		S2CellUnionTest.union_of(case.raw_a)
			.intersection(S2CellUnionTest.union_of(case.raw_b))
			.cell_ids()
			.map(S2CellId.id)
			== case.intersection,
)
	== 0
expect S2CellUnionTest.failures(
	|case|
		S2CellUnionTest.union_of(case.raw_a)
			.difference(S2CellUnionTest.union_of(case.raw_b))
			.cell_ids()
			.map(S2CellId.id)
			== case.difference,
)
	== 0

# Containment and intersection of a single cell.
expect S2CellUnionTest.failures(
	|case|
		S2CellUnionTest.union_of(case.raw_a).contains_cell_id(S2CellId.from_id(case.probe_id))
			== case.a_contains_probe,
)
	== 0
expect S2CellUnionTest.failures(
	|case|
		S2CellUnionTest.union_of(case.raw_a).intersects_cell_id(S2CellId.from_id(case.probe_id))
			== case.a_intersects_probe,
)
	== 0

# Set identities that must hold whatever upstream produced.
expect S2CellUnionTest.failures(
	|case| {
		a = S2CellUnionTest.union_of(case.raw_a)
		b = S2CellUnionTest.union_of(case.raw_b)
		union = a.union(b)
		union.contains_union(a) and union.contains_union(b)
	},
)
	== 0
expect S2CellUnionTest.failures(
	|case| {
		a = S2CellUnionTest.union_of(case.raw_a)
		b = S2CellUnionTest.union_of(case.raw_b)
		intersection = a.intersection(b)
		a.contains_union(intersection) and b.contains_union(intersection)
	},
)
	== 0
expect S2CellUnionTest.failures(
	|case| {
		a = S2CellUnionTest.union_of(case.raw_a)
		b = S2CellUnionTest.union_of(case.raw_b)
		# Difference and intersection partition the first union.
		a.difference(b).union(a.intersection(b)) == a
	},
)
	== 0
expect S2CellUnionTest.failures(
	|case| {
		a = S2CellUnionTest.union_of(case.raw_a)
		b = S2CellUnionTest.union_of(case.raw_b)
		!a.difference(b).intersects_union(b)
	},
)
	== 0

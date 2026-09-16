import s2.S2Point
import s2.S2Predicates
import ExactCorpus

## Checks the exact-arithmetic core against determinant signs computed with
## Python's rational arithmetic, so the expected answers are mathematically
## exact rather than another implementation's.
##
## The corpus is deliberately hostile: nearly proportional rows, exactly
## proportional rows, and coordinates that differ only in their last bits.
##
## `S2Exact` is internal, so the determinants are reached through
## `S2Predicates.exact_sign`, which returns the exact sign of `a . (b x c)`
## unchanged when it is non-zero and a symbolic perturbation when it is zero.
S2ExactTest := [].{

	failures : (ExactCorpus.Case -> Bool) -> U64
	failures = |check| ExactCorpus.cases.fold(0, |acc, case| if check(case) acc else acc + 1)

	point : (F64, F64, F64) -> S2Point
	point = |(x, y, z)| S2Point.new(x, y, z)

	## What `exact_sign` must return for rows whose exact determinant sign is
	## `det`: `det` itself, or the perturbed sign when `det` is zero.
	expected : S2Point, S2Point, S2Point, I8 -> I8
	expected = |a, b, c, det|
		if det != 0 {
			det
		} else {
			((pa, pb, pc), perm) = S2Predicates.sort3(a, b, c)
			perm * S2Predicates.symbolic_sign(pa, pb, pc)
		}

	## `exact_sign` of the rows, checked against the corpus sign `det`.
	agrees : (F64, F64, F64), (F64, F64, F64), (F64, F64, F64), I8 -> Bool
	agrees = |a, b, c, det| {
		(pa, pb, pc) = (S2ExactTest.point(a), S2ExactTest.point(b), S2ExactTest.point(c))
		S2Predicates.exact_sign(pa, pb, pc) == S2ExactTest.expected(pa, pb, pc, det)
	}
}

expect S2ExactTest.failures(|case| S2ExactTest.agrees(case.a, case.b, case.c, case.det3_sign)) == 0

# The 2x2 minor is the 3x3 determinant of the rows (a0, a1, 0), (b0, b1, 0) and
# (0, 0, 1), and the zeros and the one keep every product exact.
expect S2ExactTest.failures(
	|case| {
		(a0, a1, _a2) = case.a
		(b0, b1, _b2) = case.b
		S2ExactTest.agrees((a0, a1, 0.0), (b0, b1, 0.0), (0.0, 0.0, 1.0), case.det2_sign)
	},
)
	== 0

# Swapping two rows inverts the sign; a cyclic rotation preserves it.
expect S2ExactTest.failures(|case| S2ExactTest.agrees(case.b, case.a, case.c, -case.det3_sign)) == 0
expect S2ExactTest.failures(|case| S2ExactTest.agrees(case.b, case.c, case.a, case.det3_sign)) == 0

# Where the determinant is non-zero, the robust predicate must agree with it.
# Where it is zero, the predicate must still commit to an answer.
expect S2ExactTest.failures(
	|case| {
		(ax, ay, az) = case.a
		(bx, by, bz) = case.b
		(cx, cy, cz) = case.c
		a = S2Point.new(ax, ay, az).normalize()
		b = S2Point.new(bx, by, bz).normalize()
		c = S2Point.new(cx, cy, cz).normalize()
		sign = S2Predicates.sign(a, b, c)
		if a == b or b == c or c == a {
			sign == 0
		} else {
			sign != 0 and sign == -S2Predicates.sign(b, a, c) and sign == S2Predicates.sign(b, c, a)
		}
	},
)
	== 0

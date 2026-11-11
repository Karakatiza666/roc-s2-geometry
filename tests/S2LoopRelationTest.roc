import s2.S2LatLng
import s2.S2Loop
import s2.S2Point
import LoopRelationCorpus

## Checks the loop containment predicates against upstream's relation table.
##
## `LoopRelationCorpus` carries the loop pairs and the flags from
## `s2loop_test.cc`: which loop contains which, whether they are disjoint, and
## whether together they cover the sphere. What each flag implies about
## `contains`, `intersects`, `contains_nested`, `compare_boundary` and
## `boundary_equals` is re-derived here the way upstream derives it, and every
## pair is checked in all four combinations of the two loops with their
## complements.
##
## The table is worth reusing because of what is in it: hemispheres whose
## shared boundary is the whole equator, loops that touch at a single vertex,
## and loops that run along each other for several edges before parting. Those
## are the cases a containment predicate gets wrong.
S2LoopRelationTest := [].{

	loop_of : U8, List((F64, F64)) -> S2Loop
	loop_of = |kind, points| if kind == 1 {
		S2Loop.empty()
	} else if kind == 2 {
		S2Loop.full()
	} else {
		S2Loop.from_points(
			points.map(|(lat, lng)| S2LatLng.from_degrees(lat, lng).to_point()),
		)
	}

	## 0 when the claim holds, 1 when it does not.
	fault : Bool -> U64
	fault = |ok| if ok {
		0
	} else {
		1
	}

	## A pair where A contains B.
	one_nested : S2Loop, S2Loop -> U64
	one_nested = |a, b|
		S2LoopRelationTest.fault(a.contains(b))
			+ S2LoopRelationTest.fault(a.boundary_equals(b) == b.contains(a))
			+ S2LoopRelationTest.fault(!b.is_empty() == a.intersects(b))
			+ S2LoopRelationTest.fault(!b.is_empty() == b.intersects(a))

	## A pair sharing no interior point.
	one_disjoint : S2Loop, S2Loop -> U64
	one_disjoint = |a, b|
		S2LoopRelationTest.fault(!a.intersects(b))
			+ S2LoopRelationTest.fault(!b.intersects(a))
			+ S2LoopRelationTest.fault(b.is_empty() == a.contains(b))
			+ S2LoopRelationTest.fault(a.is_empty() == b.contains(a))

	## A pair whose union is the whole sphere.
	one_covering : S2Loop, S2Loop -> U64
	one_covering = |a, b| {
		# Two loops cover the sphere without overlapping only when one is the
		# complement of the other.
		complementary = a.invert().boundary_equals(b)
		S2LoopRelationTest.fault(a.is_full() == a.contains(b))
			+ S2LoopRelationTest.fault(b.is_full() == b.contains(a))
			+ S2LoopRelationTest.fault(!complementary == a.intersects(b))
			+ S2LoopRelationTest.fault(!complementary == b.intersects(a))
	}

	## A pair where each loop meets both the other and its complement.
	one_overlapping : S2Loop, S2Loop -> U64
	one_overlapping = |a, b|
		S2LoopRelationTest.fault(!a.contains(b))
			+ S2LoopRelationTest.fault(!b.contains(a))
			+ S2LoopRelationTest.fault(a.intersects(b))
			+ S2LoopRelationTest.fault(b.intersects(a))

	## A contains B, so B's complement contains A's, A's complement is
	## disjoint from B, and A together with B's complement covers the sphere.
	nested : S2Loop, S2Loop -> U64
	nested = |a, b|
		S2LoopRelationTest.one_nested(a, b)
			+ S2LoopRelationTest.one_nested(b.invert(), a.invert())
			+ S2LoopRelationTest.one_disjoint(a.invert(), b)
			+ S2LoopRelationTest.one_covering(a, b.invert())

	disjoint : S2Loop, S2Loop -> U64
	disjoint = |a, b| S2LoopRelationTest.nested(a.invert(), b)

	covering : S2Loop, S2Loop -> U64
	covering = |a, b| S2LoopRelationTest.nested(a, b.invert())

	overlapping : S2Loop, S2Loop -> U64
	overlapping = |a, b|
		S2LoopRelationTest.one_overlapping(a, b)
			+ S2LoopRelationTest.one_overlapping(a.invert(), b.invert())
			+ S2LoopRelationTest.one_overlapping(a.invert(), b)
			+ S2LoopRelationTest.one_overlapping(a, b.invert())

	## Every claim the flags on one case make.
	failures_of : LoopRelationCorpus.Case -> U64
	failures_of = |case| {
		a = S2LoopRelationTest.loop_of(case.a_kind, case.a)
		b = S2LoopRelationTest.loop_of(case.b_kind, case.b)
		contains = case.flags % 2 == 1
		contained = (case.flags / 2) % 2 == 1
		is_disjoint = (case.flags / 4) % 2 == 1
		covers = (case.flags / 8) % 2 == 1
		var $failures = 0
		if contains {
			$failures = $failures + S2LoopRelationTest.nested(a, b)
		}
		if contained {
			$failures = $failures + S2LoopRelationTest.nested(b, a)
		}
		if covers {
			$failures = $failures + S2LoopRelationTest.covering(a, b)
		}
		if is_disjoint {
			$failures = $failures + S2LoopRelationTest.disjoint(a, b)
		} else if !(contains or contained or covers) {
			$failures = $failures + S2LoopRelationTest.overlapping(a, b)
		}
		# The cheap nested test may only be asked about loops that are nested
		# or disjoint, and that share no edge.
		if !case.shared_edge and (contains or contained or is_disjoint) {
			$failures = $failures
				+ S2LoopRelationTest.fault(a.contains(b) == a.contains_nested(b))
		}
		# A holds B's boundary when it holds B, or when the two hold each
		# other's boundaries with no shared edge: at least one shared edge
		# must run the other way, and a reversed edge is not held.
		var $expected = 0
		if contains or (covers and !case.shared_edge) {
			$expected = 1
		}
		# Checked second because it wins: when both apply, A is held to
		# exclude the boundary.
		if is_disjoint or (contained and !case.shared_edge) {
			$expected = -1
		}
		if !a.is_empty() and !b.is_empty() {
			$failures = $failures
				+ S2LoopRelationTest.fault(a.compare_boundary(b, Bool.False) == $expected)
		}
		$failures
	}

	## The cases that fail any of their claims.
	failures : () -> U64
	failures = || LoopRelationCorpus.cases.fold(0, |acc, case| if (S2LoopRelationTest.failures_of(case) > 0) acc + 1 else acc)
}

expect LoopRelationCorpus.cases.len() == 86
expect S2LoopRelationTest.failures() == 0

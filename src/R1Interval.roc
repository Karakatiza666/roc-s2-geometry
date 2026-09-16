## A closed interval on the real line, `[lo, hi]`.
##
## An interval is empty when `lo > hi`; the canonical empty interval is
## `(1, 0)`, so that every empty interval compares equal to every other.
R1Interval := { lo : F64, hi : F64 }.{

	## The interval `[lo, hi]`, empty when `lo > hi`.
	new : F64, F64 -> R1Interval
	new = |lo, hi| { lo: lo, hi: hi }

	## The canonical empty interval.
	empty : () -> R1Interval
	empty = || { lo: 1.0, hi: 0.0 }

	## The interval containing exactly one point.
	from_point : F64 -> R1Interval
	from_point = |p| { lo: p, hi: p }

	## The smallest interval containing both points, in either order.
	from_point_pair : F64, F64 -> R1Interval
	from_point_pair = |a, b| if a <= b { lo: a, hi: b } else { lo: b, hi: a }

	lo : R1Interval -> F64
	lo = |i| i.lo

	hi : R1Interval -> F64
	hi = |i| i.hi

	## Bound `0` is `lo` and bound `1` is `hi`.
	bound : R1Interval, U64 -> F64
	bound = |i, k| if k == 0 i.lo else i.hi

	is_empty : R1Interval -> Bool
	is_empty = |i| i.lo > i.hi

	## The midpoint. Undefined for an empty interval.
	center : R1Interval -> F64
	center = |i| 0.5 * (i.lo + i.hi)

	## `hi - lo`, which is negative for an empty interval.
	length : R1Interval -> F64
	length = |i| i.hi - i.lo

	contains_point : R1Interval, F64 -> Bool
	contains_point = |i, p| p >= i.lo and p <= i.hi

	interior_contains_point : R1Interval, F64 -> Bool
	interior_contains_point = |i, p| p > i.lo and p < i.hi

	contains_interval : R1Interval, R1Interval -> Bool
	contains_interval = |i, other|
		if other.is_empty() {
			Bool.True
		} else {
			other.lo >= i.lo and other.hi <= i.hi
		}

	interior_contains_interval : R1Interval, R1Interval -> Bool
	interior_contains_interval = |i, other|
		if other.is_empty() {
			Bool.True
		} else {
			other.lo > i.lo and other.hi < i.hi
		}

	intersects : R1Interval, R1Interval -> Bool
	intersects = |i, other|
		if i.lo <= other.lo {
			other.lo <= i.hi and other.lo <= other.hi
		} else {
			i.lo <= other.hi and i.lo <= i.hi
		}

	interior_intersects : R1Interval, R1Interval -> Bool
	interior_intersects = |i, other|
		other.lo < i.hi and i.lo < other.hi and i.lo < i.hi and other.lo <= other.hi

	## The smallest interval containing both, which for disjoint intervals
	## also contains the gap between them.
	union : R1Interval, R1Interval -> R1Interval
	union = |i, other|
		if i.is_empty() {
			other
		} else if other.is_empty() {
			i
		} else {
			{ lo: i.lo.min(other.lo), hi: i.hi.max(other.hi) }
		}

	intersection : R1Interval, R1Interval -> R1Interval
	intersection = |i, other| { lo: i.lo.max(other.lo), hi: i.hi.min(other.hi) }

	## The smallest interval containing this one and the point.
	add_point : R1Interval, F64 -> R1Interval
	add_point = |i, p|
		if i.is_empty() {
			{ lo: p, hi: p }
		} else if p < i.lo {
			{ lo: p, hi: i.hi }
		} else if p > i.hi {
			{ lo: i.lo, hi: p }
		} else {
			i
		}

	## The closest point in the interval to `p`.
	project : R1Interval, F64 -> F64
	project = |i, p| p.max(i.lo).min(i.hi)

	## Widened by `radius` on both sides. A negative radius shrinks the
	## interval, and shrinking past empty yields the canonical empty interval.
	expanded : R1Interval, F64 -> R1Interval
	expanded = |i, radius| {
		if i.is_empty() {
			return i
		}
		widened = { lo: i.lo - radius, hi: i.hi + radius }
		if widened.lo > widened.hi {
			R1Interval.empty()
		} else {
			widened
		}
	}

	## The furthest any point of this interval is from the closest point of
	## `other`, or zero when `other` covers this one.
	directed_hausdorff_distance : R1Interval, R1Interval -> F64
	directed_hausdorff_distance = |i, other| {
		if i.is_empty() {
			0.0
		} else if other.is_empty() {
			F64.infinity
		} else {
			(i.hi - other.hi).max(other.lo - i.lo).max(0.0)
		}
	}

	## True when the bounds agree to within `max_error`, treating any two
	## empty intervals as equal.
	approx_eq : R1Interval, R1Interval, F64 -> Bool
	approx_eq = |i, other, max_error| {
		if i.is_empty() {
			other.length() <= 2.0 * max_error
		} else if other.is_empty() {
			i.length() <= 2.0 * max_error
		} else {
			(other.lo - i.lo).abs() <= max_error and (other.hi - i.hi).abs() <= max_error
		}
	}

	is_eq : R1Interval, R1Interval -> Bool
	is_eq = |i, other|
		(i.lo == other.lo and i.hi == other.hi) or (i.is_empty() and other.is_empty())

	to_inspect : R1Interval -> Str
	to_inspect = |i| "R1Interval(${i.lo.to_str()}, ${i.hi.to_str()})"
}

expect R1Interval.empty().is_empty()
expect R1Interval.new(3.0, 1.0).is_empty()
expect R1Interval.empty() == R1Interval.new(5.0, 2.0)
expect R1Interval.from_point(2.0).center() == 2.0
expect R1Interval.from_point_pair(4.0, 1.0) == R1Interval.new(1.0, 4.0)
expect R1Interval.new(0.0, 1.0).length() == 1.0
expect R1Interval.empty().length() < 0.0
expect R1Interval.new(0.0, 1.0).contains_point(0.0)
expect !R1Interval.new(0.0, 1.0).interior_contains_point(0.0)
expect R1Interval.new(0.0, 1.0).contains_interval(R1Interval.empty())
expect R1Interval.new(0.0, 1.0).contains_interval(R1Interval.new(0.2, 0.8))
expect !R1Interval.new(0.0, 1.0).interior_contains_interval(R1Interval.new(0.0, 0.8))
expect R1Interval.new(0.0, 1.0).intersects(R1Interval.new(1.0, 2.0))
expect !R1Interval.new(0.0, 1.0).interior_intersects(R1Interval.new(1.0, 2.0))
expect !R1Interval.new(0.0, 1.0).intersects(R1Interval.empty())
expect R1Interval.new(0.0, 1.0).union(R1Interval.new(2.0, 3.0)) == R1Interval.new(0.0, 3.0)
expect R1Interval.empty().union(R1Interval.new(2.0, 3.0)) == R1Interval.new(2.0, 3.0)
expect R1Interval.new(0.0, 2.0).intersection(R1Interval.new(1.0, 3.0)) == R1Interval.new(1.0, 2.0)
expect R1Interval.new(0.0, 1.0).intersection(R1Interval.new(2.0, 3.0)).is_empty()
expect R1Interval.new(1.0, 2.0).add_point(0.0) == R1Interval.new(0.0, 2.0)
expect R1Interval.empty().add_point(5.0) == R1Interval.from_point(5.0)
expect R1Interval.new(0.0, 1.0).project(2.0) == 1.0
expect R1Interval.new(0.0, 1.0).project(-2.0) == 0.0
expect R1Interval.new(0.0, 1.0).project(0.5) == 0.5
expect R1Interval.new(1.0, 2.0).expanded(0.5) == R1Interval.new(0.5, 2.5)
expect R1Interval.new(1.0, 2.0).expanded(-1.0).is_empty()
expect R1Interval.empty().expanded(1.0).is_empty()
expect R1Interval.new(0.0, 3.0).directed_hausdorff_distance(R1Interval.new(1.0, 2.0)) == 1.0
expect R1Interval.new(1.0, 2.0).directed_hausdorff_distance(R1Interval.new(0.0, 3.0)) == 0.0
expect R1Interval.new(0.0, 1.0).approx_eq(R1Interval.new(0.0, 1.0 + 1e-16), 1e-15)

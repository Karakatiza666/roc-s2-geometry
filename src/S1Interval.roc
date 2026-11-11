import Internal/S2Math

## A closed interval on the unit circle, with endpoints in `[-pi, pi]`.
##
## The interval runs counterclockwise from `lo` to `hi`, so an interval with
## `lo > hi` is *inverted*: it wraps through the +/-pi boundary. Two states are
## special-cased so that they stay distinguishable: the full interval is
## `(-pi, pi)` and the empty interval is `(pi, -pi)`.
S1Interval := { lo : F64, hi : F64 }.{

	## The interval from `lo` counterclockwise to `hi`.
	##
	## An endpoint of `-pi` is normalized to `pi` unless the other endpoint
	## is already `pi`, which keeps the full and empty intervals distinct.
	new : F64, F64 -> S1Interval
	new = |lo, hi| {
		clamped_lo = if (lo == -F64.pi and hi != F64.pi) F64.pi else lo
		clamped_hi = if (hi == -F64.pi and lo != F64.pi) F64.pi else hi
		{ lo: clamped_lo, hi: clamped_hi }
	}

	## The empty interval, `(pi, -pi)`.
	empty : () -> S1Interval
	empty = || { lo: F64.pi, hi: -F64.pi }

	## The whole circle, `(-pi, pi)`.
	full : () -> S1Interval
	full = || { lo: -F64.pi, hi: F64.pi }

	## The interval containing exactly one point.
	from_point : F64 -> S1Interval
	from_point = |p| {
		q = if (p == -F64.pi) F64.pi else p
		{ lo: q, hi: q }
	}

	## The shorter of the two intervals bounded by the pair of points.
	##
	## Ties go to the interval running counterclockwise from `a` to `b`.
	from_point_pair : F64, F64 -> S1Interval
	from_point_pair = |a, b| {
		na = if (a == -F64.pi) F64.pi else a
		nb = if (b == -F64.pi) F64.pi else b
		if positive_distance(na, nb) <= F64.pi {
			{ lo: na, hi: nb }
		} else {
			{ lo: nb, hi: na }
		}
	}

	lo : S1Interval -> F64
	lo = |i| i.lo

	hi : S1Interval -> F64
	hi = |i| i.hi

	## Bound `0` is `lo` and bound `1` is `hi`.
	bound : S1Interval, U64 -> F64
	bound = |i, k| if (k == 0) i.lo else i.hi

	## True when the interval wraps through the +/-pi boundary.
	is_inverted : S1Interval -> Bool
	is_inverted = |i| i.lo > i.hi

	is_empty : S1Interval -> Bool
	is_empty = |i| i.lo - i.hi == 2.0 * F64.pi

	is_full : S1Interval -> Bool
	is_full = |i| i.hi - i.lo == 2.0 * F64.pi

	## True when both endpoints lie in `[-pi, pi]` and the `-pi` endpoint
	## convention is respected.
	is_valid : S1Interval -> Bool
	is_valid = |i|
		i.lo.abs() <= F64.pi
			and i.hi.abs() <= F64.pi
			and !(i.lo == -F64.pi and i.hi != F64.pi)
			and !(i.hi == -F64.pi and i.lo != F64.pi)

	## The midpoint of the interval, in `[-pi, pi]`.
	center : S1Interval -> F64
	center = |i| {
		mid = 0.5 * (i.lo + i.hi)
		if !i.is_inverted() {
			mid
		} else if mid <= 0.0 {
			mid + F64.pi
		} else {
			mid - F64.pi
		}
	}

	## The angular width of the interval, in `[0, 2pi]`, or `-1` when empty.
	length : S1Interval -> F64
	length = |i| {
		direct = i.hi - i.lo
		if direct >= 0.0 {
			direct
		} else {
			wrapped = direct + 2.0 * F64.pi
			if wrapped > 0.0 {
				wrapped
			} else {
				-1.0
			}
		}
	}

	## `contains_point` without the `-pi` normalization, for callers that
	## already know `p` is in `[-pi, pi]` and not `-pi`.
	fast_contains_point : S1Interval, F64 -> Bool
	fast_contains_point = |i, p|
		if i.is_inverted() {
			(p >= i.lo or p <= i.hi) and !i.is_empty()
		} else {
			p >= i.lo and p <= i.hi
		}

	contains_point : S1Interval, F64 -> Bool
	contains_point = |i, p| {
		q = if (p == -F64.pi) F64.pi else p
		i.fast_contains_point(q)
	}

	interior_contains_point : S1Interval, F64 -> Bool
	interior_contains_point = |i, p| {
		q = if (p == -F64.pi) F64.pi else p
		if i.is_inverted() {
			q > i.lo or q < i.hi
		} else {
			(q > i.lo and q < i.hi) or i.is_full()
		}
	}

	contains_interval : S1Interval, S1Interval -> Bool
	contains_interval = |i, other|
		if i.is_inverted() {
			if other.is_inverted() {
				other.lo >= i.lo and other.hi <= i.hi
			} else {
				(other.lo >= i.lo or other.hi <= i.hi) and !i.is_empty()
			}
		} else if other.is_inverted() {
			i.is_full() or other.is_empty()
		} else {
			other.lo >= i.lo and other.hi <= i.hi
		}

	interior_contains_interval : S1Interval, S1Interval -> Bool
	interior_contains_interval = |i, other|
		if i.is_inverted() {
			if !other.is_inverted() {
				other.lo > i.lo or other.hi < i.hi
			} else {
				(other.lo > i.lo and other.hi < i.hi) or other.is_empty()
			}
		} else if other.is_inverted() {
			i.is_full() or other.is_empty()
		} else {
			(other.lo > i.lo and other.hi < i.hi) or i.is_full()
		}

	intersects : S1Interval, S1Interval -> Bool
	intersects = |i, other| {
		if i.is_empty() or other.is_empty() {
			return Bool.False
		}
		if i.is_inverted() {
			other.is_inverted() or other.lo <= i.hi or other.hi >= i.lo
		} else if other.is_inverted() {
			other.lo <= i.hi or other.hi >= i.lo
		} else {
			other.lo <= i.hi and other.hi >= i.lo
		}
	}

	interior_intersects : S1Interval, S1Interval -> Bool
	interior_intersects = |i, other| {
		if i.is_empty() or other.is_empty() or i.lo == i.hi {
			return Bool.False
		}
		if i.is_inverted() {
			other.is_inverted() or other.lo < i.hi or other.hi > i.lo
		} else if other.is_inverted() {
			other.lo < i.hi or other.hi > i.lo
		} else {
			(other.lo < i.hi and other.hi > i.lo) or i.is_full()
		}
	}

	## The complement of the interval's interior: the same boundary, but no
	## interior point in common.
	complement : S1Interval -> S1Interval
	complement = |i|
		if i.lo == i.hi {
			S1Interval.full()
		} else {
			S1Interval.new(i.hi, i.lo)
		}

	## The midpoint of the complement, which is the point furthest from the
	## interval.
	complement_center : S1Interval -> F64
	complement_center = |i|
		if i.lo != i.hi {
			i.complement().center()
		} else if i.hi <= 0.0 {
			i.hi + F64.pi
		} else {
			i.hi - F64.pi
		}

	## The smallest interval containing both, choosing the smaller of the two
	## candidate unions when the arguments are disjoint.
	union : S1Interval, S1Interval -> S1Interval
	union = |i, other| {
		if other.is_empty() {
			return i
		}
		if i.fast_contains_point(other.lo) {
			if i.fast_contains_point(other.hi) {
				if i.contains_interval(other) {
					return i
				}
				return S1Interval.full()
			}
			return { lo: i.lo, hi: other.hi }
		}
		if i.fast_contains_point(other.hi) {
			return { lo: other.lo, hi: i.hi }
		}
		if i.is_empty() or other.fast_contains_point(i.lo) {
			return other
		}
		dlo = positive_distance(other.hi, i.lo)
		dhi = positive_distance(i.hi, other.lo)
		if dlo < dhi {
			{ lo: other.lo, hi: i.hi }
		} else {
			{ lo: i.lo, hi: other.hi }
		}
	}

	## The intersection, which is the larger of the two pieces when the
	## arguments overlap at both ends.
	intersection : S1Interval, S1Interval -> S1Interval
	intersection = |i, other| {
		if other.is_empty() {
			return S1Interval.empty()
		}
		if i.fast_contains_point(other.lo) {
			if i.fast_contains_point(other.hi) {
				if other.length() < i.length() {
					return other
				}
				return i
			}
			return { lo: other.lo, hi: i.hi }
		}
		if i.fast_contains_point(other.hi) {
			return { lo: i.lo, hi: other.hi }
		}
		if other.fast_contains_point(i.lo) {
			return i
		}
		S1Interval.empty()
	}

	## The smallest interval containing this one and the point.
	add_point : S1Interval, F64 -> S1Interval
	add_point = |i, p| {
		q = if (p == -F64.pi) F64.pi else p
		if i.fast_contains_point(q) {
			return i
		}
		if i.is_empty() {
			return { lo: q, hi: q }
		}
		dlo = positive_distance(q, i.lo)
		dhi = positive_distance(i.hi, q)
		if dlo < dhi {
			{ lo: q, hi: i.hi }
		} else {
			{ lo: i.lo, hi: q }
		}
	}

	## The point of the interval closest to `p`.
	project : S1Interval, F64 -> F64
	project = |i, p| {
		q = if (p == -F64.pi) F64.pi else p
		if i.fast_contains_point(q) {
			return q
		}
		dlo = positive_distance(q, i.lo)
		dhi = positive_distance(i.hi, q)
		if dlo < dhi {
			i.lo
		} else {
			i.hi
		}
	}

	## Widened by `radius` on both sides, saturating at the full interval.
	## A negative radius shrinks the interval.
	##
	## As upstream does, the full and empty tests allow a rounding error of one
	## bit in each endpoint, so a result that rounding could make full or empty
	## is reported as full or empty.
	expanded : S1Interval, F64 -> S1Interval
	expanded = |i, radius| {
		if radius >= 0.0 {
			if i.is_empty() {
				return i
			}
			if i.length() + 2.0 * radius + 2.0 * 2.220446049250313e-16 >= 2.0 * F64.pi {
				return S1Interval.full()
			}
		} else {
			if i.is_full() {
				return i
			}
			if i.length() + 2.0 * radius - 2.0 * 2.220446049250313e-16 <= 0.0 {
				return S1Interval.empty()
			}
		}
		new_lo = S2Math.remainder(i.lo - radius, 2.0 * F64.pi)
		new_hi = S2Math.remainder(i.hi + radius, 2.0 * F64.pi)
		adjusted_lo = if (new_lo <= -F64.pi) F64.pi else new_lo
		S1Interval.new(adjusted_lo, new_hi)
	}

	## The furthest any point of this interval is from the closest point of
	## `other`.
	directed_hausdorff_distance : S1Interval, S1Interval -> F64
	directed_hausdorff_distance = |i, other| {
		if other.contains_interval(i) {
			return 0.0
		}
		if other.is_empty() {
			return F64.pi
		}
		other_complement_center = other.complement_center()
		if i.contains_point(other_complement_center) {
			return positive_distance(other.hi, other_complement_center)
		}
		hi_hi =
			if S1Interval.new(other.hi, other_complement_center).contains_point(i.hi) {
				positive_distance(other.hi, i.hi)
			} else {
				0.0
			}
		lo_lo =
			if S1Interval.new(other_complement_center, other.lo).contains_point(i.lo) {
				positive_distance(i.lo, other.lo)
			} else {
				0.0
			}
		hi_hi.max(lo_lo)
	}

	## True when the intervals agree to within `max_error`.
	##
	## An empty or full interval has no meaningful endpoints, so it is compared
	## by length. Otherwise both endpoints must agree to within `max_error`
	## and the lengths must agree to within `2 * max_error`, which rejects an
	## interval and its inversion that have the same endpoints.
	approx_eq : S1Interval, S1Interval, F64 -> Bool
	approx_eq = |i, other, max_error| {
		if i.is_empty() {
			other.length() <= 2.0 * max_error
		} else if other.is_empty() {
			i.length() <= 2.0 * max_error
		} else if i.is_full() {
			other.length() >= 2.0 * (F64.pi - max_error)
		} else if other.is_full() {
			i.length() >= 2.0 * (F64.pi - max_error)
		} else {
			S2Math.remainder(other.lo - i.lo, 2.0 * F64.pi).abs() <= max_error
				and S2Math.remainder(other.hi - i.hi, 2.0 * F64.pi).abs() <= max_error
				and (i.length() - other.length()).abs() <= 2.0 * max_error
		}
	}

	is_eq : S1Interval, S1Interval -> Bool
	is_eq = |i, other| i.lo == other.lo and i.hi == other.hi

	to_inspect : S1Interval -> Str
	to_inspect = |i| "S1Interval(${i.lo.to_str()}, ${i.hi.to_str()})"
}

expect S1Interval.empty().is_empty()
expect S1Interval.full().is_full()
expect !S1Interval.empty().is_full()
expect !S1Interval.full().is_empty()
expect S1Interval.empty().is_valid()
expect S1Interval.full().is_valid()
expect S1Interval.full().length() == 2.0 * F64.pi
expect S1Interval.empty().length() == -1.0
expect S1Interval.new(-F64.pi, -F64.pi) == S1Interval.new(F64.pi, F64.pi)
expect S1Interval.new(0.5 * F64.pi, -0.5 * F64.pi).is_inverted()
expect S1Interval.new(0.5 * F64.pi, -0.5 * F64.pi).center() == F64.pi
expect S1Interval.new(-0.5 * F64.pi, 0.5 * F64.pi).center() == 0.0
expect S1Interval.new(-0.5 * F64.pi, 0.5 * F64.pi).length() == F64.pi
expect S1Interval.new(0.5 * F64.pi, -0.5 * F64.pi).length() == F64.pi
expect S1Interval.from_point_pair(0.1, 0.2) == S1Interval.new(0.1, 0.2)
expect S1Interval.from_point_pair(0.2, 0.1) == S1Interval.new(0.1, 0.2)
expect S1Interval.from_point_pair(-F64.pi + 0.1, F64.pi - 0.1).is_inverted()
expect S1Interval.new(0.5 * F64.pi, -0.5 * F64.pi).contains_point(F64.pi)
expect S1Interval.new(0.5 * F64.pi, -0.5 * F64.pi).contains_point(-F64.pi)
expect !S1Interval.new(0.5 * F64.pi, -0.5 * F64.pi).contains_point(0.0)
expect S1Interval.full().contains_point(0.0)
expect !S1Interval.empty().contains_point(0.0)
expect S1Interval.new(0.0, 1.0).contains_interval(S1Interval.new(0.2, 0.8))
expect !S1Interval.new(0.0, 1.0).interior_contains_interval(S1Interval.new(0.0, 0.8))
expect S1Interval.new(0.0, 1.0).intersects(S1Interval.new(1.0, 2.0))
expect !S1Interval.new(0.0, 1.0).interior_intersects(S1Interval.new(1.0, 2.0))
expect S1Interval.new(0.0, 1.0).union(S1Interval.new(2.0, 3.0)) == S1Interval.new(0.0, 3.0)
expect S1Interval.new(0.0, 1.0).union(S1Interval.empty()) == S1Interval.new(0.0, 1.0)
expect S1Interval.new(0.0, 2.0).intersection(S1Interval.new(1.0, 3.0)) == S1Interval.new(1.0, 2.0)
expect S1Interval.new(0.0, 1.0).intersection(S1Interval.new(2.0, 3.0)).is_empty()
expect S1Interval.empty().add_point(1.0) == S1Interval.from_point(1.0)
expect S1Interval.new(0.0, 1.0).add_point(2.0) == S1Interval.new(0.0, 2.0)
expect S1Interval.new(0.0, 1.0).add_point(-1.0) == S1Interval.new(-1.0, 1.0)
expect S1Interval.new(0.0, 1.0).project(2.0) == 1.0
expect S1Interval.new(0.0, 1.0).project(0.5) == 0.5
expect S1Interval.new(0.2, 0.8).expanded(0.1).approx_eq(S1Interval.new(0.1, 0.9), 1e-15)
expect S1Interval.new(0.0, F64.pi).expanded(F64.pi).is_full()
expect S1Interval.empty().expanded(1.0).is_empty()
expect {
	# Two units in the last place below pi: rounding of the endpoints could
	# close the gap, so the expansion by zero is already full.
	S1Interval.new(-F64.pi, F64.pi - 8.881784197001252e-16).expanded(0.0).is_full()
}
expect S1Interval.new(0.0, 1.0).expanded(-0.49999999999999994).is_empty()
expect !S1Interval.new(0.0, 1.0).approx_eq(S1Interval.new(0.15, 1.0), 0.1)
expect S1Interval.new(0.0, 1.0).approx_eq(S1Interval.new(0.05, 0.95), 0.1)
expect !S1Interval.new(-3.0, 3.0).approx_eq(S1Interval.new(3.0, -3.0), 0.3)
expect S1Interval.full().approx_eq(S1Interval.new(-F64.pi, F64.pi - 0.01), 0.01)
expect S1Interval.empty().approx_eq(S1Interval.from_point(1.0), 0.01)
expect S1Interval.new(0.0, 1.0).complement() == S1Interval.new(1.0, 0.0)
expect S1Interval.from_point(0.0).complement().is_full()
expect S1Interval.new(0.0, 1.0).directed_hausdorff_distance(S1Interval.new(0.0, 1.0)) == 0.0

## The interval from `lo` to `hi` with no endpoint normalization.
##
## Only correct when both endpoints are known to be normalized already.
new_unchecked : F64, F64 -> S1Interval
new_unchecked = |lo, hi| { lo: lo, hi: hi }

## Counterclockwise distance from `a` to `b`, in `[0, 2pi)`.
positive_distance : F64, F64 -> F64
positive_distance = |a, b| {
	d = b - a
	if d >= 0.0 {
		d
	} else {
		(b + F64.pi) - (a - F64.pi)
	}
}

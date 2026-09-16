import R1Interval
import R2Point

## An axis-aligned rectangle in the plane, stored as an interval per axis.
##
## This is the bound S2 uses for the `(u, v)` extent of a cell on its cube
## face.
R2Rect := { x : R1Interval, y : R1Interval }.{

	## The rectangle spanning the two given intervals.
	new : R1Interval, R1Interval -> R2Rect
	new = |x, y| { x: x, y: y }

	## The rectangle spanning `[lo.x, hi.x] x [lo.y, hi.y]`, empty when either
	## axis is inverted.
	from_bounds : R2Point, R2Point -> R2Rect
	from_bounds = |lo, hi| {
		x: R1Interval.new(lo.x(), hi.x()),
		y: R1Interval.new(lo.y(), hi.y()),
	}

	## The smallest rectangle containing both points.
	from_point_pair : R2Point, R2Point -> R2Rect
	from_point_pair = |a, b| {
		x: R1Interval.from_point_pair(a.x(), b.x()),
		y: R1Interval.from_point_pair(a.y(), b.y()),
	}

	## The rectangle containing exactly one point.
	from_point : R2Point -> R2Rect
	from_point = |p| { x: R1Interval.from_point(p.x()), y: R1Interval.from_point(p.y()) }

	## The rectangle of the given size centred on `center`.
	from_center_size : R2Point, R2Point -> R2Rect
	from_center_size = |center, size| {
		x: R1Interval.new(center.x() - 0.5 * size.x(), center.x() + 0.5 * size.x()),
		y: R1Interval.new(center.y() - 0.5 * size.y(), center.y() + 0.5 * size.y()),
	}

	empty : () -> R2Rect
	empty = || { x: R1Interval.empty(), y: R1Interval.empty() }

	x : R2Rect -> R1Interval
	x = |r| r.x

	y : R2Rect -> R1Interval
	y = |r| r.y

	## Interval `0` is the x interval and interval `1` is the y interval.
	interval : R2Rect, U64 -> R1Interval
	interval = |r, k| if k == 0 r.x else r.y

	## The lower-left corner.
	lo : R2Rect -> R2Point
	lo = |r| R2Point.new(r.x.lo(), r.y.lo())

	## The upper-right corner.
	hi : R2Rect -> R2Point
	hi = |r| R2Point.new(r.x.hi(), r.y.hi())

	## The `k`-th vertex, counterclockwise from the lower-left corner.
	vertex : R2Rect, U64 -> R2Point
	vertex = |r, k| {
		j = k.shr_zf_wrap(1).bitwise_and(1)
		i = j.bitwise_xor(k.bitwise_and(1))
		R2Point.new(r.x.bound(i), r.y.bound(j))
	}

	## The vertex at x bound `i` and y bound `j`.
	vertex_ij : R2Rect, U64, U64 -> R2Point
	vertex_ij = |r, i, j| R2Point.new(r.x.bound(i), r.y.bound(j))

	## True when both intervals are empty or both are non-empty.
	is_valid : R2Rect -> Bool
	is_valid = |r| r.x.is_empty() == r.y.is_empty()

	is_empty : R2Rect -> Bool
	is_empty = |r| r.x.is_empty()

	center : R2Rect -> R2Point
	center = |r| R2Point.new(r.x.center(), r.y.center())

	## The width and height of the rectangle.
	size : R2Rect -> R2Point
	size = |r| R2Point.new(r.x.length(), r.y.length())

	contains_point : R2Rect, R2Point -> Bool
	contains_point = |r, p| r.x.contains_point(p.x()) and r.y.contains_point(p.y())

	interior_contains_point : R2Rect, R2Point -> Bool
	interior_contains_point = |r, p|
		r.x.interior_contains_point(p.x()) and r.y.interior_contains_point(p.y())

	contains_rect : R2Rect, R2Rect -> Bool
	contains_rect = |r, other|
		r.x.contains_interval(other.x) and r.y.contains_interval(other.y)

	interior_contains_rect : R2Rect, R2Rect -> Bool
	interior_contains_rect = |r, other|
		r.x.interior_contains_interval(other.x) and r.y.interior_contains_interval(other.y)

	intersects : R2Rect, R2Rect -> Bool
	intersects = |r, other| r.x.intersects(other.x) and r.y.intersects(other.y)

	interior_intersects : R2Rect, R2Rect -> Bool
	interior_intersects = |r, other|
		r.x.interior_intersects(other.x) and r.y.interior_intersects(other.y)

	add_point : R2Rect, R2Point -> R2Rect
	add_point = |r, p| { x: r.x.add_point(p.x()), y: r.y.add_point(p.y()) }

	add_rect : R2Rect, R2Rect -> R2Rect
	add_rect = |r, other| { x: r.x.union(other.x), y: r.y.union(other.y) }

	## The point of the rectangle closest to `p`.
	project : R2Rect, R2Point -> R2Point
	project = |r, p| R2Point.new(r.x.project(p.x()), r.y.project(p.y()))

	## Widened by `margin.x` horizontally and `margin.y` vertically.
	expanded : R2Rect, R2Point -> R2Rect
	expanded = |r, margin| {
		xx = r.x.expanded(margin.x())
		yy = r.y.expanded(margin.y())
		if xx.is_empty() or yy.is_empty() {
			R2Rect.empty()
		} else {
			{ x: xx, y: yy }
		}
	}

	## Widened by the same margin on all four sides.
	expanded_by : R2Rect, F64 -> R2Rect
	expanded_by = |r, margin| r.expanded(R2Point.new(margin, margin))

	union : R2Rect, R2Rect -> R2Rect
	union = |r, other| { x: r.x.union(other.x), y: r.y.union(other.y) }

	intersection : R2Rect, R2Rect -> R2Rect
	intersection = |r, other| {
		xx = r.x.intersection(other.x)
		yy = r.y.intersection(other.y)
		if xx.is_empty() or yy.is_empty() {
			R2Rect.empty()
		} else {
			{ x: xx, y: yy }
		}
	}

	approx_eq : R2Rect, R2Rect, F64 -> Bool
	approx_eq = |r, other, max_error|
		r.x.approx_eq(other.x, max_error) and r.y.approx_eq(other.y, max_error)

	is_eq : R2Rect, R2Rect -> Bool
	is_eq = |r, other| r.x == other.x and r.y == other.y

	to_inspect : R2Rect -> Str
	to_inspect = |r| "R2Rect(${r.x.to_inspect()}, ${r.y.to_inspect()})"
}

expect R2Rect.empty().is_empty()
expect R2Rect.empty().is_valid()
expect R2Rect.from_point(R2Point.new(1.0, 2.0)).center() == R2Point.new(1.0, 2.0)
expect R2Rect.from_point_pair(R2Point.new(3.0, 4.0), R2Point.new(1.0, 2.0))
	== R2Rect.from_bounds(R2Point.new(1.0, 2.0), R2Point.new(3.0, 4.0))
expect R2Rect.from_center_size(R2Point.new(0.0, 0.0), R2Point.new(2.0, 4.0))
	== R2Rect.from_bounds(R2Point.new(-1.0, -2.0), R2Point.new(1.0, 2.0))
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0)).size()
	== R2Point.new(1.0, 1.0)
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0)).vertex(0)
	== R2Point.new(0.0, 0.0)
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0)).vertex(1)
	== R2Point.new(1.0, 0.0)
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0)).vertex(2)
	== R2Point.new(1.0, 1.0)
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0)).vertex(3)
	== R2Point.new(0.0, 1.0)
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.contains_point(R2Point.new(0.5, 0.5))
expect !R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.interior_contains_point(R2Point.new(0.0, 0.5))
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(2.0, 2.0))
	.contains_rect(R2Rect.from_bounds(R2Point.new(0.5, 0.5), R2Point.new(1.0, 1.0)))
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.intersects(R2Rect.from_bounds(R2Point.new(1.0, 1.0), R2Point.new(2.0, 2.0)))
expect !R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.interior_intersects(R2Rect.from_bounds(R2Point.new(1.0, 1.0), R2Point.new(2.0, 2.0)))
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.project(R2Point.new(5.0, -5.0)) == R2Point.new(1.0, 0.0)
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0)).expanded_by(1.0)
	== R2Rect.from_bounds(R2Point.new(-1.0, -1.0), R2Point.new(2.0, 2.0))
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.expanded_by(-1.0).is_empty()
expect R2Rect.from_point(R2Point.new(0.0, 0.0)).add_point(R2Point.new(1.0, 1.0))
	== R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
expect R2Rect.from_bounds(R2Point.new(0.0, 0.0), R2Point.new(1.0, 1.0))
	.intersection(R2Rect.from_bounds(R2Point.new(2.0, 2.0), R2Point.new(3.0, 3.0)))
	.is_empty()

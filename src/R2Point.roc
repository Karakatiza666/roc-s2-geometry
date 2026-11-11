## A point in the plane, used for the `(u, v)` and `(s, t)` coordinates of a
## cube face.
R2Point := { x : F64, y : F64 }.{

	## The point with the given `x` and `y` coordinates.
	new : F64, F64 -> R2Point
	new = |x, y| { x: x, y: y }

	## The point `(0, 0)`.
	origin : () -> R2Point
	origin = || { x: 0.0, y: 0.0 }

	## The x coordinate.
	x : R2Point -> F64
	x = |p| p.x

	## The y coordinate.
	y : R2Point -> F64
	y = |p| p.y

	## Coordinate `0` is `x` and coordinate `1` is `y`.
	coord : R2Point, U64 -> F64
	coord = |p, k| if (k == 0) p.x else p.y

	## Adds the coordinates. Written `a + b`.
	plus : R2Point, R2Point -> R2Point
	plus = |a, b| { x: a.x + b.x, y: a.y + b.y }

	## Subtracts the coordinates of `b` from those of `a`. Written `a - b`.
	minus : R2Point, R2Point -> R2Point
	minus = |a, b| { x: a.x - b.x, y: a.y - b.y }

	## Scales the point. Written `p * 2.0`.
	times : R2Point, F64 -> R2Point
	times = |p, k| { x: p.x * k, y: p.y * k }

	## Divides both coordinates by `k`. Written `p / k`.
	div_by : R2Point, F64 -> R2Point
	div_by = |p, k| { x: p.x / k, y: p.y / k }

	## The point with both coordinates negated. Written `-p`.
	negate : R2Point -> R2Point
	negate = |p| { x: -p.x, y: -p.y }

	## The dot product of the two points, taken as vectors.
	dot : R2Point, R2Point -> F64
	dot = |a, b| a.x * b.x + a.y * b.y

	## The z-component of the 3D cross product, positive when `b` is
	## counterclockwise from `a`.
	cross : R2Point, R2Point -> F64
	cross = |a, b| a.x * b.y - a.y * b.x

	## The squared length of the point, taken as a vector.
	norm2 : R2Point -> F64
	norm2 = |p| p.x * p.x + p.y * p.y

	## The length of the point, taken as a vector.
	norm : R2Point -> F64
	norm = |p| p.norm2().sqrt()

	## The unit vector in the same direction, or the origin when the point is
	## the origin.
	normalize : R2Point -> R2Point
	normalize = |p| {
		n = p.norm()
		if n == 0.0 {
			p
		} else {
			{ x: p.x / n, y: p.y / n }
		}
	}

	## The point rotated 90 degrees counterclockwise.
	ortho : R2Point -> R2Point
	ortho = |p| { x: -p.y, y: p.x }

	is_eq : R2Point, R2Point -> Bool
	is_eq = |a, b| a.x == b.x and a.y == b.y

	## True when the two points are within `max_error` of each other.
	approx_eq : R2Point, R2Point, F64 -> Bool
	approx_eq = |a, b, max_error| (a - b).norm() <= max_error

	to_inspect : R2Point -> Str
	to_inspect = |p| "R2Point(${p.x.to_str()}, ${p.y.to_str()})"
}

expect R2Point.new(1.0, 2.0).x() == 1.0
expect R2Point.new(1.0, 2.0).coord(1) == 2.0
expect R2Point.new(1.0, 2.0) + R2Point.new(3.0, 4.0) == R2Point.new(4.0, 6.0)
expect R2Point.new(3.0, 4.0) - R2Point.new(1.0, 2.0) == R2Point.new(2.0, 2.0)
expect R2Point.new(1.0, 2.0) * 3.0 == R2Point.new(3.0, 6.0)
expect R2Point.new(3.0, 6.0) / 3.0 == R2Point.new(1.0, 2.0)
expect -R2Point.new(1.0, 2.0) == R2Point.new(-1.0, -2.0)
expect R2Point.new(1.0, 2.0).dot(R2Point.new(3.0, 4.0)) == 11.0
expect R2Point.new(1.0, 0.0).cross(R2Point.new(0.0, 1.0)) == 1.0
expect R2Point.new(3.0, 4.0).norm() == 5.0
expect R2Point.new(3.0, 4.0).normalize().norm() == 1.0
expect R2Point.origin().normalize() == R2Point.origin()
expect R2Point.new(1.0, 0.0).ortho() == R2Point.new(0.0, 1.0)

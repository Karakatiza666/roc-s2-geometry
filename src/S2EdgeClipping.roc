import R1Interval
import R2Point
import R2Rect
import S2Coords
import S2Point

## Clips geodesic edges to the faces of the cube, and edges in the plane of a
## face to rectangles. Upstream's `s2edge_clipping.h`.
##
## An edge between two unit-length points can cross several cube faces. On
## each face its part is a straight line in `(u, v)` coordinates, which the
## functions here find with an error bound that the constants below give.
## Upstream returns a `bool` and writes its results through pointers. These
## functions return `Ok` with the results, or `Err(NoIntersection)` where
## upstream returns `false`.
S2EdgeClipping := [].{

	## The part of an edge on one cube face: the face, and the `(u, v)`
	## coordinates of where the part starts and ends.
	FaceSegment : { face : U64, a : R2Point, b : R2Point }

	## An upper bound on the distance from a point that `get_face_segments` or
	## `clip_to_padded_face` gives to the edge, in radians: `3` epsilon.
	face_clip_error_radians : F64
	face_clip_error_radians = 3.0 * f64_epsilon

	## The same bound as a distance in `(u, v)` coordinates: `9` epsilon.
	face_clip_error_uv_dist : F64
	face_clip_error_uv_dist = 9.0 * f64_epsilon

	## The same bound for each `(u, v)` coordinate separately:
	## `9 / sqrt(2)` epsilon.
	face_clip_error_uv_coord : F64
	face_clip_error_uv_coord = 9.0 * sqrt1_2 * f64_epsilon

	## An upper bound on the distance from an edge to a rectangle for which
	## `intersects_rect` can give a wrong answer, in `(u, v)` coordinates:
	## `3 * sqrt(2)` epsilon.
	intersects_rect_error_uv_dist : F64
	intersects_rect_error_uv_dist = 3.0 * sqrt2 * f64_epsilon

	## An upper bound on the error in each coordinate of a point that
	## `clip_edge` gives: `2.25` epsilon.
	edge_clip_error_uv_coord : F64
	edge_clip_error_uv_coord = 2.25 * f64_epsilon

	## An upper bound on the distance from a point that `clip_edge` gives to
	## the edge: `2.25` epsilon.
	edge_clip_error_uv_dist : F64
	edge_clip_error_uv_dist = 2.25 * f64_epsilon

	## The parts of the edge `ab` on each cube face it crosses, in order from
	## `a` to `b`. Both points must be unit length.
	##
	## The first part starts at `a` and the last ends at `b`. Each part ends
	## on the boundary of its face where the next part starts. The result is
	## within `face_clip_error_uv_coord` of the true parts, and it never
	## skips a face, so consecutive parts are on adjacent faces.
	get_face_segments : S2Point, S2Point -> List(FaceSegment)
	get_face_segments = |a, b| {
		(a_face0, a_uv0) = S2Coords.xyz_to_face_uv(a)
		(b_face0, b_uv0) = S2Coords.xyz_to_face_uv(b)
		if a_face0 == b_face0 {
			return [{ face: a_face0, a: a_uv0, b: b_uv0 }]
		}
		# The normal of the plane through a and b defines the edge. The
		# endpoints move to faces that the plane crosses, if rounding put them
		# on a face it misses.
		ab = a.robust_cross(b)
		(a_face, a_uv) = move_origin_to_valid_face(a_face0, a, ab, a_uv0)
		(b_face, b_uv) = move_origin_to_valid_face(b_face0, b, -ab, b_uv0)

		var $segments = []
		var $face = a_face
		var $start = a_uv
		# A great circle crosses at most four faces, so the bound only guards
		# against a loop on input that is not unit length.
		var $steps = 0.U64
		while $face != b_face and $steps < 12 {
			$steps = $steps + 1
			n = S2Coords.face_xyz_to_uvw($face, ab)
			exit_axis = get_exit_axis(n)
			exit = get_exit_point(n, exit_axis)
			$segments = $segments.append({ face: $face, a: $start, b: exit })
			exit_xyz = S2Coords.face_uv_to_xyz($face, exit.x(), exit.y())
			$face = get_next_face($face, exit, exit_axis, n, b_face)
			exit_uvw = S2Coords.face_xyz_to_uvw($face, exit_xyz)
			$start = R2Point.new(exit_uvw.x(), exit_uvw.y())
		}
		$segments.append({ face: $face, a: $start, b: b_uv })
	}

	## The part of the edge `ab` on the given face, as the `(u, v)`
	## coordinates of its two ends, or `Err(NoIntersection)` when the edge
	## does not cross the face. Both points must be unit length.
	##
	## Each result is within `face_clip_error_uv_coord` of the true one.
	clip_to_face : S2Point, S2Point, U64 -> Try((R2Point, R2Point), [NoIntersection])
	clip_to_face = |a, b, face| S2EdgeClipping.clip_to_padded_face(a, b, face, 0.0)

	## Like `clip_to_face`, but the face is the square `[-R, R] x [-R, R]`
	## with `R = 1 + padding`, so that parts just beyond the face boundary are
	## kept too. The padding must not be negative.
	clip_to_padded_face : S2Point, S2Point, U64, F64 -> Try((R2Point, R2Point), [NoIntersection])
	clip_to_padded_face = |a_xyz, b_xyz, face, padding| {
		if S2Coords.face_of(a_xyz) == face and S2Coords.face_of(b_xyz) == face {
			return Ok((S2Coords.valid_face_xyz_to_uv(face, a_xyz), S2Coords.valid_face_xyz_to_uv(face, b_xyz)))
		}
		# The cross product must come from the (x, y, z) frame, since
		# robust_cross can give different results in another frame for
		# proportional inputs.
		n0 = S2Coords.face_xyz_to_uvw(face, a_xyz.robust_cross(b_xyz))
		a = S2Coords.face_xyz_to_uvw(face, a_xyz)
		b = S2Coords.face_xyz_to_uvw(face, b_xyz)

		# Scaling the u and v components of the normal by R tests against the
		# padded face with no other change.
		scale_uv = 1.0 + padding
		scaled_n = S2Point.new(scale_uv * n0.x(), scale_uv * n0.y(), n0.z())
		if !intersects_face(scaled_n) {
			return Err(NoIntersection)
		}
		n = n0.normalize()
		a_tangent = n.cross(a)
		b_tangent = b.cross(n)
		# When the scores of the two ends add up to 3 or more, the edge misses
		# the face.
		(a_score, a_uv) = clip_destination(b, a, -scaled_n, b_tangent, a_tangent, scale_uv)
		(b_score, b_uv) = clip_destination(a, b, scaled_n, a_tangent, b_tangent, scale_uv)
		if a_score + b_score < 3 {
			Ok((a_uv, b_uv))
		} else {
			Err(NoIntersection)
		}
	}

	## True when the edge `ab` in the plane meets the rectangle. The answer
	## is exact for the given doubles, and so correct for any edge and
	## rectangle further apart than `intersects_rect_error_uv_dist`.
	intersects_rect : R2Point, R2Point, R2Rect -> Bool
	intersects_rect = |a, b, rect| {
		if !rect.intersects(R2Rect.from_point_pair(a, b)) {
			return Bool.False
		}
		# The edge meets the rectangle unless all four vertices are on the
		# same side of its line. The two vertices with the largest and the
		# smallest projection on its normal decide.
		n = (b - a).ortho()
		i = if (n.x() >= 0.0) 1 else 0
		j = if (n.y() >= 0.0) 1 else 0
		max = n.dot(rect.vertex_ij(i, j) - a)
		min = n.dot(rect.vertex_ij(1 - i, 1 - j) - a)
		max >= 0.0 and min <= 0.0
	}

	## The part of the edge `ab` in the plane that lies inside the rectangle
	## `clip`, as its two ends, or `Err(NoIntersection)` when there is none.
	##
	## Each coordinate of the result is within `edge_clip_error_uv_coord` of
	## the true one. An edge that just touches the rectangle may be kept or
	## dropped.
	clip_edge : R2Point, R2Point, R2Rect -> Try((R2Point, R2Point), [NoIntersection])
	clip_edge = |a, b, clip| {
		bound = S2EdgeClipping.clip_edge_bound(a, b, clip, R2Rect.from_point_pair(a, b))?
		ai = if (a.x() > b.x()) 1 else 0
		aj = if (a.y() > b.y()) 1 else 0
		Ok((bound.vertex_ij(ai, aj), bound.vertex_ij(1 - ai, 1 - aj)))
	}

	## The bounding rectangle of the part of the edge `ab` inside `clip`, or
	## the empty rectangle when there is none.
	get_clipped_edge_bound : R2Point, R2Point, R2Rect -> R2Rect
	get_clipped_edge_bound = |a, b, clip|
		S2EdgeClipping.clip_edge_bound(a, b, clip, R2Rect.from_point_pair(a, b)) ?? R2Rect.empty()

	## Shrinks `bound`, a bound of some part of the edge `ab`, to a bound of
	## the part of it inside `clip`. Gives `Err(NoIntersection)` when that
	## part is empty.
	##
	## `bound` must be the bound of a part of the line through `a` and `b`,
	## for example `R2Rect.from_point_pair(a, b)` or the result of an earlier
	## clip. Clipping the same edge to several rectangles in turn this way
	## gives a smaller error than clipping the edge itself, because the
	## errors do not add up.
	clip_edge_bound : R2Point, R2Point, R2Rect, R2Rect -> Try(R2Rect, [NoIntersection])
	clip_edge_bound = |a, b, clip, bound| {
		# Which diagonal of the bound the edge spans: 0 for a positive slope,
		# 1 for a negative one.
		diag = if ((a.x() > b.x()) != (a.y() > b.y())) 1 else 0
		(x1, y1) = clip_bound_axis(a.x(), b.x(), bound.x(), a.y(), b.y(), bound.y(), diag, clip.x())?
		(y2, x2) = clip_bound_axis(a.y(), b.y(), y1, a.x(), b.x(), x1, diag, clip.y())?
		Ok(R2Rect.new(x2, y2))
	}

	## The value at `x` of the linear function that is `a1` at `a` and `b1`
	## at `b`. The nearer of `a` and `b` to `x` is the base of the
	## interpolation, which makes the result exact at both ends. When
	## `a == b`, it is `a1`.
	interpolate_double : F64, F64, F64, F64, F64 -> F64
	interpolate_double = |x, a, b, a1, b1|
		if a == b {
			a1
		} else if (a - x).abs() <= (b - x).abs() {
			a1 + (b1 - a1) * ((x - a) / (b - a))
		} else {
			b1 + (a1 - b1) * ((x - b) / (a - b))
		}
}

## `F64` machine epsilon.
f64_epsilon : F64
f64_epsilon = 2.220446049250313e-16

## The square root of 2.
sqrt2 : F64
sqrt2 = 1.4142135623730951

## The square root of 1/2.
sqrt1_2 : F64
sqrt1_2 = 0.7071067811865476

## True when `u + v == w` exactly, from three rounded comparisons.
sum_equals : F64, F64, F64 -> Bool
sum_equals = |u, v, w| u + v == w and u == w - v and v == w - u

## True when the line with normal `n`, in the `(u, v, w)` frame of a face,
## crosses the face: when `|nu| + |nv| >= |nw|`, evaluated exactly.
intersects_face : S2Point -> Bool
intersects_face = |n| {
	u = n.x().abs()
	v = n.y().abs()
	w = n.z().abs()
	v >= w - u and u >= w - v
}

## True when the line with normal `n`, which crosses the face, crosses two
## opposite edges of it, or passes through a corner: when
## `||nu| - |nv|| >= |nw|`, evaluated exactly.
intersects_opposite_edges : S2Point -> Bool
intersects_opposite_edges = |n| {
	u = n.x().abs()
	v = n.y().abs()
	w = n.z().abs()
	if (u - v).abs() != w {
		(u - v).abs() >= w
	} else if u >= v {
		u - w >= v
	} else {
		v - w >= u
	}
}

## The axis of the face edge where the line with normal `n` leaves the face:
## `0` for the `u = -1` or `u = 1` edge, and `1` for a `v` edge.
get_exit_axis : S2Point -> U64
get_exit_axis = |n|
	if intersects_opposite_edges(n) {
		if (n.x().abs() >= n.y().abs()) 1 else 0
	} else {
		# The sign bits rather than a product, which could underflow.
		signs = sign_bit(n.x()).bitwise_xor(sign_bit(n.y())).bitwise_xor(sign_bit(n.z()))
		if (signs == 0) 1 else 0
	}

## `1` when the sign bit of `x` is set, `0` otherwise.
sign_bit : F64 -> U64
sign_bit = |x| x.to_bits().shr_zf_wrap(63)

## The `(u, v)` point where the line with normal `n` leaves the face across
## the edge of the given axis.
get_exit_point : S2Point, U64 -> R2Point
get_exit_point = |n, axis|
	if axis == 0 {
		u = if (n.y() > 0.0) 1.0 else -1.0
		R2Point.new(u, (-u * n.x() - n.z()) / n.y())
	} else {
		v = if (n.x() < 0.0) 1.0 else -1.0
		R2Point.new((-v * n.y() - n.z()) / n.x(), v)
	}

## The face where the edge with normal `ab` starts, given the face that `a`
## projects onto and its `(u, v)` there.
##
## The normal is rounded, so its plane can miss that face, or leave it on the
## wrong side of `a`. Then `a` moves to the adjacent face that the plane
## passes nearest, which moves it by less than the clipping error.
move_origin_to_valid_face : U64, S2Point, S2Point, R2Point -> (U64, R2Point)
move_origin_to_valid_face = |face, a, ab, a_uv| {
	max_safe_uv_coord = 1.0 - S2EdgeClipping.face_clip_error_uv_coord
	if a_uv.x().abs().max(a_uv.y().abs()) <= max_safe_uv_coord {
		return (face, a_uv)
	}
	n = S2Coords.face_xyz_to_uvw(face, ab)
	if intersects_face(n) {
		exit_uv = get_exit_point(n, get_exit_axis(n))
		exit = S2Coords.face_uv_to_xyz(face, exit_uv.x(), exit_uv.y())
		a_tangent = ab.normalize().cross(a)
		if (exit - a).dot(a_tangent) >= -S2EdgeClipping.face_clip_error_radians {
			return (face, a_uv)
		}
	}
	new_face =
		if a_uv.x().abs() >= a_uv.y().abs() {
			S2Coords.uvw_face(face, 0, if (a_uv.x() > 0.0) 1 else 0)
		} else {
			S2Coords.uvw_face(face, 1, if (a_uv.y() > 0.0) 1 else 0)
		}
	uv = S2Coords.valid_face_xyz_to_uv(new_face, a)
	clamp = |c| c.min(1.0).max(-1.0)
	(new_face, R2Point.new(clamp(uv.x()), clamp(uv.y())))
}

## The next face that the edge with normal `n` enters after leaving `face` at
## `exit` across the edge of axis `axis`. When it leaves exactly through a
## corner and one of the two faces there is `target_face`, which holds the
## end of the edge, that face is the next one.
get_next_face : U64, R2Point, U64, S2Point, U64 -> U64
get_next_face = |face, exit, axis, n, target_face| {
	other = exit.coord(1 - axis)
	if
		other.abs() == 1.0
			and S2Coords.uvw_face(face, 1 - axis, if (other > 0.0) 1 else 0) == target_face
			and sum_equals(exit.x() * n.x(), exit.y() * n.y(), -n.z())
			{
				target_face
			} else {
		S2Coords.uvw_face(face, axis, if (exit.coord(axis) > 0.0) 1 else 0)
	}
}

## Clips the edge `ab`, in the `(u, v, w)` frame of a face, at the end `b`:
## the `(u, v)` of `b` when it is safely inside the face, else of the point
## where the edge leaves the face, else of `b`.
##
## Also gives a score from 0 to 3 for whether the edge misses the face. When
## the scores of the two ends add up to 3 or more, it does.
clip_destination : S2Point, S2Point, S2Point, S2Point, S2Point, F64 -> (U64, R2Point)
clip_destination = |a, b, scaled_n, a_tangent, b_tangent, scale_uv| {
	max_safe_uv_coord = 1.0 - S2EdgeClipping.face_clip_error_uv_coord
	if b.z() > 0.0 {
		uv = R2Point.new(b.x() / b.z(), b.y() / b.z())
		if uv.x().abs().max(uv.y().abs()) <= max_safe_uv_coord {
			return (0, uv)
		}
	}
	exit = get_exit_point(scaled_n, get_exit_axis(scaled_n)) * scale_uv
	p = S2Point.new(exit.x(), exit.y(), 1.0)
	# 2 when the exit point is on the wrong side of a, 1 when it is on the
	# wrong side of b. Then the end b is the clipped end, if it projects onto
	# the face at all.
	score =
		if (p - a).dot(a_tangent) < 0.0 {
			2
		} else if (p - b).dot(b_tangent) < 0.0 {
			1
		} else {
			0
		}
	if score == 0 {
		(0, exit)
	} else if b.z() <= 0.0 {
		(3, exit)
	} else {
		(score, R2Point.new(b.x() / b.z(), b.y() / b.z()))
	}
}

## Moves an end of `bound0`, the bound of a part of the edge from `(a0, a1)`
## to `(b0, b1)` along one axis, inside `clip0`, and the matching end of
## `bound1` along the other axis with it. `diag` is which diagonal the edge
## spans. Gives the two bounds, or `Err(NoIntersection)` when nothing is left.
clip_bound_axis : F64, F64, R1Interval, F64, F64, R1Interval, U64, R1Interval -> Try((R1Interval, R1Interval), [NoIntersection])
clip_bound_axis = |a0, b0, bound0, a1, b1, bound1, diag, clip0| {
	var $bound0 = bound0
	var $bound1 = bound1
	if $bound0.lo() < clip0.lo() {
		if $bound0.hi() < clip0.lo() {
			return Err(NoIntersection)
		}
		$bound0 = R1Interval.new(clip0.lo(), $bound0.hi())
		$bound1 = update_endpoint($bound1, diag, S2EdgeClipping.interpolate_double(clip0.lo(), a0, b0, a1, b1))?
	}
	if $bound0.hi() > clip0.hi() {
		if $bound0.lo() > clip0.hi() {
			return Err(NoIntersection)
		}
		$bound0 = R1Interval.new($bound0.lo(), clip0.hi())
		$bound1 = update_endpoint($bound1, 1 - diag, S2EdgeClipping.interpolate_double(clip0.hi(), a0, b0, a1, b1))?
	}
	Ok(($bound0, $bound1))
}

## Moves the low end (`end == 0`) or the high end of the interval to `value`
## when that shrinks it, or gives `Err(NoIntersection)` when `value` is
## beyond the other end.
update_endpoint : R1Interval, U64, F64 -> Try(R1Interval, [NoIntersection])
update_endpoint = |bound, end, value|
	if end == 0 {
		if bound.hi() < value {
			Err(NoIntersection)
		} else if bound.lo() < value {
			Ok(R1Interval.new(value, bound.hi()))
		} else {
			Ok(bound)
		}
	} else if bound.lo() > value {
		Err(NoIntersection)
	} else if bound.hi() > value {
		Ok(R1Interval.new(bound.lo(), value))
	} else {
		Ok(bound)
	}

# The values below were printed by upstream's s2edge_clipping.h at v0.14.0
# through tools/s2_oracle.cc. tests/ClippingCorpus.roc holds many more.
expect S2EdgeClipping.face_clip_error_radians == 6.6613381477509392e-16
expect S2EdgeClipping.face_clip_error_uv_dist == 1.9984014443252818e-15
expect S2EdgeClipping.face_clip_error_uv_coord == 1.4130832128153977e-15
expect S2EdgeClipping.intersects_rect_error_uv_dist == 9.4205547521026515e-16
expect S2EdgeClipping.edge_clip_error_uv_coord == 4.9960036108132044e-16
expect S2EdgeClipping.edge_clip_error_uv_dist == 4.9960036108132044e-16
expect S2EdgeClipping.interpolate_double(0.3, 0.0, 1.0, 2.0, 4.0) == 2.6000000000000001
expect S2EdgeClipping.interpolate_double(0.9, 0.0, 1.0, 2.0, 4.0) == 3.7999999999999998
expect S2EdgeClipping.interpolate_double(0.5, 0.5, 0.5, 3.0, 3.0) == 3.0

# Upstream's FaceClipping test: an edge that crosses three cube edges, so four
# faces.
expect S2EdgeClipping.get_face_segments(
	S2Point.new(0.60717674071891636, 0.5464590666470247, 0.57681790368297048),
	S2Point.new(-0.60717674071891636, 0.57681790368297048, 0.5464590666470247),
)
	== [
		{ face: 0, a: R2Point.new(0.89999999999999991, 0.94999999999999984), b: R2Point.new(0.94999999999999996, 1.0) },
		{ face: 2, a: R2Point.new(-1.0, -0.94999999999999996), b: R2Point.new(0.0, -1.0) },
		{ face: 1, a: R2Point.new(0.0, 1.0), b: R2Point.new(1.0, 0.94999999999999996) },
		{ face: 3, a: R2Point.new(-0.94999999999999996, -1.0), b: R2Point.new(-0.89999999999999991, -0.94999999999999984) },
	]
expect S2EdgeClipping.clip_to_face(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 0) == Ok((R2Point.new(0.0, 0.0), R2Point.new(1.0, 0.0)))
expect S2EdgeClipping.clip_to_face(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 2) == Err(NoIntersection)
expect S2EdgeClipping.clip_to_padded_face(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), 2, 0.5) == Err(NoIntersection)
expect S2EdgeClipping.intersects_rect(
	R2Point.new(-1.0, -1.0),
	R2Point.new(1.0, 1.0),
	R2Rect.new(R1Interval.new(0.0, 0.5), R1Interval.new(-0.5, 0.0)),
)
expect !S2EdgeClipping.intersects_rect(
	R2Point.new(-1.0, -1.0),
	R2Point.new(1.0, 1.0),
	R2Rect.new(R1Interval.new(0.5, 1.0), R1Interval.new(-0.5, 0.0)),
)
expect S2EdgeClipping.clip_edge(
	R2Point.new(-1.0, -1.0),
	R2Point.new(1.0, 1.0),
	R2Rect.new(R1Interval.new(0.0, 0.5), R1Interval.new(-0.5, 0.25)),
)
	== Ok((R2Point.new(0.0, 0.0), R2Point.new(0.25, 0.25)))
expect S2EdgeClipping.clip_edge(
	R2Point.new(-1.0, -1.0),
	R2Point.new(1.0, 1.0),
	R2Rect.new(R1Interval.new(0.5, 1.0), R1Interval.new(-0.5, 0.0)),
)
	== Err(NoIntersection)
expect S2EdgeClipping.get_clipped_edge_bound(
	R2Point.new(-1.0, -1.0),
	R2Point.new(1.0, 1.0),
	R2Rect.new(R1Interval.new(0.0, 0.5), R1Interval.new(-0.5, 0.25)),
)
	== R2Rect.new(R1Interval.new(0.0, 0.25), R1Interval.new(0.0, 0.25))
expect S2EdgeClipping.clip_edge_bound(
	R2Point.new(-1.0, -0.5),
	R2Point.new(1.0, 0.5),
	R2Rect.new(R1Interval.new(-0.5, 0.5), R1Interval.new(-1.0, 1.0)),
	R2Rect.new(R1Interval.new(-0.5, 0.5), R1Interval.new(-0.25, 0.25)),
)
	== Ok(R2Rect.new(R1Interval.new(-0.5, 0.5), R1Interval.new(-0.25, 0.25)))

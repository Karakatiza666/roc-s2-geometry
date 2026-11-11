import Internal/S2Exact
import S1ChordAngle
import S2Point

## Robust geometric predicates: tests whose answers are exact, not merely
## computed carefully.
##
## Floating point cannot decide the orientation of three nearly collinear
## points, and a predicate that guesses produces contradictory answers that
## break the algorithms built on it. `sign` therefore escalates: a cheap
## error-bounded test first, then a more careful one, then exact arithmetic,
## and finally a symbolic perturbation that gives even exactly collinear
## points a consistent answer.
##
## The guarantees, for any distinct `a`, `b`, `c`:
##
## - `sign` is never zero
## - `sign(a, b, c) == -sign(b, a, c)` and the other five permutation
##   identities hold
## - the answer for a given triple never changes
S2Predicates := [].{

	## The largest determinant that a rounded dot product can produce from
	## unit-length inputs whose true determinant is zero.
	max_det_error : F64
	max_det_error = 4.057643110400022e-16

	## The orientation of the triangle `abc`: `1` when `c` is to the left of
	## the directed great circle from `a` to `b`, and `-1` when it is to the
	## right.
	##
	## Zero only when two of the points are identical.
	sign : S2Point, S2Point, S2Point -> I8
	sign = |a, b, c| S2Predicates.sign_with_cross(a, b, c, a.cross(b))

	## `sign` when `a x b` has already been computed.
	sign_with_cross : S2Point, S2Point, S2Point, S2Point -> I8
	sign_with_cross = |a, b, c, a_cross_b| {
		triaged = S2Predicates.triage_sign(c, a_cross_b)
		if triaged != 0 {
			triaged
		} else {
			S2Predicates.expensive_sign(a, b, c)
		}
	}

	## The cheap test: trust the rounded determinant only when it exceeds the
	## worst-case rounding error. Answers `0` when it does not.
	triage_sign : S2Point, S2Point -> I8
	triage_sign = |c, a_cross_b| {
		det = a_cross_b.dot(c)
		if det > S2Predicates.max_det_error {
			1
		} else if det < -S2Predicates.max_det_error {
			-1
		} else {
			0
		}
	}

	## The escalation path taken when `triage_sign` is undecided.
	expensive_sign : S2Point, S2Point, S2Point -> I8
	expensive_sign = |a, b, c| {
		# Identical points have no orientation, which is the only case that
		# answers zero.
		if a == b or b == c or c == a {
			return 0
		}
		stable = stable_sign(a, b, c)
		if stable != 0 {
			stable
		} else {
			S2Predicates.exact_sign(a, b, c)
		}
	}

	## The exact determinant sign, falling back to a symbolic perturbation
	## when the determinant is exactly zero.
	##
	## The points are sorted first, because the perturbation scheme assigns
	## each point an infinitesimal by its position in that order.
	exact_sign : S2Point, S2Point, S2Point -> I8
	exact_sign = |a, b, c| {
		(sorted, perm_sign) = S2Predicates.sort3(a, b, c)
		(pa, pb, pc) = sorted
		det = S2Exact.det3_sign(
			(pa.x(), pa.y(), pa.z()),
			(pb.x(), pb.y(), pb.z()),
			(pc.x(), pc.y(), pc.z()),
		)
		if det != 0 {
			perm_sign * det
		} else {
			perm_sign * S2Predicates.symbolic_sign(pa, pb, pc)
		}
	}

	## The sign of the determinant once every point has been nudged by its own
	## infinitesimal, which resolves the exactly-degenerate cases.
	##
	## Requires `a < b < c` and a determinant of exactly zero. This is
	## Edelsbrunner and Muecke's "Simulation of Simplicity": the tests below
	## enumerate the perturbation coefficients in decreasing order of
	## magnitude, and the first non-zero one decides.
	symbolic_sign : S2Point, S2Point, S2Point -> I8
	symbolic_sign = |a, b, c| {
		# Components of b x c, which are the coefficients of a's own
		# perturbations.
		bc2 = S2Exact.det2_sign(b.x(), b.y(), c.x(), c.y())
		if bc2 != 0 {
			return bc2
		}
		bc1 = S2Exact.det2_sign(b.z(), b.x(), c.z(), c.x())
		if bc1 != 0 {
			return bc1
		}
		bc0 = S2Exact.det2_sign(b.y(), b.z(), c.y(), c.z())
		if bc0 != 0 {
			return bc0
		}

		ca01 = S2Exact.det2_sign(c.x(), c.y(), a.x(), a.y())
		if ca01 != 0 {
			return ca01
		}
		cx = sign_of(c.x())
		if cx != 0 {
			return cx
		}
		cy = sign_of(c.y())
		if cy != 0 {
			return -cy
		}
		ca20 = S2Exact.det2_sign(c.z(), c.x(), a.z(), a.x())
		if ca20 != 0 {
			return ca20
		}
		cz = sign_of(c.z())
		if cz != 0 {
			return cz
		}

		ab01 = S2Exact.det2_sign(a.x(), a.y(), b.x(), b.y())
		if ab01 != 0 {
			return ab01
		}
		bx = sign_of(b.x())
		if bx != 0 {
			return -bx
		}
		by = sign_of(b.y())
		if by != 0 {
			return by
		}
		ax = sign_of(a.x())
		if ax != 0 {
			return ax
		}
		1
	}

	## True when a loop with consecutive vertices `a`, `b`, `c` contains the
	## vertex `b`.
	##
	## The wedge at `b` is treated as closed at `a` and open at `c`, which is
	## what makes two loops sharing a vertex agree about who owns it.
	angle_contains_vertex : S2Point, S2Point, S2Point -> Bool
	angle_contains_vertex = |a, b, c| !S2Predicates.ordered_ccw(b.ortho(), c, a, b)

	## True when `a`, `b`, `c` occur in counterclockwise order around the
	## vertex `o`, walking counterclockwise from `a` to `c`.
	##
	## Equivalently: `b` lies in the wedge from `a` to `c`. Degenerate cases
	## are resolved so that the three rotations of the arguments agree.
	ordered_ccw : S2Point, S2Point, S2Point, S2Point -> Bool
	ordered_ccw = |a, b, c, o| {
		var $sum = 0.U64
		if S2Predicates.sign(b, o, a) >= 0 {
			$sum = $sum + 1
		}
		if S2Predicates.sign(c, o, b) >= 0 {
			$sum = $sum + 1
		}
		if S2Predicates.sign(a, o, c) > 0 {
			$sum = $sum + 1
		}
		$sum >= 2
	}

	## Compares the distances from `x` to `a` and from `x` to `b`: `-1` when
	## `a` is closer, `1` when `b` is closer, and `0` only when `a == b`.
	##
	## The distances are measured as though every point lay exactly on the
	## unit sphere. Equal distances are broken by a symbolic perturbation, so
	## the results are consistent: if `ab < bc` and `bc < ac`, then `ab < ac`.
	##
	## Like `sign`, the test escalates from rounded arithmetic with an error
	## bound to exact arithmetic. Upstream tries `long double` precision
	## between those two steps; this port goes straight to exact arithmetic,
	## which gives the same answers.
	compare_distances : S2Point, S2Point, S2Point -> I8
	compare_distances = |x, a, b| {
		triaged = triage_compare_cos_distances(x, a, b)
		if triaged != 0 {
			return triaged
		}
		if a == b {
			return 0
		}
		# sin^2 is the more accurate measure near 0 and 180 degrees, cos near
		# 90 degrees. The test above failed, so the two angles are nearly
		# equal and one of them is enough to choose.
		cos_ax = a.dot(x)
		sin2 =
			if cos_ax > sqrt1_2 {
				triage_compare_sin2_distances(x, a, b)
			} else if cos_ax < -sqrt1_2 {
				-triage_compare_sin2_distances(x, a, b)
			} else {
				0
			}
		if sin2 != 0 {
			return sin2
		}
		exact = exact_compare_distances(x, a, b)
		if exact != 0 {
			return exact
		}
		# Symbolic perturbation: the smaller point stands on the higher
		# pedestal, so it is further away.
		if a < b {
			1
		} else if a > b {
			-1
		} else {
			0
		}
	}

	## Compares the distance from `x` to `y` with `r`: `-1` when it is less,
	## `0` when it is equal, and `1` when it is greater.
	##
	## The points are treated as though they lay exactly on the unit sphere.
	## There is no symbolic perturbation, so `0` is a possible answer.
	compare_distance : S2Point, S2Point, S1ChordAngle -> I8
	compare_distance = |x, y, r| {
		r2 = r.length2()
		triaged = triage_compare_cos_distance(x, y, r2)
		if triaged != 0 {
			return triaged
		}
		if r2 == 0.0 and x == y {
			return 0
		}
		# Near 180 degrees the chord angle itself has a rounding error of
		# about 2e-8 radians, so the sin^2 test is only worth trying for
		# small limits.
		sin2 = if (r2 < k45_degrees_length2) triage_compare_sin2_distance(x, y, r2) else 0
		if sin2 != 0 {
			return sin2
		}
		exact_compare_distance(x, y, r2)
	}

	## The exact sign of the dot product of `a` and `b`: `1`, `-1`, or `0`.
	##
	## Requires `a.norm2() <= 2` and `b.norm2() <= 2`, so that the edge
	## normals of a cell, which are not unit length, are allowed.
	sign_dot_prod : S2Point, S2Point -> I8
	sign_dot_prod = |a, b| {
		# The rounded dot product of vectors no longer than sqrt(2) is within
		# 3.03 epsilon of the true one (Rump 2011), rounded up to a value that
		# is exact in binary.
		dot = a.dot(b)
		if dot.abs() > 3.046875 * f64_epsilon {
			if (dot > 0.0) 1 else -1
		} else {
			S2Exact.sign_of(S2Exact.dot(coords(a), coords(b)))
		}
	}

	## Compares the distance from `x` to the edge `a0a1` with `r`: `-1` when
	## it is less, `0` when it is equal, and `1` when it is greater.
	##
	## The points are treated as though they lay exactly on the unit sphere.
	## Requires that `a0` and `a1` are not antipodal.
	compare_edge_distance : S2Point, S2Point, S2Point, S1ChordAngle -> I8
	compare_edge_distance = |x, a0, a1, r| {
		triaged = triage_compare_edge_distance(x, a0, a1, r.length2())
		if triaged != 0 {
			return triaged
		}
		if a0 == a1 {
			return S2Predicates.compare_distance(x, a0, r)
		}
		exact_compare_edge_distance(x, a0, a1, r)
	}

	## The sign of the dot product of the normals of the edges `a0a1` and
	## `b0b1`: `1` when the edges run in roughly the same direction around the
	## sphere, `-1` when they run in roughly opposite directions, and `0` when
	## they are exactly perpendicular.
	##
	## The answer is exact. There is no symbolic perturbation, so a
	## degenerate edge, or one whose endpoints are exactly proportional,
	## gives `0`. Requires that neither edge has antipodal endpoints.
	compare_edge_directions : S2Point, S2Point, S2Point, S2Point -> I8
	compare_edge_directions = |a0, a1, b0, b1| {
		na = (a0 - a1).cross(a0 + a1)
		nb = (b0 - b1).cross(b0 + b1)
		na_len = na.norm()
		nb_len = nb.norm()
		cos_ab = na.dot(nb)
		cos_ab_error =
			((5.0 + 4.0 * sqrt3) * na_len * nb_len + 32.0 * sqrt3 * dbl_err * (na_len + nb_len))
				* dbl_err
		if cos_ab > cos_ab_error {
			return 1
		}
		if cos_ab < -cos_ab_error {
			return -1
		}
		if a0 == a1 or b0 == b1 {
			return 0
		}
		S2Exact.sign_of(
			S2Exact.dot_exact(
				S2Exact.cross(coords(a0), coords(a1)),
				S2Exact.cross(coords(b0), coords(b1)),
			),
		)
	}

	## Sorts three points lexicographically, reporting the sign of the
	## permutation alongside them.
	sort3 : S2Point, S2Point, S2Point -> ((S2Point, S2Point, S2Point), I8)
	sort3 = |a, b, c| {
		var $x = a
		var $y = b
		var $z = c
		var $sign = 1.I8
		if $x > $y {
			swapped = $x
			$x = $y
			$y = swapped
			$sign = $sign.negate()
		}
		if $y > $z {
			swapped = $y
			$y = $z
			$z = swapped
			$sign = $sign.negate()
		}
		if $x > $y {
			swapped = $x
			$x = $y
			$y = swapped
			$sign = $sign.negate()
		}
		(($x, $y, $z), $sign)
	}
}

expect sign_of(1.5) == 1
expect sign_of(-0.0) == 0
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	S2Predicates.sign(a, b, c) == 1
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	S2Predicates.sign(b, a, c) == -1
}
expect {
	# Identical points are the only case with no orientation.
	a = S2Point.new(1.0, 0.0, 0.0)
	S2Predicates.sign(a, a, S2Point.new(0.0, 1.0, 0.0)) == 0
}
expect {
	# Three points on the equator are exactly collinear, so the answer comes
	# from the symbolic perturbation rather than from the determinant.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(-1.0, 0.0, 0.0)
	s = S2Predicates.sign(a, b, c)
	s != 0 and s == -S2Predicates.sign(b, a, c) and s == S2Predicates.sign(b, c, a)
}
expect {
	# The six permutations of an exactly degenerate triple stay consistent:
	# cyclic rotations agree and swaps invert.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(-1.0, 0.0, 0.0)
	s = S2Predicates.sign(a, b, c)
	s == S2Predicates.sign(b, c, a)
		and s == S2Predicates.sign(c, a, b)
		and s == -S2Predicates.sign(b, a, c)
		and s == -S2Predicates.sign(c, b, a)
		and s == -S2Predicates.sign(a, c, b)
}
expect {
	# Nearly collinear points that triage cannot decide.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(1.0, 1e-16, 0.0).normalize()
	c = S2Point.new(1.0, 2e-16, 1e-30).normalize()
	S2Predicates.sign(a, b, c) != 0
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(-1.0, 0.0, 0.0)
	o = S2Point.new(0.0, 0.0, 1.0)
	S2Predicates.ordered_ccw(a, b, c, o)
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, -1.0, 0.0)
	c = S2Point.new(-1.0, 0.0, 0.0)
	o = S2Point.new(0.0, 0.0, 1.0)
	!S2Predicates.ordered_ccw(a, b, c, o)
}
expect {
	(sorted, s) = S2Predicates.sort3(
		S2Point.new(3.0, 0.0, 0.0),
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(2.0, 0.0, 0.0),
	)
	sorted.0 == S2Point.new(1.0, 0.0, 0.0)
		and sorted.1 == S2Point.new(2.0, 0.0, 0.0)
		and sorted.2 == S2Point.new(3.0, 0.0, 0.0)
		and s == 1
}
expect {
	(sorted, s) = S2Predicates.sort3(
		S2Point.new(2.0, 0.0, 0.0),
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(3.0, 0.0, 0.0),
	)
	sorted.0 == S2Point.new(1.0, 0.0, 0.0) and s == -1
}
expect {
	# The wedge is closed at the incoming edge and open at the outgoing one.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	S2Predicates.angle_contains_vertex(a, b, c)
		!= S2Predicates.angle_contains_vertex(c, b, a)
}
expect {
	# A straight angle contains its vertex from exactly one side.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	S2Predicates.angle_contains_vertex(a, b, a) == Bool.False
}

# The cases of upstream's CompareDistances.Coverage test, with the
# arguments swapped as well. Upstream records the precision each case needs;
# the cases marked "long double", "exact" and "symbolic" are those that
# rounded arithmetic cannot decide.
# Double.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0).normalize(), S2Point.new(1.0, 1.0, 1.000000000000002).normalize()) == -1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 1.0, 1.000000000000002).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0).normalize()) == 1
# Double.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0e-21).normalize(), S2Point.new(1.0, 0.999999999999999, 0.0).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.999999999999999, 0.0).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0e-21).normalize()) == -1
# Long double.
expect S2Predicates.compare_distances(S2Point.new(2.0, 0.0, 0.0).normalize(), S2Point.new(2.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-08).normalize()) == -1
expect S2Predicates.compare_distances(S2Point.new(2.0, 0.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-08).normalize(), S2Point.new(2.0, -1.0, 0.0).normalize()) == 1
# Exact.
expect S2Predicates.compare_distances(S2Point.new(2.0, 0.0, 0.0).normalize(), S2Point.new(2.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-100).normalize()) == -1
expect S2Predicates.compare_distances(S2Point.new(2.0, 0.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-100).normalize(), S2Point.new(2.0, -1.0, 0.0).normalize()) == 1
# Symbolic.
expect S2Predicates.compare_distances(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 1.0, 0.0).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == -1
# Symbolic.
expect S2Predicates.compare_distances(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == 0
expect S2Predicates.compare_distances(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)) == 0
# Double.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 3.0e-15).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(-1.0, 1.0, 3.0e-15).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == -1
# Double.
expect S2Predicates.compare_distances(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0e-30, 0.0), S2Point.new(-1.0, 1.0e-40, 0.0)) == -1
expect S2Predicates.compare_distances(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 1.0e-40, 0.0), S2Point.new(1.0, 1.0e-30, 0.0)) == 1
# Long double.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 3.0e-18).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(-1.0, 1.0, 3.0e-18).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == -1
# Exact.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 1.0e-100).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(-1.0, 1.0, 1.0e-100).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == -1
# Symbolic.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize()) == -1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(-1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == 1
# Symbolic.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == 0
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize()) == 0
# Double.
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -0.999999999999999, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize()) == -1
expect S2Predicates.compare_distances(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(-1.0, -0.999999999999999, 0.0).normalize()) == 1
# Double.
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.999999999999999, 0.0).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0e-21).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0e-21).normalize(), S2Point.new(1.0, 0.999999999999999, 0.0).normalize()) == -1
# Long double.
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-08).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-08).normalize(), S2Point.new(2.0, 1.0, 0.0).normalize()) == -1
# Exact.
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-30).normalize()) == 1
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 1.0e-30).normalize(), S2Point.new(2.0, 1.0, 0.0).normalize()) == -1
# Symbolic.
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 2.0, 0.0).normalize()) == -1
expect S2Predicates.compare_distances(S2Point.new(-1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 2.0, 0.0).normalize(), S2Point.new(2.0, 1.0, 0.0).normalize()) == 1
# The cases of upstream's CompareDistance.Coverage test.
# Double.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0, 1.0).normalize(), S2Point.new(1.0, 0.999999999999999, 1.0).normalize(), S1ChordAngle.from_length2(1.0e-30)) == -1
# Long double.
expect S2Predicates.compare_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(0.585786437626905)) == -1
# Exact.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0e-40, 0.0), S2Point.new(1.0000000000000002, 1.0e-40, 0.0), S1ChordAngle.from_length2(3.9936083326813714e-112)) == 1
# Exact.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0e-40, 0.0), S2Point.new(1.0000000000000002, 1.0e-40, 0.0), S1ChordAngle.from_length2(5.965760595733903e-112)) == -1
# Exact.
expect S2Predicates.compare_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0000000000000002, 0.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
# Double.
expect S2Predicates.compare_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0e-08, 0.0), S1ChordAngle.from_length2(9.99999999999999e-15)) == -1
# Double.
expect S2Predicates.compare_distance(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0, 1.0e-08, 0.0), S1ChordAngle.from_length2(3.9999999999999902)) == 1
# Double.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0000000000000004, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == 1
# Long double.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0000000000000002, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == 1
# Exact.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 1.0e-30).normalize(), S1ChordAngle.from_length2(2.0)) == 0
# Exact.
expect S2Predicates.compare_distance(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(0.0, 1.0, 1.0).normalize(), S1ChordAngle.from_length2(1.0)) == 0
# The cases of upstream's CompareEdgeDistance.Coverage test.
# Double.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0, 1.0e-10, 1.0e-15), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(1.493393016426376e-30)) == -1
# Long double.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0, 1.0, 1.0e-15).normalize(), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(1.493393016426376e-30)) == -1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0, 1.0, 1.0e-40).normalize(), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(9.999999999999998e-81)) == -1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(0.0)) == 0
# Double.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0e-15, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(1.9999999999999964)) == 1
# Long double.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0e-15, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(1.9999999999999971)) == 1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0e-40, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(2.0)) == -1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(0.0, 0.0, 1.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(2.0)) == 0
# Double.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0e-15, -1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == -1
# Double.
expect S2Predicates.compare_edge_distance(S2Point.new(-1.0, -1.0, 1.0).normalize(), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == 1
# Long double.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0e-18, -1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == -1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(1.0e-100, -1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == -1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(0.0, -1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == 0
# Double.
expect S2Predicates.compare_edge_distance(S2Point.new(-1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S1ChordAngle.from_length2(2.0)) == 1
# Long double.
expect S2Predicates.compare_edge_distance(S2Point.new(-1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0e-18, 1.0, 0.0), S1ChordAngle.from_length2(2.0)) == 1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(-1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0e-100, 1.0, 0.0), S1ChordAngle.from_length2(2.0)) == 1
# Exact.
expect S2Predicates.compare_edge_distance(S2Point.new(0.0, -1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S1ChordAngle.from_length2(2.0)) == 0
# The cases of upstream's CompareEdgeDirections.Coverage test, and the same
# with the first edge reversed.
# Double.
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0)) == 1
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, -1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0)) == -1
# Double.
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 0.0, 1.5e-15), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 1
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.5e-15), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == -1
# Long double.
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 0.0, 1.0e-18), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 1
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0e-18), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == -1
# Exact.
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 0.0, 1.0e-50), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 1
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 1.0e-50), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == -1
# Exact.
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 0
expect S2Predicates.compare_edge_directions(S2Point.new(1.0, 1.0, 0.0).normalize(), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)) == 0
# The cases of upstream's SignDotProd tests, and two more.
# Exact.
expect S2Predicates.sign_dot_prod(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)) == 0
# Long double.
expect S2Predicates.sign_dot_prod(S2Point.new(1.0, 0.0, 0.0), S2Point.new(2.220446049250313e-16, 1.0, 0.0)) == 1
# Exact.
expect S2Predicates.sign_dot_prod(S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0e-45, 1.0, 0.0)) == 1
# Long double.
expect S2Predicates.sign_dot_prod(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-2.220446049250313e-16, 1.0, 0.0)) == -1
# Exact.
expect S2Predicates.sign_dot_prod(S2Point.new(1.0, 0.0, 0.0), S2Point.new(-1.0e-45, 1.0, 0.0)) == -1
# Exact.
expect S2Predicates.sign_dot_prod(S2Point.new(0.6, 0.8, 0.0), S2Point.new(0.8, -0.6, 1.0e-300)) == 0
# Exact.
expect S2Predicates.sign_dot_prod(S2Point.new(1.0, 1.0, 0.0), S2Point.new(1.0, -1.0, 0.0)) == 0

## `1`, `-1`, or `0` according to the sign of a double.
sign_of : F64 -> I8
sign_of = |x|
	if x > 0.0 {
		1
	} else if x < 0.0 {
		-1
	} else {
		0
	}

## The second test: recompute the determinant from edge vectors, which
## cancels far less for nearly collinear points, and keep the answer only
## when it clears that formulation's own error bound.
##
## This settles almost every case that `triage_sign` cannot, leaving exact
## arithmetic for points that really are collinear.
stable_sign : S2Point, S2Point, S2Point -> I8
stable_sign = |a, b, c| {
	ab = b - a
	bc = c - b
	ca = a - c
	ab2 = ab.norm2()
	bc2 = bc.norm2()
	ca2 = ca.norm2()

	# Permute so the longest edge comes first, which keeps the cross
	# product as large as possible.
	(det, max_error) =
		if ab2 >= bc2 and ab2 >= ca2 {
			(-ca.cross(bc).dot(c), 7.176703675781937e-16 * (ca2 * bc2).sqrt())
		} else if bc2 >= ca2 {
			(-ab.cross(ca).dot(a), 7.176703675781937e-16 * (ab2 * ca2).sqrt())
		} else {
			(-bc.cross(ab).dot(b), 7.176703675781937e-16 * (bc2 * ab2).sqrt())
		}

	# Below this the error bound itself has underflowed and says nothing.
	if max_error < 1.0705260268167732e-169 {
		0
	} else if det.abs() <= max_error {
		0
	} else if det > 0.0 {
		1
	} else {
		-1
	}
}

## Half of `F64` machine epsilon: the largest relative error of one rounded
## operation.
dbl_err : F64
dbl_err = 1.1102230246251565e-16

## `F64` machine epsilon.
f64_epsilon : F64
f64_epsilon = 2.220446049250313e-16

## The square root of 3.
sqrt3 : F64
sqrt3 = 1.7320508075688772

## The square root of 1/2.
sqrt1_2 : F64
sqrt1_2 = 0.7071067811865476

## The squared chord length of 45 degrees, `2 - sqrt(2)`.
k45_degrees_length2 : F64
k45_degrees_length2 = 2.0 - 1.4142135623730951

## The three coordinates of a point, the form `S2Exact` takes.
coords : S2Point -> (F64, F64, F64)
coords = |p| (p.x(), p.y(), p.z())

## `cos(xy)` and the largest error in it.
cos_distance : S2Point, S2Point -> (F64, F64)
cos_distance = |x, y| {
	c = x.dot(y)
	(c, 9.5 * dbl_err * c.abs() + 1.5 * dbl_err)
}

## `sin^2(xy)` and the largest error in it.
##
## The `(x - y) x (x + y)` form cancels almost all of the error that comes
## from `x` and `y` not being exactly unit length, so the relative error stays
## small even for tiny distances.
sin2_distance : S2Point, S2Point -> (F64, F64)
sin2_distance = |x, y| {
	n = (x - y).cross(x + y)
	d2 = 0.25 * n.norm2()
	error =
		(21.0 + 4.0 * sqrt3) * dbl_err * d2
			+ 32.0 * sqrt3 * dbl_err * dbl_err * d2.sqrt()
			+ 768.0 * dbl_err * dbl_err * dbl_err * dbl_err
	(d2, error)
}

## `compare_distances` from cosines, or `0` when the error bound says the
## answer is uncertain.
triage_compare_cos_distances : S2Point, S2Point, S2Point -> I8
triage_compare_cos_distances = |x, a, b| {
	(cos_ax, cos_ax_error) = cos_distance(a, x)
	(cos_bx, cos_bx_error) = cos_distance(b, x)
	diff = cos_ax - cos_bx
	error = cos_ax_error + cos_bx_error
	if diff > error {
		-1
	} else if diff < -error {
		1
	} else {
		0
	}
}

## `compare_distances` from squared sines, valid when both angles are below
## 90 degrees, or `0` when the answer is uncertain.
triage_compare_sin2_distances : S2Point, S2Point, S2Point -> I8
triage_compare_sin2_distances = |x, a, b| {
	(sin2_ax, sin2_ax_error) = sin2_distance(a, x)
	(sin2_bx, sin2_bx_error) = sin2_distance(b, x)
	diff = sin2_ax - sin2_bx
	error = sin2_ax_error + sin2_bx_error
	if diff > error {
		1
	} else if diff < -error {
		-1
	} else {
		0
	}
}

## `compare_distances` in exact arithmetic, as though the points lay exactly
## on the sphere: it tests `x.a / |a| < x.b / |b|` with both sides squared.
## Zero when the distances are exactly equal.
exact_compare_distances : S2Point, S2Point, S2Point -> I8
exact_compare_distances = |x, a, b| {
	cos_ax = S2Exact.dot(coords(x), coords(a))
	cos_bx = S2Exact.dot(coords(x), coords(b))
	a_sign = S2Exact.sign_of(cos_ax)
	b_sign = S2Exact.sign_of(cos_bx)
	if a_sign != b_sign {
		# A larger cosine is a smaller distance.
		return if (a_sign > b_sign) -1 else 1
	}
	a_norm2 = S2Exact.norm2_exact(S2Exact.vector(coords(a)))
	b_norm2 = S2Exact.norm2_exact(S2Exact.vector(coords(b)))
	cmp = S2Exact.sub(
		S2Exact.mul(S2Exact.square(cos_bx), a_norm2),
		S2Exact.mul(S2Exact.square(cos_ax), b_norm2),
	)
	a_sign * S2Exact.sign_of(cmp)
}

## `compare_distance` from cosines, or `0` when the answer is uncertain.
triage_compare_cos_distance : S2Point, S2Point, F64 -> I8
triage_compare_cos_distance = |x, y, r2| {
	(cos_xy, cos_xy_error) = cos_distance(x, y)
	cos_r = 1.0 - 0.5 * r2
	cos_r_error = 2.0 * dbl_err * cos_r
	diff = cos_xy - cos_r
	error = cos_xy_error + cos_r_error
	if diff > error {
		-1
	} else if diff < -error {
		1
	} else {
		0
	}
}

## `compare_distance` from squared sines, valid for limits below 90 degrees,
## or `0` when the answer is uncertain.
triage_compare_sin2_distance : S2Point, S2Point, F64 -> I8
triage_compare_sin2_distance = |x, y, r2| {
	(sin2_xy, sin2_xy_error) = sin2_distance(x, y)
	sin2_r = r2 * (1.0 - 0.25 * r2)
	sin2_r_error = 3.0 * dbl_err * sin2_r
	diff = sin2_xy - sin2_r
	error = sin2_xy_error + sin2_r_error
	if diff > error {
		1
	} else if diff < -error {
		-1
	} else {
		0
	}
}

## `compare_distance` in exact arithmetic, comparing `cos(xy)` with
## `cos(r) = 1 - r2 / 2` with both sides squared.
exact_compare_distance : S2Point, S2Point, F64 -> I8
exact_compare_distance = |x, y, r2| {
	cos_xy = S2Exact.dot(coords(x), coords(y))
	cos_r = S2Exact.grow(S2Exact.from_f64(-0.5 * r2), 1.0)
	xy_sign = S2Exact.sign_of(cos_xy)
	r_sign = S2Exact.sign_of(cos_r)
	if xy_sign != r_sign {
		return if (xy_sign > r_sign) -1 else 1
	}
	x_norm2 = S2Exact.norm2_exact(S2Exact.vector(coords(x)))
	y_norm2 = S2Exact.norm2_exact(S2Exact.vector(coords(y)))
	cmp = S2Exact.sub(
		S2Exact.mul(S2Exact.mul(S2Exact.square(cos_r), x_norm2), y_norm2),
		S2Exact.square(cos_xy),
	)
	xy_sign * S2Exact.sign_of(cmp)
}

## `compare_distance` from cosines, then from squared sines when the limit
## is small enough for them, or `0` when both are uncertain.
triage_compare_distance : S2Point, S2Point, F64 -> I8
triage_compare_distance = |x, y, r2| {
	sign = triage_compare_cos_distance(x, y, r2)
	if sign == 0 and r2 < k45_degrees_length2 {
		triage_compare_sin2_distance(x, y, r2)
	} else {
		sign
	}
}

## Whichever of `a0` and `a1` is closer to `x`, with ties going to the
## smaller point, and its squared distance from `x`.
closest_vertex : S2Point, S2Point, S2Point -> (S2Point, F64)
closest_vertex = |x, a0, a1| {
	a0x2 = (a0 - x).norm2()
	a1x2 = (a1 - x).norm2()
	if a0x2 < a1x2 or (a0x2 == a1x2 and a0 < a1) {
		(a0, a0x2)
	} else {
		(a1, a1x2)
	}
}

## Compares the distance from `x` to the great circle through `a0` and `a1`
## with `r2`, from squared sines, which is the accurate measure below 45
## degrees. `n` is `(a0 - a1) x (a0 + a1)`, `n1` its length and `n2` its
## squared length.
triage_compare_line_sin2_distance : S2Point, S2Point, S2Point, F64, S2Point, F64, F64 -> I8
triage_compare_line_sin2_distance = |x, a0, a1, r2, n, n1, n2| {
	# The closest point is interior to the edge, so the distance is below
	# 90 degrees.
	if r2 >= 2.0 {
		return -1
	}
	n2sin2_r = n2 * r2 * (1.0 - 0.25 * r2)
	(closest, ax2) = closest_vertex(x, a0, a1)
	x_dn = (x - closest).dot(n)
	x_dn2 = x_dn * x_dn
	c1 = ((3.5 + 2.0 * sqrt3) * n1 + 32.0 * sqrt3 * dbl_err) * dbl_err * ax2.sqrt()
	x_dn2_error = 4.0 * dbl_err * x_dn2 + (2.0 * x_dn.abs() + c1) * c1
	# x is unit length to within 4 * dbl_err.
	n2sin2_r_error = 6.0 * dbl_err * n2sin2_r + 8.0 * dbl_err * n2sin2_r
	diff = x_dn2 - n2sin2_r
	error = x_dn2_error + n2sin2_r_error
	if diff > error {
		1
	} else if diff < -error {
		-1
	} else {
		0
	}
}

## As `triage_compare_line_sin2_distance`, but from squared cosines, which is
## the accurate measure above 45 degrees.
triage_compare_line_cos2_distance : S2Point, S2Point, S2Point, F64, S2Point, F64, F64 -> I8
triage_compare_line_cos2_distance = |x, _a0, _a1, r2, n, n1, n2| {
	if r2 >= 2.0 {
		return -1
	}
	cos_r = 1.0 - 0.5 * r2
	n2cos2_r = n2 * cos_r * cos_r
	# The length of x cross n is the cosine of the distance.
	m2 = x.cross(n).norm2()
	m1 = m2.sqrt()
	m1_error = ((1.0 + 8.0 / sqrt3) * n1 + 32.0 * sqrt3 * dbl_err) * dbl_err
	m2_error = 3.0 * dbl_err * m2 + (2.0 * m1 + m1_error) * m1_error
	n2cos2_r_error = 7.0 * dbl_err * n2cos2_r + 8.0 * dbl_err * n2cos2_r
	diff = m2 - n2cos2_r
	error = m2_error + n2cos2_r_error
	if diff > error {
		-1
	} else if diff < -error {
		1
	} else {
		0
	}
}

## The line distance test that suits the size of the limit.
triage_compare_line_distance : S2Point, S2Point, S2Point, F64, S2Point, F64, F64 -> I8
triage_compare_line_distance = |x, a0, a1, r2, n, n1, n2|
	if r2 < k45_degrees_length2 {
		triage_compare_line_sin2_distance(x, a0, a1, r2, n, n1, n2)
	} else {
		triage_compare_line_cos2_distance(x, a0, a1, r2, n, n1, n2)
	}

## `compare_edge_distance` in rounded arithmetic, or `0` when the answer is
## uncertain.
##
## The closest point is interior to the edge exactly when `a0.m < 0` and
## `a1.m > 0`, where `m` is the normal of the plane through `x` that is
## perpendicular to the edge.
triage_compare_edge_distance : S2Point, S2Point, S2Point, F64 -> I8
triage_compare_edge_distance = |x, a0, a1, r2| {
	n = (a0 - a1).cross(a0 + a1)
	m = n.cross(x)
	# Subtracting x first keeps short edges accurate.
	a0_dir = a0 - x
	a1_dir = a1 - x
	a0_sign = a0_dir.dot(m)
	a1_sign = a1_dir.dot(m)
	n2 = n.norm2()
	n1 = n2.sqrt()
	n1_error = ((3.5 + 8.0 / sqrt3) * n1 + 32.0 * sqrt3 * dbl_err) * dbl_err
	a0_sign_error = n1_error * a0_dir.norm()
	a1_sign_error = n1_error * a1_dir.norm()
	vertex_sign = || triage_compare_distance(x, a0, r2).min(triage_compare_distance(x, a1, r2))
	if a0_sign < a0_sign_error and a1_sign > -a1_sign_error {
		line_sign = triage_compare_line_distance(x, a0, a1, r2, n, n1, n2)
		if a0_sign > -a0_sign_error or a1_sign < a1_sign_error {
			# Whether the closest point is a vertex or interior is itself
			# uncertain, so both must agree.
			if (vertex_sign() == line_sign) line_sign else 0
		} else {
			line_sign
		}
	} else {
		vertex_sign()
	}
}

## `compare_edge_distance` in exact arithmetic where it matters.
##
## Whether the closest point is an endpoint or interior is often easy even
## when the earlier tests failed, so that choice uses `compare_edge_directions`
## and the endpoint case uses `compare_distance`. Only the distance to the
## great circle is always exact.
exact_compare_edge_distance : S2Point, S2Point, S2Point, S1ChordAngle -> I8
exact_compare_edge_distance = |x, a0, a1, r| {
	# compare_edge_directions requires edges without antipodal endpoints.
	interior =
		a0 != -x
			and a1 != -x
			and S2Predicates.compare_edge_directions(a0, a1, a0, x) > 0
			and S2Predicates.compare_edge_directions(a0, a1, x, a1) > 0
	if interior {
		exact_compare_line_distance(x, a0, a1, r.length2())
	} else {
		S2Predicates.compare_distance(x, a0, r).min(S2Predicates.compare_distance(x, a1, r))
	}
}

## Compares the distance from `x` to the great circle through `a0` and `a1`
## with `r2` exactly, comparing `sin^2` of both. Requires that the closest
## point is interior to the edge.
exact_compare_line_distance : S2Point, S2Point, S2Point, F64 -> I8
exact_compare_line_distance = |x, a0, a1, r2| {
	if r2 >= 2.0 {
		return -1
	}
	n = S2Exact.cross(coords(a0), coords(a1))
	xv = S2Exact.vector(coords(x))
	sin_d = S2Exact.dot_exact(xv, n)
	sin2_r = S2Exact.mul(S2Exact.from_f64(r2), S2Exact.grow(S2Exact.from_f64(-0.25 * r2), 1.0))
	cmp = S2Exact.sub(
		S2Exact.square(sin_d),
		S2Exact.mul(S2Exact.mul(sin2_r, S2Exact.norm2_exact(xv)), S2Exact.norm2_exact(n)),
	)
	S2Exact.sign_of(cmp)
}

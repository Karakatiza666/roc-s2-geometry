import Internal/S2Exact
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

	## The escalation path taken when `triage_sign` is undecided.
	expensive_sign : S2Point, S2Point, S2Point -> I8
	expensive_sign = |a, b, c| {
		# Identical points have no orientation, which is the only case that
		# answers zero.
		if a == b or b == c or c == a {
			return 0
		}
		stable = S2Predicates.stable_sign(a, b, c)
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
		cx = S2Predicates.sign_of(c.x())
		if cx != 0 {
			return cx
		}
		cy = S2Predicates.sign_of(c.y())
		if cy != 0 {
			return -cy
		}
		ca20 = S2Exact.det2_sign(c.z(), c.x(), a.z(), a.x())
		if ca20 != 0 {
			return ca20
		}
		cz = S2Predicates.sign_of(c.z())
		if cz != 0 {
			return cz
		}

		ab01 = S2Exact.det2_sign(a.x(), a.y(), b.x(), b.y())
		if ab01 != 0 {
			return ab01
		}
		bx = S2Predicates.sign_of(b.x())
		if bx != 0 {
			return -bx
		}
		by = S2Predicates.sign_of(b.y())
		if by != 0 {
			return by
		}
		ax = S2Predicates.sign_of(a.x())
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
}

expect S2Predicates.sign_of(1.5) == 1
expect S2Predicates.sign_of(-0.0) == 0
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

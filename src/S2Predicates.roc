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

	## Which of two sites `get_voronoi_site_exclusion` finds excluded:
	## `First`, `Second`, or `Neither`.
	##
	## Upstream's enum also has `UNCERTAIN`, which only its rounded triage
	## step returns. The exact step that follows always decides, so the
	## public result never has it.
	Excluded : [First, Second, Neither]

	## The side of the great circle with normal `x` on which the edge `ab`
	## meets the great circle with normal `n`: `1` when the point where the
	## edge's great circle crosses `n` in the direction of `(a x b) x n` lies
	## on the positive side of `x`, `-1` on the negative side, and `0` when it
	## lies exactly on it.
	##
	## The test is `((a x b) x n) . x`, which is `(n.a)(x.b) - (n.b)(x.a)`,
	## first in rounded arithmetic with an error bound and then exactly.
	## `n` and `x` need not be unit length. Requires that `a` and `b` are
	## neither equal nor antipodal. Upstream's
	## `s2pred::CircleEdgeIntersectionSign`.
	circle_edge_intersection_sign : S2Point, S2Point, S2Point, S2Point -> I8
	circle_edge_intersection_sign = |a, b, n, x| {
		triaged = triage_circle_edge_intersection_sign(a, b, n, x)
		if triaged != 0 {
			return triaged
		}
		S2Exact.sign_of(
			S2Exact.sub(
				S2Exact.mul(S2Exact.dot(coords(n), coords(a)), S2Exact.dot(coords(x), coords(b))),
				S2Exact.mul(S2Exact.dot(coords(n), coords(b)), S2Exact.dot(coords(x), coords(a))),
			),
		)
	}

	## Compares where the edges `ab` and `cd` meet the great circle with
	## normal `m`, measured along that circle from the great circle with
	## normal `n`: `-1` when the crossing of `ab` comes first, `1` when the
	## crossing of `cd` comes first, and `0` when they coincide.
	##
	## The distances compared are `((a x b) x m) . n` and
	## `((c x d) x m) . n`. The comparison is exact, and an edge compared with
	## itself or with its reverse gives `0`. Requires that neither edge has
	## equal or antipodal endpoints, and that `m` and `n` are neither equal
	## nor antipodal. Upstream's `s2pred::CircleEdgeIntersectionOrdering`.
	circle_edge_intersection_ordering : S2Point, S2Point, S2Point, S2Point, S2Point, S2Point -> I8
	circle_edge_intersection_ordering = |a, b, c, d, m, n| {
		triaged = triage_intersection_ordering(a, b, c, d, m, n)
		if triaged != 0 {
			return triaged
		}
		if (a == c and b == d) or (a == d and b == c) {
			return 0
		}
		product = |p, q| S2Exact.sub(
			S2Exact.mul(S2Exact.dot(coords(m), coords(p)), S2Exact.dot(coords(n), coords(q))),
			S2Exact.mul(S2Exact.dot(coords(m), coords(q)), S2Exact.dot(coords(n), coords(p))),
		)
		S2Exact.sign_of(S2Exact.sub(product(a, b), product(c, d)))
	}

	## The side of the edge `x0x1` on which the circumcenter of the triangle
	## `abc` lies: `sign(x0, x1, z)` for the circumcenter `z`, as `sign` gives
	## it. The circumcenter is the point equidistant from `a`, `b` and `c` on
	## the side of the triangle's plane where its vertices run
	## counterclockwise.
	##
	## The answer is `0` only when `x0 == x1` or two of `a`, `b`, `c` are
	## equal. Otherwise a circumcenter that lies exactly on the great circle
	## of the edge is resolved by a symbolic perturbation that moves it
	## towards the smallest of `a`, `b` and `c`. Requires that `x0` and `x1`
	## are not antipodal. Upstream's `s2pred::EdgeCircumcenterSign`.
	##
	## The test escalates from rounded arithmetic with an error bound to an
	## exact polynomial of degree 20. Upstream tries `long double` precision
	## between those two steps; this port goes straight to exact arithmetic.
	edge_circumcenter_sign : S2Point, S2Point, S2Point, S2Point, S2Point -> I8
	edge_circumcenter_sign = |x0, x1, a, b, c| {
		abc_sign = S2Predicates.sign(a, b, c)
		triaged = triage_edge_circumcenter_sign(x0, x1, a, b, c, abc_sign)
		if triaged != 0 {
			return triaged
		}
		if x0 == x1 or a == b or b == c or c == a {
			return 0
		}
		exact = exact_edge_circumcenter_sign(x0, x1, a, b, c, abc_sign)
		if exact != 0 {
			return exact
		}
		symbolic_edge_circumcenter_sign(x0, x1, a, b, c)
	}

	## Given two sites `a` and `b` that are both within the distance `r` of
	## the edge `x0x1`, and with `a` closer than `b` to `x0`, tells whether
	## one site is closer than the other to every point of the edge that is
	## within `r` of either of them.
	##
	## `First` means `a` is excluded: on that part of the edge, `b` is always
	## the closer site. `Second` means `b` is excluded, and `Neither` that
	## each site is the closer one somewhere. The Voronoi regions of the two
	## sites are measured along the edge, which is how upstream's snapping
	## decides which sites an edge needs to pass near.
	##
	## Requires `r` below 90 degrees, `compare_distances(x0, a, b) < 0`, both
	## sites within `r` of the edge, and that `x0` and `x1` are not
	## antipodal. Upstream's `s2pred::GetVoronoiSiteExclusion`. The test
	## escalates from rounded arithmetic to exact arithmetic; upstream tries
	## `long double` precision between the two.
	get_voronoi_site_exclusion : S2Point, S2Point, S2Point, S2Point, S1ChordAngle -> Excluded
	get_voronoi_site_exclusion = |a, b, x0, x1, r| {
		# One site that is closer to both endpoints is closer to the whole
		# edge. compare_distances breaks ties consistently.
		if S2Predicates.compare_distances(x1, a, b) < 0 {
			return Second
		}
		match triage_voronoi_site_exclusion(a, b, x0, x1, r.length2()) {
			First => First
			Second => Second
			Neither => Neither
			Uncertain => exact_voronoi_site_exclusion(a, b, x0, x1, r.length2())
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

## Upstream's `UnperturbedSign`: the orientation of `abc` as `sign` finds it,
## but `0` when the points are exactly collinear rather than a symbolic
## answer.
unperturbed_sign : S2Point, S2Point, S2Point -> I8
unperturbed_sign = |a, b, c| {
	triaged = S2Predicates.triage_sign(c, a.cross(b))
	if triaged != 0 {
		return triaged
	}
	if a == b or b == c or c == a {
		return 0
	}
	stable = stable_sign(a, b, c)
	if stable != 0 {
		return stable
	}
	S2Exact.det3_sign(coords(a), coords(b), coords(c))
}

## `circle_edge_intersection_sign` in rounded arithmetic, with an absolute
## error of at most `14` epsilon, or `0` when that leaves the sign uncertain.
triage_circle_edge_intersection_sign : S2Point, S2Point, S2Point, S2Point -> I8
triage_circle_edge_intersection_sign = |a, b, n, x| {
	ndota = n.dot(a)
	ndotb = n.dot(b)
	xdota = x.dot(a)
	xdotb = x.dot(b)
	prod = ndota * xdotb - ndotb * xdota
	if prod.abs() <= 14.0 * f64_epsilon {
		0
	} else if prod < 0.0 {
		-1
	} else {
		1
	}
}

## `circle_edge_intersection_ordering` in rounded arithmetic, with an
## absolute error of at most `32` epsilon, or `0` when that leaves the order
## uncertain.
triage_intersection_ordering : S2Point, S2Point, S2Point, S2Point, S2Point, S2Point -> I8
triage_intersection_ordering = |a, b, c, d, m, n| {
	mdota = m.dot(a)
	mdotb = m.dot(b)
	mdotc = m.dot(c)
	mdotd = m.dot(d)
	ndota = n.dot(a)
	ndotb = n.dot(b)
	ndotc = n.dot(c)
	ndotd = n.dot(d)
	prodab = mdota * ndotb - mdotb * ndota
	prodcd = mdotc * ndotd - mdotd * ndotc
	if (prodab - prodcd).abs() > 32.0 * f64_epsilon {
		if (prodab < prodcd) -1 else 1
	} else {
		0
	}
}

## The circumcenter of `abc` when the triangle runs counterclockwise, and its
## negation when it runs clockwise, from the perpendicular bisectors of `ab`
## and `bc`, with the largest error in it.
circumcenter : S2Point, S2Point, S2Point -> (S2Point, F64)
circumcenter = |a, b, c| {
	ab_diff = a - b
	ab_sum = a + b
	bc_diff = b - c
	bc_sum = b + c
	nab = ab_diff.cross(ab_sum)
	nab_len = nab.norm()
	ab_len = ab_diff.norm()
	nbc = bc_diff.cross(bc_sum)
	nbc_len = nbc.norm()
	bc_len = bc_diff.norm()
	mab = nab.cross(ab_sum)
	mbc = nbc.cross(bc_sum)
	error =
		((16.0 + 24.0 * sqrt3) * dbl_err + 8.0 * dbl_err * (ab_len + bc_len)) * nab_len * nbc_len
			+ 128.0 * sqrt3 * dbl_err * dbl_err * (nab_len + nbc_len)
			+ 3.0 * 4096.0 * dbl_err * dbl_err * dbl_err * dbl_err
	(mab.cross(mbc), error)
}

## `edge_circumcenter_sign` in rounded arithmetic, or `0` when the error bound
## leaves the sign uncertain.
triage_edge_circumcenter_sign : S2Point, S2Point, S2Point, S2Point, S2Point, I8 -> I8
triage_edge_circumcenter_sign = |x0, x1, a, b, c, abc_sign| {
	(z, z_error) = circumcenter(a, b, c)
	nx = (x0 - x1).cross(x0 + x1)
	# A clockwise triangle gave the negated circumcenter.
	result = abc_sign.to_f64() * nx.dot(z)
	z_len = z.norm()
	nx_len = nx.norm()
	nx_error = ((1.0 + 2.0 * sqrt3) * nx_len + 32.0 * sqrt3 * dbl_err) * dbl_err
	result_error = (3.0 * dbl_err * nx_len + nx_error) * z_len + z_error * nx_len
	if result > result_error {
		1
	} else if result < -result_error {
		-1
	} else {
		0
	}
}

## `-1`, `0` or `1` for an integer difference, clamped as upstream's
## `max(-1, min(1, x))` clamps it.
clamp_sign : I8 -> I8
clamp_sign = |x| x.max(-1).min(1)

## `edge_circumcenter_sign` in exact arithmetic, or `0` when the circumcenter
## lies exactly on the great circle of the edge, or the edge is degenerate.
##
## The test is `(x0 x x1) . (|c| (a x b) + |a| (b x c) + |b| (c x a)) > 0`.
## The square roots in the norms are removed by isolating them and squaring
## both sides twice, checking the signs of both sides before each squaring.
exact_edge_circumcenter_sign : S2Point, S2Point, S2Point, S2Point, S2Point, I8 -> I8
exact_edge_circumcenter_sign = |x0, x1, a, b, c, abc_sign| {
	nx = S2Exact.cross(coords(x0), coords(x1))
	if S2Exact.is_zero(nx) {
		return 0
	}
	dab = S2Exact.dot_exact(nx, S2Exact.cross(coords(a), coords(b)))
	dbc = S2Exact.dot_exact(nx, S2Exact.cross(coords(b), coords(c)))
	dca = S2Exact.dot_exact(nx, S2Exact.cross(coords(c), coords(a)))
	abc2 = S2Exact.mul(S2Exact.norm2_exact(S2Exact.vector(coords(a))), S2Exact.square(dbc))
	bca2 = S2Exact.mul(S2Exact.norm2_exact(S2Exact.vector(coords(b))), S2Exact.square(dca))
	cab2 = S2Exact.mul(S2Exact.norm2_exact(S2Exact.vector(coords(c))), S2Exact.square(dab))

	# |C| dAB > -|A| dBC: compare the signs, and square when they agree.
	lhs3_sgn = S2Exact.sign_of(dab)
	rhs3_sgn = -S2Exact.sign_of(dbc)
	lhs2_sgn =
		if clamp_sign(lhs3_sgn - rhs3_sgn) == 0 and lhs3_sgn != 0 {
			S2Exact.sign_of(S2Exact.sub(cab2, abc2)) * lhs3_sgn
		} else {
			clamp_sign(lhs3_sgn - rhs3_sgn)
		}

	# |C| dAB + |A| dBC > -|B| dCA, in the same way.
	rhs2_sgn = -S2Exact.sign_of(dca)
	first = clamp_sign(lhs2_sgn - rhs2_sgn)
	result =
		if first == 0 and lhs2_sgn != 0 {
			# 2 |A| |C| dAB dBC > |B|^2 dCA^2 - |C|^2 dAB^2 - |A|^2 dBC^2.
			lhs4_sgn = S2Exact.sign_of(dab) * S2Exact.sign_of(dbc)
			rhs4 = S2Exact.sub(S2Exact.sub(bca2, cab2), abc2)
			second = clamp_sign(lhs4_sgn - S2Exact.sign_of(rhs4))
			squared =
				if second == 0 and lhs4_sgn != 0 {
					four_products = S2Exact.scale(S2Exact.mul(abc2, cab2), 4.0)
					S2Exact.sign_of(S2Exact.sub(four_products, S2Exact.square(rhs4))) * lhs4_sgn
				} else {
					second
				}
			squared * lhs2_sgn
		} else {
			first
		}
	abc_sign * result
}

## `edge_circumcenter_sign` after symbolic perturbation, for a circumcenter
## that lies exactly on the great circle of the edge.
##
## The smallest of `a`, `b`, `c` has the largest perturbation, which moves
## the circumcenter towards it, so the side of that point decides. When it
## lies on the great circle too, the next point decides. The answer is `0`
## only when two of `a`, `b`, `c` are equal.
symbolic_edge_circumcenter_sign : S2Point, S2Point, S2Point, S2Point, S2Point -> I8
symbolic_edge_circumcenter_sign = |x0, x1, a, b, c| {
	if a == b or b == c or c == a {
		return 0
	}
	((pa, pb, pc), _) = S2Predicates.sort3(a, b, c)
	first = unperturbed_sign(x0, x1, pa)
	if first != 0 {
		return first
	}
	second = unperturbed_sign(x0, x1, pb)
	if second != 0 {
		return second
	}
	unperturbed_sign(x0, x1, pc)
}

## `get_voronoi_site_exclusion` in rounded arithmetic, or `Uncertain` when the
## error bounds do not decide it.
##
## Each site covers an interval of the edge, the points within `r` of it.
## One site excludes the other when its interval contains the other's, which
## is `|rb - ra| > d` for the radii `ra`, `rb` of the intervals and the
## distance `d` between their centres. The sines and cosines of those angles
## come from dot and cross products, scaled to avoid divisions.
triage_voronoi_site_exclusion : S2Point, S2Point, S2Point, S2Point, F64 -> [First, Second, Neither, Uncertain]
triage_voronoi_site_exclusion = |a, b, x0, x1, r2| {
	n = (x0 - x1).cross(x0 + x1)
	n2 = n.norm2()
	n1 = n2.sqrt()
	dn_error = ((3.5 + 2.0 * sqrt3) * n1 + 32.0 * sqrt3 * dbl_err) * dbl_err

	cos_r = 1.0 - 0.5 * r2
	sin2_r = r2 * (1.0 - 0.25 * r2)
	n2sin2_r = n2 * sin2_r

	# The scaled sine of the radius of the interval of a site, and its error.
	radius = |p| {
		(closest, px2) = closest_vertex(p, x0, x1)
		p_dn = (p - closest).dot(n)
		p_dn2 = p_dn * p_dn
		p_dn_error = dn_error * px2.sqrt()
		rp2 = n2sin2_r - p_dn2
		rp2_error =
			(8.0 * dbl_err + 4.0 * dbl_err) * p_dn2
				+ (2.0 * p_dn.abs() + p_dn_error) * p_dn_error
				+ 6.0 * dbl_err * n2sin2_r
		min_rp2 = rp2 - rp2_error
		if min_rp2 < 0.0 {
			Err(Uncertain)
		} else {
			rp = rp2.sqrt()
			Ok({ dn: p_dn, dn_error: p_dn_error, r: rp, error: 1.5 * dbl_err * rp + 0.5 * rp2_error / min_rp2.sqrt() })
		}
	}
	match (radius(a), radius(b)) {
		(Ok(ra), Ok(rb)) => {
			# Positive when a may be excluded, negative when b may be.
			lhs3 = cos_r * (rb.r - ra.r)
			abs_lhs3 = lhs3.abs()
			lhs3_error = cos_r * (ra.error + rb.error) + 3.0 * dbl_err * abs_lhs3

			# The scaled sine of the distance between the centres.
			a_x_b = (a - b).cross(a + b)
			a_x_b1 = a_x_b.norm()
			sin_d = 0.5 * a_x_b.dot(n)
			sin_d_error =
				(4.0 * dbl_err + (2.5 + 2.0 * sqrt3) * dbl_err) * a_x_b1 * n1
					+ 16.0 * sqrt3 * dbl_err * dbl_err * (a_x_b1 + n1)

			result = abs_lhs3 - sin_d
			result_error = lhs3_error + sin_d_error
			if result < -result_error {
				Neither
			} else if sin_d < -sin_d_error {
				# The sites project onto the edge in the opposite order. Each
				# site is kept when it is within 90 degrees of its endpoint.
				ca = triage_compare_cos_distance(a, x0, 2.0)
				cb = triage_compare_cos_distance(b, x1, 2.0)
				if ca < 0 and cb < 0 {
					Neither
				} else if ca <= 0 and cb <= 0 {
					Uncertain
				} else if ca > 0 {
					First
				} else {
					Second
				}
			} else if sin_d <= sin_d_error {
				Uncertain
			} else {
				# The test above needs the distance below 90 degrees.
				cos_d = a.dot(b) * n2 - ra.dn * rb.dn
				cos_d_error =
					((8.0 * dbl_err + 5.0 * dbl_err) * ra.dn.abs() + ra.dn_error) * rb.dn.abs()
						+ (ra.dn.abs() + ra.dn_error) * rb.dn_error
						+ (8.0 * dbl_err + 8.0 * dbl_err) * n2
				if cos_d <= -cos_d_error {
					Neither
				} else if cos_d < cos_d_error {
					Uncertain
				} else if result <= result_error {
					Uncertain
				} else if lhs3 > 0.0 {
					First
				} else {
					Second
				}
			}
		}
		_ => Uncertain
	}
}

## `get_voronoi_site_exclusion` in exact arithmetic. The square roots in the
## radii are removed by isolating them and squaring both sides twice, with
## the signs of both sides checked before each squaring.
exact_voronoi_site_exclusion : S2Point, S2Point, S2Point, S2Point, F64 -> S2Predicates.Excluded
exact_voronoi_site_exclusion = |a, b, x0, x1, r2| {
	n = S2Exact.cross(coords(x0), coords(x1))
	av = S2Exact.vector(coords(a))
	bv = S2Exact.vector(coords(b))
	rhs2 = S2Exact.dot_exact(S2Exact.cross(coords(a), coords(b)), n)
	rhs2_sgn = S2Exact.sign_of(rhs2)
	if rhs2_sgn < 0 {
		# The sites project onto the edge in the opposite order.
		ca = exact_compare_distance(a, x0, 2.0)
		cb = exact_compare_distance(b, x1, 2.0)
		return if ca < 0 and cb < 0 {
			Neither
		} else if ca > 0 {
			First
		} else {
			Second
		}
	}

	# The distance between the centres must be below 90 degrees.
	n2 = S2Exact.norm2_exact(n)
	a_dn = S2Exact.dot_exact(av, n)
	b_dn = S2Exact.dot_exact(bv, n)
	cos_d = S2Exact.sub(S2Exact.mul(S2Exact.dot(coords(a), coords(b)), n2), S2Exact.mul(a_dn, b_dn))
	if S2Exact.sign_of(cos_d) < 0 {
		return Neither
	}

	# sa and sb are the scaled radii; the sign of sb - sa says which site
	# may be excluded.
	a2 = S2Exact.norm2_exact(av)
	b2 = S2Exact.norm2_exact(bv)
	r2_xf = S2Exact.from_f64(r2)
	n2sin2_r = S2Exact.mul(S2Exact.mul(r2_xf, S2Exact.grow(S2Exact.from_f64(-0.25 * r2), 1.0)), n2)
	sa2 = S2Exact.mul(b2, S2Exact.sub(S2Exact.mul(n2sin2_r, a2), S2Exact.square(a_dn)))
	sb2 = S2Exact.mul(a2, S2Exact.sub(S2Exact.mul(n2sin2_r, b2), S2Exact.square(b_dn)))
	lhs2_sgn = S2Exact.sign_of(S2Exact.sub(sb2, sa2))
	if lhs2_sgn == 0 {
		# Both sites are equidistant from every point of the edge, which
		# compare_distances has already resolved.
		return Neither
	}

	# cos^2(r) (sb^2 + sa^2) - (aXb.n)^2 > 2 cos^2(r) sa sb, then squared.
	cos_r = S2Exact.grow(S2Exact.from_f64(-0.5 * r2), 1.0)
	cos2_r = S2Exact.square(cos_r)
	lhs3 = S2Exact.sub(S2Exact.mul(cos2_r, S2Exact.add(sa2, sb2)), S2Exact.square(rhs2))
	if S2Exact.sign_of(lhs3) < 0 {
		return Neither
	}
	lhs4 = S2Exact.square(lhs3)
	rhs4 = S2Exact.scale(S2Exact.mul(S2Exact.mul(S2Exact.square(cos2_r), sa2), sb2), 4.0)
	result = S2Exact.sign_of(S2Exact.sub(lhs4, rhs4))
	if result < 0 {
		return Neither
	}
	# Equal radii share an endpoint at the distance r from both sites, and
	# the larger site is the closer one there.
	if result == 0 and (lhs2_sgn > 0) == (a > b) {
		return Neither
	}
	if (lhs2_sgn > 0) First else Second
}

# CircleEdgeIntersectionSign at v0.14.0, through tools/s2_oracle.cc, for the
# cases of upstream's CircleEdgeIntersectionSign.Works test: the centre of a
# cell, a point in a neighbouring cell, the cell's top edge normal and one of
# its side edge normals. Each case also gives the result of upstream's
# double-precision triage; where that is 0, the exact step decides.
circle_sign_cases : List((S2Point, S2Point, S2Point, S2Point, I8, I8))
circle_sign_cases = [
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.98287218693432188, -0.18428853505018536, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), -1, -1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.98287218693432188, -0.18428853505018536, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), 0, 0),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.92307692307692313, 0.38461538461538458, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.92307692307692313, 0.38461538461538458, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), -1, -1),
	(S2Point.new(0.99225137462702884, -0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, 1.0, -0.0), 1, 1),
	(S2Point.new(0.99225137462702884, -0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.0, -1.0, 0.0), 0, 0),
	# The two cases above that land exactly on the side edge, with the end of
	# the edge moved off it by a tiny amount. Triage cannot decide them, and
	# the exact step does.
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 1e-17, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), 1, 0),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 0.0, -1e-15), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), -1, 0),
	(S2Point.new(0.99225137462702884, -0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, -1e-15, 0.0), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.0, -1.0, 0.0), 1, 0),
	(S2Point.new(0.99225137462702884, -0.087855590461768163, -0.087855590461768163), S2Point.new(1.0, 0.0, 1e-17), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.0, -1.0, 0.0), 1, 0),
]

expect circle_sign_cases.all(
	|(a, b, n, x, expected, triaged)|
		S2Predicates.circle_edge_intersection_sign(a, b, n, x) == expected
			and triage_circle_edge_intersection_sign(a, b, n, x) == triaged,
)

# CircleEdgeIntersectionOrdering, for the cases of upstream's
# CircleEdgeIntersectionOrdering.Works test, with the triage result. The last
# four move one endpoint by one epsilon, and upstream decides them in long
# double precision; this port decides them exactly.
circle_order_cases : List((S2Point, S2Point, S2Point, S2Point, S2Point, S2Point, I8, I8))
circle_order_cases = [
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 0, 0),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.98287218693432188, 0.0, 0.18428853505018536), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.96659534932828317, 0.1812366279990531, 0.1812366279990531), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.98287218693432188, 0.0, 0.18428853505018536), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.96659534932828317, 0.1812366279990531, 0.1812366279990531), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), -1, -1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.96659534932828317, 0.1812366279990531, 0.1812366279990531), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.98287218693432188, 0.0, 0.18428853505018536), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), -1, -1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.96659534932828317, 0.1812366279990531, 0.1812366279990531), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.98287218693432188, 0.0, 0.18428853505018536), S2Point.new(0.0, -0.0, -1.0), S2Point.new(-0.0, 1.0, -0.0), 1, 1),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768385, 0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), -1, 0),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461767941, 0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 1, 0),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768385, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), 1, 0),
	(S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, 0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461768163, -0.087855590461768163), S2Point.new(0.99225137462702884, 0.087855590461767941, 0.087855590461768163), S2Point.new(0.0, -0.0, -1.0), S2Point.new(0.1875, -1.0, 0.0), -1, 0),
]

expect circle_order_cases.all(
	|(a, b, c, d, m, n, expected, triaged)|
		S2Predicates.circle_edge_intersection_ordering(a, b, c, d, m, n) == expected
			and triage_intersection_ordering(a, b, c, d, m, n) == triaged,
)

# EdgeCircumcenterSign, for the cases of upstream's EdgeCircumcenterSign.Coverage
# test, with the triage and the exact results. A triage of 0 with an exact
# result of 0 is a symbolic case; the last two fall back to the second and the
# third perturbation.
circumcenter_cases : List((S2Point, S2Point, S2Point, S2Point, S2Point, I8, I8, I8))
circumcenter_cases = [
	(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.0, 0.0, 1.0), S2Point.new(0.70710678118654746, 0.0, 0.70710678118654746), S2Point.new(0.0, 0.70710678118654746, 0.70710678118654746), 1, 1, 1),
	(S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.0, 0.0, -1.0), S2Point.new(0.70710678118654746, 0.0, -0.70710678118654746), S2Point.new(0.0, 0.70710678118654746, -0.70710678118654746), -1, -1, -1),
	(S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.70710678116886982, -7.0710678116886989e-6, 0.70710678116886982), S2Point.new(0.70710678116886982, 7.0710678116886989e-6, -0.70710678116886982), S2Point.new(0.70711031671161428, 0.70710324560844717, 7.0711031671161436e-6), -1, -1, -1),
	(S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.70710678116886982, -7.0710678116886989e-6, 0.70710678116886982), S2Point.new(0.70710678116886982, 7.0710678116886989e-6, -0.70710678116886982), S2Point.new(0.70710678152242323, 0.70710678081531653, 7.0710678152242331e-6), -1, 0, -1),
	(S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.70710678116886982, -7.0710678116886989e-6, 0.70710678116886982), S2Point.new(0.70710678116886982, 7.0710678116886989e-6, -0.70710678116886982), S2Point.new(0.70710678116887027, 0.7071067811688696, 7.0710678116887032e-6), -1, 0, -1),
	(S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.70710678116886982, -7.0710678116886989e-6, 0.70710678116886982), S2Point.new(0.70710678116886982, 7.0710678116886989e-6, -0.70710678116886982), S2Point.new(0.70710678116886982, 0.70710678116886982, 7.0710678116886989e-6), 1, 0, 0),
	(S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), S2Point.new(0.0, -1.0, 0.0), S2Point.new(0.0, 0.0, -1.0), S2Point.new(0.0, 0.0, 1.0), -1, 0, 0),
	(S2Point.new(0.0, -0.70710678118654746, 0.70710678118654746), S2Point.new(0.0, 0.70710678118654746, 0.70710678118654746), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, -1.0, 0.0), S2Point.new(1.0, 0.0, 0.0), -1, 0, 0),
]

expect circumcenter_cases.all(
	|(x0, x1, a, b, c, expected, triaged, exact)| {
		abc = S2Predicates.sign(a, b, c)
		S2Predicates.edge_circumcenter_sign(x0, x1, a, b, c) == expected
			and triage_edge_circumcenter_sign(x0, x1, a, b, c, abc) == triaged
			and exact_edge_circumcenter_sign(x0, x1, a, b, c, abc) == exact
	},
)

# The identities that upstream's test checks: the order of a, b, c does not
# matter, reversing the edge negates the answer, and so does negating a, b, c
# when the answer is not symbolic.
expect circumcenter_cases.all(
	|(x0, x1, a, b, c, expected, _triaged, exact)|
		S2Predicates.edge_circumcenter_sign(x0, x1, a, c, b) == expected
			and S2Predicates.edge_circumcenter_sign(x0, x1, b, a, c) == expected
			and S2Predicates.edge_circumcenter_sign(x0, x1, b, c, a) == expected
			and S2Predicates.edge_circumcenter_sign(x0, x1, c, a, b) == expected
			and S2Predicates.edge_circumcenter_sign(x0, x1, c, b, a) == expected
			and S2Predicates.edge_circumcenter_sign(x1, x0, a, b, c) == -expected
			and S2Predicates.edge_circumcenter_sign(-x0, -x1, a, b, c) == expected
			and (exact == 0 or S2Predicates.edge_circumcenter_sign(x0, x1, -a, -b, -c) == -expected),
)
expect {
	# A degenerate edge or triangle gives 0.
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	S2Predicates.edge_circumcenter_sign(a, a, a, b, c) == 0 and S2Predicates.edge_circumcenter_sign(a, b, c, c, a) == 0
}

# GetVoronoiSiteExclusion, for the cases of upstream's
# VoronoiSiteExclusion.Coverage test: sites a and b, the edge x0x1, the
# squared chord length of r, the result, and the results of the triage and the
# exact step. Those two are compared only when a is not closer to both
# endpoints, since upstream answers that case first.
voronoi_cases : List((S2Point, S2Point, S2Point, S2Point, F64, S2Predicates.Excluded, [First, Second, Neither, Uncertain], S2Predicates.Excluded))
voronoi_cases = [
	(S2Point.new(0.99999999995, -9.9999999995000007e-6, 0.0), S2Point.new(0.99999999979999998, -1.9999999996e-5, 0.0), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 9.9999991666666942e-7, Second, Neither, Neither),
	(S2Point.new(0.70710678118654746, 0.70710678118654746, 7.0710678118654753e-31), S2Point.new(0.70710678118654746, 0.70710678118654746, -7.0710678118654736e-21), S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 1.0000000000000001e-20, Second, Uncertain, Second),
	(S2Point.new(0.99999999995, -9.9999999995000007e-11, 9.9999999995000007e-6), S2Point.new(0.99999999995, 9.9999999995000007e-11, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 9.9999999916666684e-9, Neither, Neither, Neither),
	(S2Point.new(0.99999999995, -9.9999999995000007e-11, 9.9999999995000007e-6), S2Point.new(0.99999999995, 9.9999999995000007e-11, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 9.9999999999166671e-11, Neither, Uncertain, Neither),
	(S2Point.new(0.99999999995, -9.9999999995e-18, 9.9999999995000007e-6), S2Point.new(0.99999999995, 9.9999999995e-18, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 9.9999999916666684e-9, Neither, Uncertain, Neither),
	(S2Point.new(0.99999999995, -9.9999999994999994e-21, 9.9999999995000007e-6), S2Point.new(0.99999999995, 9.9999999994999994e-21, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 9.9999999999166671e-11, Neither, Uncertain, Neither),
	(S2Point.new(0.9999999999489988, -9.9999999994899883e-7, 1.0049999998487438e-5), S2Point.new(0.99999999995, 0.0, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 1.010024999991499e-10, First, First, First),
	(S2Point.new(0.99999999994899769, -1.001049999948944e-6, 1.0049999998487427e-5), S2Point.new(0.99999999995, 0.0, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 1.010024999991499e-10, First, Uncertain, First),
	(S2Point.new(0.9999999999489988, -9.9999999994899883e-7, 1.0049999999487439e-5), S2Point.new(0.99999999995, 0.0, -9.9999999995000007e-6), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 1.010024999991499e-10, First, Uncertain, First),
	(S2Point.new(1.0, -1.0000000000000001e-31, 1.005e-30), S2Point.new(1.0, 0.0, -1.0000000000000001e-30), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(0.70710678118654746, 0.70710678118654746, 0.0), 1.0100250000000001e-60, First, Uncertain, First),
	(S2Point.new(0.99999999495000003, -9.9999999495000015e-6, 9.9999999495000005e-5), S2Point.new(0.99999999995, -1.0000000099500001e-5, 0.0), S2Point.new(-0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(1.0, 0.0, 0.0), 0.91939538826372058, First, First, First),
	(S2Point.new(0.99503719020998926, 9.9503719020998924e-11, 0.099503719020998929), S2Point.new(1.0, -1.0e-10, 1.0e-8), S2Point.new(-0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(1.0, 0.0, 0.0), 0.91939538826372058, First, First, First),
	(S2Point.new(0.99503719020998926, 1.9900743804199785e-10, 0.099503719020998929), S2Point.new(1.0, 1.0e-10, 0.0), S2Point.new(-0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(1.0, 0.0, 0.0), 0.91939538826372058, First, First, First),
	(S2Point.new(0.67267279399631241, 0.7399400733959437, 0.0), S2Point.new(0.7035627157549601, 0.71059834291250967, 0.007035627157549601), S2Point.new(-0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(1.0, 0.0, 0.0), 0.91939538826372058, First, First, First),
	(S2Point.new(0.67267279399631241, 0.7399400733959437, 0.0), S2Point.new(0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(-1.0, 0.0, 0.0), S2Point.new(1.0, -1.0e-10, 0.0), 1.3159597133486622, First, First, First),
	(S2Point.new(-0.99503669761768654, 0.099503669761768665, 0.00099503669761768663), S2Point.new(0.67267279399631241, 0.7399400733959437, 0.0), S2Point.new(-0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(1.0, 0.0, 0.0), 0.91939538826372058, Neither, Neither, Neither),
	(S2Point.new(-0.99503719020998926, 0.099503719020998929, 0.0), S2Point.new(0.67267264180794917, 0.73993990598874415, 0.00067267264180794915), S2Point.new(-0.70710678118654746, -0.70710678118654746, 0.0), S2Point.new(1.0, 0.0, 0.0), 0.91939538826372058, Neither, Neither, Neither),
	(S2Point.new(0.0, 0.70710678118654746, 0.70710678118654746), S2Point.new(0.70710678118654746, 0.0, 0.70710678118654746), S2Point.new(0.0, 0.70710678118654746, 0.70710678118654746), S2Point.new(0.70710678118654746, 0.0, -0.70710678118654746), 1.0, Neither, Uncertain, Neither),
	(S2Point.new(0.0, 0.70710678118654746, 0.70710678118654746), S2Point.new(-0.70710678118654746, 0.0, 0.70710678118654746), S2Point.new(0.0, 0.70710678118654746, 0.70710678118654746), S2Point.new(-0.70710678118654746, 0.0, -0.70710678118654746), 1.0, Second, Uncertain, Second),
]

expect voronoi_cases.all(
	|(a, b, x0, x1, r2, expected, triaged, exact)| {
		r = S1ChordAngle.from_length2(r2)
		decided_first = S2Predicates.compare_distances(x1, a, b) < 0
		S2Predicates.get_voronoi_site_exclusion(a, b, x0, x1, r) == expected
			and (decided_first or triage_voronoi_site_exclusion(a, b, x0, x1, r2) == triaged)
			and (decided_first or exact_voronoi_site_exclusion(a, b, x0, x1, r2) == exact)
	},
)

# Swapping the sites and reversing the edge excludes the same site, when b is
# the closer site to x1.
expect voronoi_cases.all(
	|(a, b, x0, x1, r2, expected, _triaged, _exact)| {
		swapped = match expected {
			First => Second
			Second => First
			Neither => Neither
		}
		S2Predicates.compare_distances(x1, b, a) >= 0
			or S2Predicates.get_voronoi_site_exclusion(b, a, x1, x0, S1ChordAngle.from_length2(r2)) == swapped
	},
)

# Upstream's SymbolicCrossProdConsistentWithSign: for exactly proportional
# inputs, S2Point.robust_cross agrees with the symbolic perturbation of sign.
expect {
	values = [-1.0, 0.0, 1.0]
	scales = [-1.0, 1.0 - dbl_err, 1.0 + 2.0 * dbl_err]
	var $ok = Bool.True
	for x in values {
		for y in values {
			for z in values {
				a = S2Point.new(x, y, z).normalize()
				if a != S2Point.zero() {
					for scale in scales {
						b = a * scale
						if S2Predicates.sign(a, b, a.robust_cross(b).normalize()) <= 0 {
							$ok = Bool.False
						}
					}
				}
			}
		}
	}
	$ok
}

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

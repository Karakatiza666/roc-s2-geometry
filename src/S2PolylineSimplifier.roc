import S1ChordAngle
import S1Interval
import Internal/S2Math
import S2LatLng
import S2Point

## Finds the end of a simplified edge that passes near some points and away
## from others. Upstream's `S2PolylineSimplifier`.
##
## Start an edge at a source vertex with `new`. Then add constraints: each
## `target_disc` requires the edge to pass through a disc, and each
## `avoid_disc` requires the edge to miss a disc on a given side. `extend`
## tells if an edge from the source to a given destination satisfies all the
## constraints so far.
##
##     s0 = S2PolylineSimplifier.new(a)
##     (_, s1) = s0.target_disc(b, radius)
##     ok = s1.extend(c)
##
## Upstream changes the simplifier in place. Here a constraint returns a new
## simplifier, and the old one stays usable. To start a new edge, call `new`
## again.
##
## The output edge cannot be longer than 90 degrees. The results are
## conservative: the error bounds are those of upstream, so an edge that
## `extend` accepts passes through each target disc and misses each disc to
## avoid, in spite of rounding errors.
S2PolylineSimplifier := {
	src : S2Point,
	x_dir : S2Point,
	y_dir : S2Point,
	window : S1Interval,
	ranges_to_avoid : List({ interval : S1Interval, on_left : Bool }),
}.{

	## A simplifier for an edge that starts at `src`, with no constraint.
	new : S2Point -> S2PolylineSimplifier
	new = |src| {
		# The basis vectors of the tangent space at `src`, as upstream makes
		# them: not normalized, but of the same magnitude.
		tmp = src.abs()
		i =
			if tmp.x < tmp.y {
				if (tmp.x < tmp.z) 0 else 2
			} else if tmp.y < tmp.z {
				1
			} else {
				2
			}
		j = if (i == 2) 0 else i + 1
		k = if (i == 0) 2 else i - 1
		si = src.coord(i)
		sj = src.coord(j)
		sk = src.coord(k)
		y_dir =
			S2Point.zero()
				.with_coord(i, 0.0)
				.with_coord(j, sk)
				.with_coord(k, -sj)
		x_dir =
			S2Point.zero()
				.with_coord(i, sj * sj + sk * sk)
				.with_coord(j, -sj * si)
				.with_coord(k, -sk * si)
		{ src: src, x_dir: x_dir, y_dir: y_dir, window: S1Interval.full(), ranges_to_avoid: [] }
	}

	## The source vertex of the output edge.
	src : S2PolylineSimplifier -> S2Point
	src = |s| s.src

	## True when the edge from the source to `dst` satisfies all the
	## constraints so far. False when the edge is longer than 90 degrees,
	## because such edges are not supported.
	extend : S2PolylineSimplifier, S2Point -> Bool
	extend = |s, dst| {
		# The limit of 90 degrees keeps the error bounds simple. The error
		# gets very large as the edge length approaches 180 degrees.
		if S1ChordAngle.from_points(s.src, dst) > S1ChordAngle.right() {
			return Bool.False
		}
		dir = direction(s, dst)
		if !s.window.contains_point(dir) {
			return Bool.False
		}
		!s.ranges_to_avoid.any(|range| range.interval.contains_point(dir))
	}

	## Adds the constraint that the output edge must pass through the disc
	## with the given center and radius. Returns the new simplifier, and true
	## when the constraints so far can still be satisfied.
	target_disc : S2PolylineSimplifier, S2Point, S1ChordAngle -> (Bool, S2PolylineSimplifier)
	target_disc = |s, p, r| {
		# The interval shrinks by the maximum error from all sources, so
		# that the output edge surely meets the disc.
		semiwidth = semiwidth_of(s, p, r, -1.0)
		if semiwidth >= F64.pi {
			# The disc contains the source vertex, so nothing changes.
			return (Bool.True, s)
		}
		if semiwidth < 0.0 {
			return (Bool.False, { ..s, window: S1Interval.empty() })
		}
		center = direction(s, p)
		target = S1Interval.from_point(center).expanded(semiwidth)
		narrowed = { ..s, window: s.window.intersection(target), ranges_to_avoid: [] }
		# The window is now at most 180 degrees wide, so the ranges to avoid
		# that were kept for later can be applied.
		window = s.ranges_to_avoid.fold(narrowed.window, |w, range| avoid_range(w, range.interval, range.on_left))
		(!window.is_empty(), { ..narrowed, window: window })
	}

	## Adds the constraint that the output edge must not meet the disc with
	## the given center and radius, and must pass it on the given side.
	## Returns the new simplifier, and true when the disc can be avoided as
	## far as the constraints so far tell.
	##
	## Let AB be the output edge, P the center of the disc, and r its radius.
	## The constraint is that the distance from AB to P is more than r, and
	## that when P is not behind A with respect to the direction AB, P is to
	## the left of AB exactly when `disc_on_left` is true.
	##
	## To simplify a polyline ABCDE that already avoid_discs points X_i, when ABC
	## is added and D is next: find the X_i near the edge CD, and drop those
	## with AX_i <= AC or AX_i >= AD. Then X_i is on the left exactly when
	## `S2Predicates.ordered_ccw(A, D, X_i, C)` is true, that is, when X_i is
	## to the left of the wedge ACD. The sign of CDX_i or of ADX_i alone does
	## not handle all cases correctly.
	##
	## The discs to avoid cannot be applied until a target disc that does
	## not contain the source vertex reduces the allowed directions to at
	## most 180 degrees. Until then this keeps the disc for later and
	## returns true.
	avoid_disc : S2PolylineSimplifier, S2Point, S1ChordAngle, Bool -> (Bool, S2PolylineSimplifier)
	avoid_disc = |s, p, r, disc_on_left| {
		# The interval grows by the maximum error from all sources, so that
		# the output edge surely misses the disc.
		semiwidth = semiwidth_of(s, p, r, 1.0)
		if semiwidth >= F64.pi {
			# The disc contains the source vertex, so it cannot be avoided.
			return (Bool.False, { ..s, window: S1Interval.empty() })
		}
		# The directions not allowed: the angle the disc subtends on one
		# side, and 90 degrees on the other, to satisfy `disc_on_left`.
		center = direction(s, p)
		half_pi = 0.5 * F64.pi
		dleft = if (disc_on_left) half_pi else semiwidth
		dright = if (disc_on_left) semiwidth else half_pi
		avoid_interval =
			S1Interval.new(
				S2Math.remainder(center - dright, 2.0 * F64.pi),
				S2Math.remainder(center + dleft, 2.0 * F64.pi),
			)
		if s.window.is_full() {
			kept = s.ranges_to_avoid.append({ interval: avoid_interval, on_left: disc_on_left })
			return (Bool.True, { ..s, ranges_to_avoid: kept })
		}
		window = avoid_range(s.window, avoid_interval, disc_on_left)
		(!window.is_empty(), { ..s, window: window })
	}
}

# Half of the machine epsilon: the largest relative rounding error.
dbl_err : F64
dbl_err = 0.5 * 2.220446049250313e-16

# The direction of `p` from the source, as an angle in the tangent plane.
direction : S2PolylineSimplifier, S2Point -> F64
direction = |s, p| S2Math.atan2(p.dot(s.y_dir), p.dot(s.x_dir))

# Removes the directions in `avoid_interval` from the window.
#
# When `avoid_interval` is a proper subset of the window, the exact result is
# two intervals: one towards the disc that passes it on the correct side, and
# one away from it. The second never holds an acceptable direction when the
# simplifier is used correctly, so it is dropped. See upstream's comment.
avoid_range : S1Interval, S1Interval, Bool -> S1Interval
avoid_range = |window, avoid_interval, disc_on_left|
	if window.contains_interval(avoid_interval) {
		if disc_on_left {
			S1Interval.new(window.lo(), avoid_interval.lo())
		} else {
			S1Interval.new(avoid_interval.hi(), window.hi())
		}
	} else {
		window.intersection(avoid_interval.complement())
	}

# Half the angle in radians that the disc of radius `r` around `p` subtends
# from the source, rounded conservatively up (`round_direction` 1) or down
# (-1). Pi means that the disc contains the source.
semiwidth_of : S2PolylineSimplifier, S2Point, S1ChordAngle, F64 -> F64
semiwidth_of = |s, p, r, round_direction| {
	# sin(semiwidth) = sin(r) / sin(a), where `a` is the angle from the
	# source to `p`, through sin^2 = d2 (1 - d2 / 4) for a squared chord d2.
	# The absolute error of `a2`, which comes from points that are not quite
	# unit length, is taken into account here.
	r2 = r.length2()
	a2 = S1ChordAngle.from_points(s.src, p).length2() - 64.0 * dbl_err * dbl_err * round_direction
	if a2 <= r2 {
		F64.pi
	} else {
		sin2_r = r2 * (1.0 - 0.25 * r2)
		sin2_a = a2 * (1.0 - 0.25 * a2)
		semiwidth = (sin2_r / sin2_a).sqrt().asin()
		# Upstream's bound on the errors of this function and of the two
		# calls of `direction`: 10 * dbl_err for each direction, 4 * dbl_err
		# for the sum with the center, and a relative 17 * dbl_err here.
		error = (2.0 * 10.0 + 4.0) * dbl_err + 17.0 * dbl_err * semiwidth
		semiwidth + round_direction * error
	}
}

# Helpers of the tests below.
Op : [Target(S2Point, F64), Avoid(S2Point, F64, Bool), Extend(S2Point), Restart(S2Point)]

# Runs the operations from `src` and lists the result of each one but
# `Restart`, as the "simp" query of tools/s2_oracle.cc does. Radii are in
# degrees.
run_ops : S2Point, List(Op) -> List(Bool)
run_ops = |src, ops| {
	(_, results) =
		ops.fold(
			(S2PolylineSimplifier.new(src), []),
			|(s, out), op|
				match op {
					Target(p, deg) => {
						(ok, next) = s.target_disc(p, S1ChordAngle.from_degrees(deg))
						(next, out.append(ok))
					}
					Avoid(p, deg, left) => {
						(ok, next) = s.avoid_disc(p, S1ChordAngle.from_degrees(deg), left)
						(next, out.append(ok))
					}
					Extend(p) => (s, out.append(s.extend(p)))
					Restart(p) => (S2PolylineSimplifier.new(p), out)
				},
		)
	results
}

ll : F64, F64 -> S2Point
ll = |lat, lng| S2LatLng.from_degrees(lat, lng).to_point()

unit : F64, F64, F64 -> S2Point
unit = |x, y, z| S2Point.new(x, y, z).normalize()

# Upstream's CheckSimplify: target the discs, avoid the discs, then extend.
check_simplify : (F64, F64), (F64, F64), List((F64, F64)), List((F64, F64, Bool)), F64 -> List(Bool)
check_simplify = |(src_lat, src_lng), (dst_lat, dst_lng), target_discs, avoid_discs, radius| {
	ops =
		target_discs.map(|(lat, lng)| Target(ll(lat, lng), radius))
			.concat(avoid_discs.map(|(lat, lng, left)| Avoid(ll(lat, lng), radius, left)))
			.append(Extend(ll(dst_lat, dst_lng)))
	run_ops(ll(src_lat, src_lng), ops)
}

# The expected results below are the answers of upstream's
# S2PolylineSimplifier, through the "simp" query of tools/s2_oracle.cc. The
# cases come from s2polyline_simplifier_test.cc, under the test names in the
# comments.
# Src.
expect S2PolylineSimplifier.new(S2Point.new(1.0, 0.0, 0.0)).src() == S2Point.new(1.0, 0.0, 0.0)
# Reuse.
expect
	run_ops(
		S2Point.new(1.0, 0.0, 0.0),
		[
			Target(unit(1.0, 1.0, 0.0), 10.0),
			Target(unit(1.0, 1.0, 0.1), 10.0),
			Extend(unit(1.0, 1.0, 0.4)),
			Restart(S2Point.new(0.0, 1.0, 0.0)),
			Target(unit(1.0, 1.0, 0.3), 10.0),
			Target(unit(1.0, 1.0, 0.2), 10.0),
			Extend(unit(1.0, 1.0, 0.0)),
		],
	)
		== [Bool.True, Bool.True, Bool.False, Bool.True, Bool.True, Bool.False]
# NoConstraints: dst == src, dst != src, and an edge longer than 90 degrees.
expect check_simplify((0.0, 1.0), (0.0, 1.0), [], [], 0.0) == [Bool.True]
expect check_simplify((0.0, 1.0), (1.0, 0.0), [], [], 0.0) == [Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 91.0), [], [], 0.0) == [Bool.False]
# TargetOnePoint.
expect check_simplify((0.0, 0.0), (0.0, 2.0), [(0.0, 1.0)], [], 1.0e-10) == [Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [(1.0, 1.0)], [], 0.9) == [Bool.True, Bool.False]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [(0.0, 0.1)], [], 1.0) == [Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [(0.0, 2.1)], [], 1.0) == [Bool.True, Bool.True]
# AvoidOnePoint.
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(0.0, 1.0, Bool.True)], 1.0e-10) == [Bool.True, Bool.False]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(1.0, 1.0, Bool.True)], 0.9) == [Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(1.0, 1.0, Bool.False)], 1.0e-10) == [Bool.True, Bool.False]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(1.0, -1.0, Bool.False)], 1.4) == [Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(1.0, -1.0, Bool.True)], 1.4) == [Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(-1.0, -1.0, Bool.False)], 1.4) == [Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(-1.0, -1.0, Bool.True)], 1.4) == [Bool.True, Bool.True]
# AvoidSeveralPoints: three gaps between three small discs, and the same
# discs on the wrong side.
expect {
	ops = |left| [
		Avoid(ll(0.01, 2.0), 0.00001, left),
		Avoid(ll(1.732, -1.01), 0.00001, left),
		Avoid(ll(-1.732, -0.99), 0.00001, left),
		Extend(ll(0.0, 2.0)),
		Extend(ll(1.732, -1.0)),
		Extend(ll(-1.732, -1.0)),
	]
	run_ops(ll(0.0, 0.0), ops(Bool.True)) == [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]
		and run_ops(ll(0.0, 0.0), ops(Bool.False)) == [Bool.True, Bool.True, Bool.True, Bool.False, Bool.False, Bool.False]
}
# TargetAndAvoid, and the same with the avoided discs first.
expect check_simplify((0.0, 0.0), (10.0, 10.0), [(2.0, 3.0), (4.0, 3.0), (7.0, 8.0)], [(4.0, 2.0, Bool.True), (7.0, 5.0, Bool.True), (7.0, 9.0, Bool.False)], 1.0) == [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]
expect check_simplify((0.0, 0.0), (10.0, 10.0), [(2.0, 3.0), (4.0, 6.0), (7.0, 8.0)], [(4.0, 2.0, Bool.True), (7.0, 5.0, Bool.True), (7.0, 9.0, Bool.False)], 1.0) == [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.False, Bool.False]
expect check_simplify((0.0, 0.0), (10.0, 10.0), [(2.0, 3.0), (4.0, 3.0), (7.0, 8.0)], [(4.0, 2.0, Bool.True), (6.0, 5.0, Bool.True), (7.0, 9.0, Bool.False)], 1.0) == [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.False, Bool.False]
expect
	run_ops(
		ll(0.0, 0.0),
		[
			Avoid(ll(4.0, 2.0), 1.0, Bool.True),
			Avoid(ll(7.0, 5.0), 1.0, Bool.True),
			Avoid(ll(7.0, 9.0), 1.0, Bool.False),
			Target(ll(2.0, 3.0), 1.0),
			Target(ll(4.0, 3.0), 1.0),
			Target(ll(7.0, 8.0), 1.0),
			Extend(ll(10.0, 10.0)),
		],
	)
		== [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]
# Not from upstream's tests: a disc to avoid that contains the source, a
# target window tested at several destinations, and an edge across the
# antimeridian.
expect check_simplify((0.0, 0.0), (0.0, 2.0), [], [(0.0, 0.5, Bool.True)], 1.0) == [Bool.False, Bool.False]
expect run_ops(ll(0.0, 0.0), [Target(ll(0.0, 50.0), 1.0), Extend(ll(0.0, 50.0)), Extend(ll(0.0, 49.0)), Extend(ll(1.0, 50.0))]) == [Bool.True, Bool.True, Bool.True, Bool.True]
expect run_ops(ll(10.0, 170.0), [Target(ll(10.0, -175.0), 0.5), Avoid(ll(11.0, -178.0), 0.3, Bool.False), Extend(ll(10.0, -170.0)), Extend(ll(9.0, -170.0))]) == [Bool.True, Bool.False, Bool.False, Bool.False]

# Cases in the manner of upstream's Precision test, from the
# "simp_precision 7 30" query of tools/s2_oracle.cc. Each has a source, a
# destination, five discs (avoid, on the left, center, squared chord radius)
# that miss or meet the edge by 25 machine epsilons, and the results of the
# five calls and of `extend`. The discs are so close to the edge that these
# check the error bounds of `semiwidth_of`.
expect {
	cases = [
		(S2Point.new(0.6235027488073258, 0.7317740811173679, 0.27522902542163047), S2Point.new(0.5694845468908598, 0.6124431832745498, 0.5482706431253168), [(Bool.True, Bool.False, S2Point.new(0.3582853248515805, 0.7817557270679039, 0.510381826863507), 0.07118945841936584), (Bool.True, Bool.True, S2Point.new(0.6548793565581377, 0.7410732531665944, 0.14813325688406445), 0.017224300494902523), (Bool.False, Bool.False, S2Point.new(0.3358525698514048, 0.888797771262289, 0.3118358111625337), 0.10852065643849329), (Bool.False, Bool.True, S2Point.new(0.6290528636854081, 0.6969186390919634, 0.34437901384287806), 0.0003172739844090495), (Bool.True, Bool.False, S2Point.new(-0.22359806985074365, 0.9307893210325991, 0.2891974118326358), 0.756097280485328)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.32975067236038597, 0.5021765288929064, -0.7994268121016116), S2Point.new(0.20845121205328065, 0.5135737219558388, -0.8323401494040432), [(Bool.False, Bool.False, S2Point.new(0.3327960360650297, -0.02139855383293782, -0.9427560131196526), 0.29468340135594395), (Bool.True, Bool.False, S2Point.new(0.3378048989014927, 0.4764499850159703, -0.8117162447902804), 0.0008777557808363803), (Bool.False, Bool.True, S2Point.new(0.3338496345832151, 0.5617879100089223, -0.7569271864958088), 0.005376536426497286), (Bool.True, Bool.True, S2Point.new(0.26329851975812985, 0.7373487909134748, -0.622085725629205), 0.08981023858286528), (Bool.True, Bool.False, S2Point.new(0.2742186467902749, 0.39659568504504417, -0.8760799029518728), 0.016060411083040398)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.8502524283219802, 0.027790491989078823, 0.5256410340599188), S2Point.new(0.8511802421179075, 0.025589148915709677, 0.5242493594520362), [(Bool.True, Bool.False, S2Point.new(0.8078288936700307, -0.02970772763750551, 0.5886679280124489), 0.009078190913894503), (Bool.False, Bool.True, S2Point.new(0.8914530918607569, 0.09581949652528994, 0.4428656783919217), 0.013175452253418823), (Bool.True, Bool.True, S2Point.new(0.9389178432453477, 0.3223220740341644, 0.12058923760360804), 0.25867736643799305), (Bool.True, Bool.True, S2Point.new(0.9117888593200423, 0.4087275547447076, -0.03978519840679867), 0.46860311927740994), (Bool.False, Bool.True, S2Point.new(0.8315608602906908, 0.5014368943125661, -0.23888820953486772), 0.809193956870775)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.4867051761651359, -0.26545164560588347, -0.8322580701556413), S2Point.new(-0.5895497820910559, 0.25992135467674876, -0.7647692095131656), [(Bool.True, Bool.False, S2Point.new(-0.6935984364960028, -0.40094030953744236, -0.5984714505123199), 0.11581818274854214), (Bool.True, Bool.True, S2Point.new(-0.4479127695734554, -0.2621865797677792, -0.8547703482472417), 0.0020223141289744694), (Bool.True, Bool.True, S2Point.new(0.27866752023305036, 0.27278914210785676, -0.9208314162294975), 0.7703084705420694), (Bool.False, Bool.False, S2Point.new(-0.6734906464372354, -0.4534934422663789, -0.5837414213356334), 0.13200905393680756), (Bool.False, Bool.False, S2Point.new(-0.9563540488548403, -0.0691285669574973, -0.2839157876366808), 0.4516259369650154)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.False]),
		(S2Point.new(-0.22272730172187333, -0.8026958634811746, 0.5532376522055462), S2Point.new(-0.7459700792929475, -0.40985774361315075, 0.5249240619365916), [(Bool.True, Bool.False, S2Point.new(-0.5887793095182601, -0.27156981792284746, 0.761307269554516), 0.0981367982927174), (Bool.False, Bool.True, S2Point.new(-0.23420807704780297, -0.9242924535553947, -0.3013802198985842), 0.7452892462395629), (Bool.False, Bool.False, S2Point.new(-0.10433289569805679, -0.43165569278476057, 0.8959843803112679), 0.2629971848240692), (Bool.False, Bool.False, S2Point.new(-0.22724451082175182, 0.05256237687737619, 0.9724181861927427), 0.6797865407660191), (Bool.True, Bool.False, S2Point.new(0.040934538210919635, -0.2350156894441911, 0.9711292340860357), 0.5658443018488597)], [Bool.True, Bool.True, Bool.True, Bool.False, Bool.False, Bool.False]),
		(S2Point.new(0.1051688980599784, 0.9245522734534098, 0.3662548245866276), S2Point.new(0.0424544805635097, 0.8107779474411015, 0.5838122446671337), [(Bool.False, Bool.True, S2Point.new(0.21730881642290462, 0.7921652010478359, 0.5703079629057605), 0.02905561728853278), (Bool.True, Bool.True, S2Point.new(0.6108513133300059, 0.6370720404419185, 0.47010625212836477), 0.342954815242671), (Bool.False, Bool.True, S2Point.new(0.7221112968571919, 0.45273440685896327, 0.5230552856030493), 0.5931206709710718), (Bool.True, Bool.True, S2Point.new(0.7669440774232535, 0.4859063625625393, 0.41915604364799125), 0.6309555775876975), (Bool.False, Bool.True, S2Point.new(0.4596796166472794, 0.7695394657351645, 0.44328733425967437), 0.1540384817378505)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.9650169107681492, 0.14824038687294336, 0.21625713775794322), S2Point.new(0.8367709431321538, 0.5170541953696416, 0.18019252975741842), [(Bool.False, Bool.True, S2Point.new(0.4180844267911277, 0.18740410148802536, 0.8888673212691534), 0.7424380997406285), (Bool.False, Bool.False, S2Point.new(0.6965390714350611, 0.1300071654809572, -0.7056425857953799), 0.91418226801317), (Bool.False, Bool.True, S2Point.new(0.38716514166250954, 0.12684789943503497, 0.9132429925766572), 0.8191141195587448), (Bool.False, Bool.True, S2Point.new(0.5398522368265667, 0.39979722169298415, 0.7407575473256574), 0.415390842209857), (Bool.True, Bool.False, S2Point.new(0.728290744570223, 0.15233838517550904, -0.6681209529534818), 0.8266539554390192)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.48844867168540446, 0.8712922838544419, 0.04761986165954759), S2Point.new(-0.4594914076260574, 0.8867916668687478, -0.04968084027039496), [(Bool.False, Bool.False, S2Point.new(0.10707439637572769, 0.9664838835709005, 0.23333233046126187), 0.39819828631795673), (Bool.True, Bool.True, S2Point.new(-0.5913915795852211, 0.8045921287967248, -0.05373551780760901), 0.022104275965786378), (Bool.False, Bool.True, S2Point.new(-0.8724548123859927, 0.47601566909533416, -0.11059693992260179), 0.3287368745740714), (Bool.True, Bool.False, S2Point.new(-0.09781756658376695, 0.9847086394894425, 0.14415484377044535), 0.17369795622512216), (Bool.False, Bool.True, S2Point.new(-0.7307070582455173, 0.6725441010412163, -0.11726733212981531), 0.122179759984896)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.False, Bool.False]),
		(S2Point.new(0.33803209005763746, 0.9411293587693079, -0.0031362642963118186), S2Point.new(0.31811479302840867, 0.9477755502748128, -0.022901632207524454), [(Bool.False, Bool.True, S2Point.new(-0.034044773109958404, 0.9350128642331379, 0.3529757741579939), 0.26518853777353013), (Bool.False, Bool.True, S2Point.new(0.20210546123447864, 0.9693462714342034, 0.13971824718270132), 0.03967478253028248), (Bool.False, Bool.True, S2Point.new(0.015434370858811386, 0.9470583570639141, 0.32069026881337165), 0.208967490130925), (Bool.False, Bool.True, S2Point.new(-0.1732431823079957, 0.8612464915876769, 0.4777460418587647), 0.4990284015359873), (Bool.False, Bool.True, S2Point.new(-0.3347495565612666, 0.7400441203680752, 0.5833330389157443), 0.8368332813833312)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.False]),
		(S2Point.new(0.7278753686665096, 0.3500946210721826, -0.589602581392685), S2Point.new(0.6598670057282433, 0.38094755035191236, -0.6476530696539003), [(Bool.False, Bool.True, S2Point.new(0.5833113773969163, 0.7541744493370672, -0.30161024015514426), 0.2639114814323207), (Bool.False, Bool.False, S2Point.new(0.5439888631522833, -0.3855187171052491, -0.7452861433891075), 0.5991786016906798), (Bool.True, Bool.False, S2Point.new(0.4656101113985069, -0.4856794242086526, -0.7398126256450493), 0.7898643773292314), (Bool.True, Bool.False, S2Point.new(0.5829900921385407, -0.16253659673876114, -0.7960555302168795), 0.322660695628281), (Bool.False, Bool.False, S2Point.new(0.7027121685778264, 0.14004294439835116, -0.6975554328201372), 0.05619200782914796)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.09744252097654818, 0.045661785181055126, -0.994193118302382), S2Point.new(-0.44952030913739427, 0.6779363212220901, -0.5816647110156166), [(Bool.True, Bool.True, S2Point.new(0.04487152627418618, 0.19528460907296208, -0.9797195862026264), 0.03955280282308927), (Bool.True, Bool.False, S2Point.new(-0.6390942914253543, 0.2814802047794596, -0.7157704806604123), 0.13278042301097406), (Bool.True, Bool.True, S2Point.new(0.24858299507275283, 0.16984998738887927, -0.9536023680469011), 0.13680397633110333), (Bool.True, Bool.False, S2Point.new(-0.7399468689744495, 0.22570726824415643, -0.6336677837452914), 0.24348333021130752), (Bool.False, Bool.False, S2Point.new(-0.7691312353908906, -0.20575468418393683, -0.6050637591877827), 0.6271061876656839)], [Bool.True, Bool.True, Bool.False, Bool.False, Bool.False, Bool.False]),
		(S2Point.new(0.7070074330195426, -0.0553808565436721, -0.7050343611368215), S2Point.new(0.7207001718515987, 0.3273344714001445, -0.61110016046984), [(Bool.True, Bool.True, S2Point.new(0.9610861646204614, -0.21590994665768, 0.17232608365946575), 0.860086940717893), (Bool.True, Bool.False, S2Point.new(0.5441381772300208, 0.11840107309465572, -0.8305990789609778), 0.05544098677884052), (Bool.True, Bool.False, S2Point.new(0.35376810723345276, 0.12742268795236972, -0.9266129639172191), 0.19750691197191705), (Bool.False, Bool.True, S2Point.new(0.8109245418093332, -0.23281599705923323, -0.5368408507226683), 0.07057105153444489), (Bool.True, Bool.True, S2Point.new(0.8809033872007569, -0.21291268813600978, -0.4227025072659634), 0.13476735655558317)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.27000349461962486, -0.9133298827804271, -0.30483870835817656), S2Point.new(0.1403157916575092, -0.8556376791535226, 0.4981923731093244), [(Bool.False, Bool.True, S2Point.new(-0.397249287806874, -0.9122590316852205, -0.09988224289469803), 0.04223952568669892), (Bool.False, Bool.True, S2Point.new(-0.6215361803314047, -0.6894014208434215, 0.37204631093201196), 0.4619709675345784), (Bool.False, Bool.True, S2Point.new(-0.32728783760018826, -0.8997071733222698, -0.2888073296013174), 0.0037240792685427414), (Bool.True, Bool.True, S2Point.new(-0.650463576366625, -0.7268207555565981, 0.22051921710471356), 0.38981094918623166), (Bool.True, Bool.True, S2Point.new(-0.9342639390394655, -0.35594457381527367, 0.021315547891746833), 0.8582969195409552)], [Bool.True, Bool.True, Bool.True, Bool.False, Bool.False, Bool.False]),
		(S2Point.new(0.8358181986544432, 0.5488811552309028, 0.011722466908943558), S2Point.new(0.9975988529882656, 0.05416400188908056, 0.043160044205919755), [(Bool.True, Bool.True, S2Point.new(0.9089205162081616, 0.398288118915578, -0.1234101679221756), 0.02127556884530854), (Bool.False, Bool.False, S2Point.new(0.9248586530368912, 0.3599849808664566, 0.12266737729879204), 0.00952353696345765), (Bool.False, Bool.True, S2Point.new(0.9959670484608607, 0.07746463168666537, -0.0452644365679188), 0.007587689016927504), (Bool.True, Bool.False, S2Point.new(0.7608569331519024, 0.6431677214737379, 0.08620910235562018), 0.020057406759771503), (Bool.False, Bool.True, S2Point.new(0.7907590144294191, 0.013086316258941428, -0.611987687315182), 0.47367642454694014)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.646612291100203, -0.7626075638793802, -0.017951281628430044), S2Point.new(0.6419313870902804, -0.7665133501454542, -0.019528909778611537), [(Bool.False, Bool.False, S2Point.new(0.5333701794041377, -0.7764255127841364, 0.3356779331744774), 0.1380516983519095), (Bool.False, Bool.False, S2Point.new(0.2880057871788754, -0.6348832745467535, 0.7169211213601312), 0.6849424809893981), (Bool.True, Bool.False, S2Point.new(0.572332388266121, -0.7837664438141011, 0.24113440006062142), 0.07307918820727655), (Bool.True, Bool.True, S2Point.new(0.6685315688343707, -0.6542244646423426, -0.3536324240440847), 0.12490902298857844), (Bool.True, Bool.True, S2Point.new(0.6129467008804377, -0.4866457601789271, -0.622472686934665), 0.4427070712588514)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.158101403143277, 0.026150762930329047, 0.9870765339740828), S2Point.new(-0.25418928644610467, 0.11220298018642476, 0.9606239107441085), [(Bool.False, Bool.True, S2Point.new(-0.5609718897282272, -0.31845280345947785, 0.7641324171264698), 0.3181194479425204), (Bool.False, Bool.True, S2Point.new(-0.2882414248255129, -0.10202988478530306, 0.9521064980480157), 0.034291261940083036), (Bool.True, Bool.True, S2Point.new(-0.22400343683144747, -0.08216708881073519, 0.971118442726771), 0.016330495726294865), (Bool.True, Bool.True, S2Point.new(-0.1916307786323805, -0.01280111977013949, 0.9813836028859348), 0.0026738730829153107), (Bool.False, Bool.True, S2Point.new(-0.3712578325194953, -0.1946886325128744, 0.9078898381208996), 0.09987602301058542)], [Bool.True, Bool.True, Bool.False, Bool.False, Bool.False, Bool.False]),
		(S2Point.new(-0.8262271859904904, -0.5510319352316967, 0.11710014297620175), S2Point.new(-0.9726184281490129, 0.1167722578961286, -0.20094186475392203), [(Bool.True, Bool.True, S2Point.new(-0.6971315384919712, -0.6716644441910753, -0.25074786629064505), 0.16653004634247423), (Bool.False, Bool.False, S2Point.new(-0.7214691677141722, -0.6355205371325654, 0.2749470620329576), 0.0430282161000572), (Bool.True, Bool.False, S2Point.new(-0.8619745248690079, 0.026527073854631017, 0.5062570817574398), 0.3835361633866325), (Bool.True, Bool.True, S2Point.new(-0.4590252603896006, -0.323063383331616, -0.8276024774458984), 0.8414772888841351), (Bool.False, Bool.False, S2Point.new(-0.9969669548112955, -0.016788217889848092, 0.07599372838843535), 0.04066709942061263)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.9530820186273069, -0.250493171867446, 0.16996422157937838), S2Point.new(-0.5112390844734702, -0.8205894885730025, 0.2554750276450248), [(Bool.True, Bool.False, S2Point.new(-0.6966194671680733, -0.27346212818355914, -0.6632795658029791), 0.760595822466518), (Bool.False, Bool.False, S2Point.new(-0.7459401735975024, -0.35920322665679727, -0.5608442737272742), 0.5882551293060739), (Bool.False, Bool.True, S2Point.new(-0.8277790388087909, 0.028510408280866782, 0.5603293848518502), 0.24592879518372435), (Bool.False, Bool.False, S2Point.new(-0.9510916636119857, -0.2955124844818471, -0.08998343693787011), 0.06960348518996312), (Bool.False, Bool.False, S2Point.new(-0.5557832293001187, -0.7432581786834505, -0.37238727401576455), 0.3908746379228553)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.6766187485600335, 0.6676285087947753, 0.310578884249266), S2Point.new(0.7201915809268342, 0.6006885060994077, 0.3471273619324315), [(Bool.False, Bool.True, S2Point.new(0.7516374312818149, 0.644085852696898, 0.1421076572595043), 0.0345646137368921), (Bool.True, Bool.False, S2Point.new(0.07445871156473677, 0.4874840440274512, 0.8699512670780827), 0.7031292602664806), (Bool.False, Bool.True, S2Point.new(0.7376501014283633, 0.6456353291214972, 0.19755340962104784), 0.016983283900015113), (Bool.False, Bool.False, S2Point.new(0.4977390962709086, 0.6189742557747594, 0.6075579501014713), 0.11745415711961239), (Bool.True, Bool.False, S2Point.new(0.33501628157724106, 0.6631758481184049, 0.6692995484464286), 0.2453925865578768)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.9201725934778927, 0.23923988444285538, 0.3099139814592722), S2Point.new(0.6736512635924301, 0.6458254258876417, 0.3593097470670237), [(Bool.True, Bool.False, S2Point.new(0.6861889687031693, 0.47086690240527407, -0.5544628566904578), 0.8264426594050928), (Bool.True, Bool.False, S2Point.new(0.759104325294193, 0.6501280605721518, 0.033077608383024315), 0.10963337347148867), (Bool.True, Bool.True, S2Point.new(0.5270591649132811, 0.02537558184706551, 0.8494496550866555), 0.4909267500724713), (Bool.True, Bool.True, S2Point.new(0.5027253928130613, 0.058810245294646485, 0.8624433514552343), 0.5073662701001515), (Bool.True, Bool.True, S2Point.new(0.5253950397909204, 0.2863242917634421, 0.801235578409534), 0.32076743401748375)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.12415585124098827, 0.22720336809641165, -0.9659005922600277), S2Point.new(0.20573419212586058, 0.2871542305285603, -0.9355297376780014), [(Bool.False, Bool.True, S2Point.new(0.17612533282314516, 0.09440109798462011, -0.9798307506081009), 0.020531319274367365), (Bool.False, Bool.False, S2Point.new(-0.010231585589922071, 0.3468127520860351, -0.9378785793730585), 0.0331516211225986), (Bool.False, Bool.True, S2Point.new(0.5652415370932754, -0.405999291826456, -0.7180992826767395), 0.6550658863464525), (Bool.True, Bool.True, S2Point.new(0.47733471288737894, -0.3471844153106797, -0.8072264574690952), 0.4798341150927958), (Bool.False, Bool.False, S2Point.new(0.13976152489472668, 0.2619159073724361, -0.9549171553723257), 0.00035073002575050784)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.False, Bool.False]),
		(S2Point.new(0.026531718119837566, 0.5153370191588436, -0.856576806023889), S2Point.new(0.05766473679642788, 0.5357920183340943, -0.8423785913825661), [(Bool.True, Bool.True, S2Point.new(0.34884071834719727, 0.11075004411912376, -0.9306151626481398), 0.2727939093737591), (Bool.True, Bool.True, S2Point.new(0.19509548897574827, 0.36801608443667483, -0.9091215055080438), 0.05148641624486935), (Bool.True, Bool.True, S2Point.new(0.0653071226888973, 0.4982520560011733, -0.8645691808159144), 0.0015110387066852395), (Bool.False, Bool.False, S2Point.new(-0.22351658942067548, 0.7360832744711348, -0.6389223327585297), 0.1586265350706909), (Bool.True, Bool.True, S2Point.new(0.27608130934004077, 0.1777883679937851, -0.9445477260780395), 0.18395297315669)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.False]),
		(S2Point.new(0.26968985772791204, -0.5154205711617278, 0.8133935182075261), S2Point.new(0.13404378824879162, -0.397851477614504, 0.907604795377299), [(Bool.True, Bool.True, S2Point.new(0.19512326745861475, -0.48288579570540197, 0.8536675106868216), 0.0005656944080715148), (Bool.True, Bool.True, S2Point.new(0.2769398079234799, -0.5536592856254715, 0.7853443437295506), 0.002301517250573319), (Bool.True, Bool.True, S2Point.new(0.013472679820896172, -0.7688438170829737, 0.6392946674513458), 0.16018099366251412), (Bool.True, Bool.False, S2Point.new(0.24833164749571213, -0.4246946352041799, 0.8706123475352587), 0.003209856223351931), (Bool.False, Bool.True, S2Point.new(0.1767134672330217, -0.6373424844533759, 0.750044604013176), 0.02752264705975949)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.9090451466727163, -0.4037077464891059, -0.10323263406243072), S2Point.new(-0.9942185407734269, -0.06566960995809712, 0.08495290171800694), [(Bool.False, Bool.False, S2Point.new(-0.7520079516557141, -0.5637727568159338, 0.34153231079758634), 0.24777936208589596), (Bool.True, Bool.True, S2Point.new(-0.9412558064304258, -0.30293105500441697, -0.14923231143060067), 0.008218507489092803), (Bool.True, Bool.True, S2Point.new(-0.8278593809192715, 0.08329467314400746, -0.5547169033388055), 0.4217928693300421), (Bool.False, Bool.True, S2Point.new(-0.6304505019445454, 0.009339452789554059, -0.7761732662360012), 0.7010720593333339), (Bool.False, Bool.False, S2Point.new(-0.860630463359231, -0.41956661139873624, 0.28858112228185906), 0.13196844191934615)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.False]),
		(S2Point.new(-0.23622003291429985, 0.9392788873264147, -0.2489081514792543), S2Point.new(-0.2251910483662787, 0.9681945417757649, 0.1090335774489351), [(Bool.True, Bool.False, S2Point.new(-0.4436376182249562, 0.8386874896528145, -0.31589390370114506), 0.05762777498276168), (Bool.True, Bool.False, S2Point.new(-0.8810567843300764, 0.4682471721857997, -0.06695915565437902), 0.6645717709362753), (Bool.True, Bool.True, S2Point.new(0.5529833400792779, 0.8330286761030307, -0.01651212841514471), 0.6350618809277098), (Bool.False, Bool.True, S2Point.new(0.2336804926719767, 0.917707301591106, -0.3212580519628317), 0.22650634535738334), (Bool.True, Bool.True, S2Point.new(-0.16030462039488805, 0.9812228053314865, -0.10725779681430388), 0.005873217911573535)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.4402830253793413, -0.14346565101734207, -0.8863230023761003), S2Point.new(0.4449832238457741, 0.04640327530163434, -0.894335880157507), [(Bool.False, Bool.False, S2Point.new(-0.4947913828924547, 0.6061202657219863, -0.6227356669538698), 0.6343284910077162), (Bool.True, Bool.True, S2Point.new(0.23041999703467006, -0.8392206298533774, -0.4925600058825762), 0.9184362265210788), (Bool.False, Bool.True, S2Point.new(0.20329517914570175, -0.07035023123353382, -0.9765868702278899), 0.00346457343059861), (Bool.False, Bool.False, S2Point.new(-0.5203342375561424, 0.6242362621045244, -0.5827361069134462), 0.6879394270786099), (Bool.True, Bool.False, S2Point.new(-0.3026037955552422, 0.5796413843828279, -0.7566021467233093), 0.515392524830654)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.8129399227731445, -0.34748594617513856, -0.46731381230642277), S2Point.new(-0.5912350573406506, -0.7332044474587461, 0.33593503121602597), [(Bool.False, Bool.True, S2Point.new(-0.8543014107012006, -0.3653801130497862, 0.3696842878209246), 0.17765845986914625), (Bool.True, Bool.False, S2Point.new(-0.2062855332394148, -0.7734739262955072, -0.5993199180046853), 0.5557030973257648), (Bool.False, Bool.True, S2Point.new(-0.8150796167248736, 0.16438881987328358, 0.5555371583434381), 0.901717124835257), (Bool.False, Bool.True, S2Point.new(-0.8779633443632251, 0.034891009027541664, 0.47745469255582906), 0.6693125052974046), (Bool.True, Bool.False, S2Point.new(-0.7839666810247347, -0.3932002845332439, -0.48040584851356494), 0.0028507137018933234)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(0.20096430953345096, -0.584180420038404, 0.7863501657261206), S2Point.new(0.5820332562804985, -0.02465914773779021, 0.8127910032821263), [(Bool.True, Bool.False, S2Point.new(0.8687945990285054, -0.4548156076240489, 0.19580272664206128), 0.628482101286841), (Bool.True, Bool.True, S2Point.new(0.38845054010871405, -0.022863826227460735, 0.921185878821147), 0.03883861403425524), (Bool.True, Bool.True, S2Point.new(-0.03581989370437649, -0.11287168142419257, 0.9929637046475983), 0.2626863708146328), (Bool.False, Bool.True, S2Point.new(-0.18776516229032375, 0.3406488048938885, 0.921250582390293), 0.7377950962735548), (Bool.True, Bool.False, S2Point.new(0.7424056757211196, -0.49378289101490896, 0.4527828057667677), 0.29220517984584526)], [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]),
		(S2Point.new(-0.8212145077405435, 0.21878690307331766, 0.5270095097055119), S2Point.new(-0.9452044428271317, 0.19765581209314853, 0.2598475345383317), [(Bool.True, Bool.True, S2Point.new(-0.8847281850430775, 0.034004721274572464, 0.4648652681384368), 0.03302689074068546), (Bool.True, Bool.True, S2Point.new(-0.6922443923223852, -0.5758817550585402, 0.4349228730348717), 0.6544665910184155), (Bool.False, Bool.True, S2Point.new(-0.7604478858937471, 0.005313000183771067, 0.6493772284803172), 0.06423754814371416), (Bool.False, Bool.True, S2Point.new(-0.7664854564839562, -0.4670304047368081, 0.44088847348275567), 0.4744513190711812), (Bool.True, Bool.False, S2Point.new(-0.8392541477600723, 0.4711440432161993, 0.2714328020144336), 0.0811958323965995)], [Bool.True, Bool.True, Bool.True, Bool.False, Bool.False, Bool.False]),
		(S2Point.new(0.553597881613896, -0.8024820420306636, 0.2226026902148834), S2Point.new(0.7226908551368806, -0.6653465034604014, 0.18716826182486893), [(Bool.True, Bool.True, S2Point.new(0.31026362210535574, -0.31118225256830045, 0.8982772904201595), 0.7571232103388827), (Bool.False, Bool.True, S2Point.new(0.47621557692376687, -0.4574192323281683, 0.7509902597181093), 0.40132501279265503), (Bool.True, Bool.False, S2Point.new(0.5090331120982869, -0.8574965493114906, -0.07473258129102228), 0.09342087837482553), (Bool.False, Bool.True, S2Point.new(0.39559559408492057, -0.1969892061702764, 0.8970503768423506), 0.8289437653834484), (Bool.False, Bool.False, S2Point.new(0.30940931001129485, -0.7062649265004465, -0.6367540596444232), 0.8073798153510334)], [Bool.True, Bool.True, Bool.False, Bool.False, Bool.True, Bool.False]),
	]
	cases.all(
		|(src, dst, discs, expected)| {
			(last, results) =
				discs.fold(
					(S2PolylineSimplifier.new(src), []),
					|(s, out), (avoid, left, center, length2)| {
						radius = S1ChordAngle.from_length2(length2)
						(ok, next) = if (avoid) s.avoid_disc(center, radius, left) else s.target_disc(center, radius)
						(next, out.append(ok))
					},
				)
			results.append(last.extend(dst)) == expected
		},
	)
}

import /S2Point
import /S2Predicates

## The edge crossing test shared by `S2Edge.crossing_sign` and
## `S2EdgeCrosser`, so that the two cannot disagree.
##
## Internal to this package.
S2Crossing := [].{

	## The error bound on the tangent test below, `(1.5 + 1 / sqrt(3))`
	## times `F64` machine epsilon.
	tangent_error : F64
	tangent_error = 4.612644198131179e-16

	## The crossing sign of the edges `ab` and `cd`, given the triage results
	## that the caller has already computed: `acb` is the orientation of the
	## triangle `acb` and `bda` that of `bda`, each `0` when triage was not
	## sure.
	##
	## Returns the crossing sign and the orientation of `bda` as this test
	## leaves it, which is exact whenever the test had to compute it. An edge
	## crosser keeps the negation of that orientation as the `acb` of the next
	## edge in its chain.
	crossing_sign : S2Point, S2Point, S2Point, S2Point, I8, I8 -> (I8, I8)
	crossing_sign = |a, b, c, d, acb, bda| {
		# The common case: c and d sit on opposite sides of the great circle
		# through a and b, so no crossing is possible.
		if acb == -bda and bda != 0 {
			return (-1, bda)
		}

		# Test whether cd lies entirely beyond one end of ab, which rules out
		# a crossing far more cheaply than exact arithmetic would.
		norm = a.robust_cross(b)
		a_tangent = a.cross(norm)
		b_tangent = norm.cross(b)
		beyond_a =
			c.dot(a_tangent) > S2Crossing.tangent_error and d.dot(a_tangent) > S2Crossing.tangent_error
		beyond_b =
			c.dot(b_tangent) > S2Crossing.tangent_error and d.dot(b_tangent) > S2Crossing.tangent_error
		if beyond_a or beyond_b {
			return (-1, bda)
		}

		# A shared endpoint is a vertex crossing, not an edge crossing.
		if a == c or a == d or b == c or b == d {
			return (0, bda)
		}
		if a == b or c == d {
			return (-1, bda)
		}

		# The four triangles acb, cbd, bda, dac must agree in orientation.
		exact_acb = if (acb == 0) -S2Predicates.expensive_sign(a, b, c) else acb
		exact_bda = if (bda == 0) S2Predicates.expensive_sign(a, b, d) else bda
		if exact_bda != exact_acb {
			return (-1, exact_bda)
		}
		c_cross_d = c.cross(d)
		if -S2Predicates.sign_with_cross(c, d, b, c_cross_d) != exact_acb {
			return (-1, exact_bda)
		}
		if S2Predicates.sign_with_cross(c, d, a, c_cross_d) != exact_acb {
			return (-1, exact_bda)
		}
		(1, exact_bda)
	}
}

import Internal/S2Crossing
import S2Edge
import S2LatLng
import S2Point
import S2Predicates

## Tests one fixed edge `ab` against a chain of other edges, reusing work
## from one test to the next.
##
## Upstream's `S2EdgeCrosser` is a mutable object. Here it is a value: each
## test returns its answer together with the crosser advanced to the end of
## the edge just tested, so a chain `c0, c1, c2, ...` is walked as
##
## ```
## (first, crosser1) = S2EdgeCrosser.new_with_c(a, b, c0).crossing_sign(c1)
## (second, crosser2) = crosser1.crossing_sign(c2)
## ```
##
## The answers are always those of `S2Edge.crossing_sign`,
## `S2Edge.edge_or_vertex_crossing` and the signed variant, since both use one
## implementation. Walking a chain is faster than calling those functions
## edge by edge, because the orientation of each chain vertex relative to
## `ab` is computed once.
S2EdgeCrosser := { a : S2Point, b : S2Point, a_cross_b : S2Point, c : Try(S2Point, [NoVertex]), acb : I8 }.{

	## A crosser for the fixed edge `ab` with no chain vertex yet.
	##
	## Start a chain with `restart_at`, or use the forms that take both
	## endpoints of the other edge, such as `crossing_sign_edge`.
	new : S2Point, S2Point -> S2EdgeCrosser
	new = |a, b| { a, b, a_cross_b: a.cross(b), c: Err(NoVertex), acb: 0 }

	## A crosser for the fixed edge `ab` whose chain starts at `c`.
	new_with_c : S2Point, S2Point, S2Point -> S2EdgeCrosser
	new_with_c = |a, b, start| S2EdgeCrosser.new(a, b).restart_at(start)

	## The same crosser with its chain restarted at `c`.
	restart_at : S2EdgeCrosser, S2Point -> S2EdgeCrosser
	restart_at = |crosser, start| { ..crosser, c: Ok(start), acb: -S2Predicates.triage_sign(start, crosser.a_cross_b) }

	## The first endpoint of the fixed edge.
	a : S2EdgeCrosser -> S2Point
	a = |crosser| crosser.a

	## The second endpoint of the fixed edge.
	b : S2EdgeCrosser -> S2Point
	b = |crosser| crosser.b

	## The last vertex of the chain, or `Err(NoVertex)` before the chain has
	## started.
	c : S2EdgeCrosser -> Try(S2Point, [NoVertex])
	c = |crosser| crosser.c

	## `S2Edge.crossing_sign(a, b, c, d)` for the previous chain vertex `c`,
	## and the crosser advanced to `d`.
	##
	## Before the chain has started, the call starts it at `d` and answers
	## `-1`, as there is no edge to test yet.
	crossing_sign : S2EdgeCrosser, S2Point -> (I8, S2EdgeCrosser)
	crossing_sign = |crosser, d|
		match crosser.c {
			Err(NoVertex) => (-1, crosser.restart_at(d))
			Ok(prev) => {
				bda = S2Predicates.triage_sign(d, crosser.a_cross_b)
				(result, final_bda) = S2Crossing.crossing_sign(crosser.a, crosser.b, prev, d, crosser.acb, bda)
				(result, { ..crosser, c: Ok(d), acb: -final_bda })
			}
		}

	## `S2Edge.edge_or_vertex_crossing(a, b, c, d)` for the previous chain
	## vertex `c`, and the crosser advanced to `d`.
	edge_or_vertex_crossing : S2EdgeCrosser, S2Point -> (Bool, S2EdgeCrosser)
	edge_or_vertex_crossing = |crosser, d| {
		(crossing, next) = crosser.crossing_sign(d)
		answer =
			if crossing < 0 {
				Bool.False
			} else if crossing > 0 {
				Bool.True
			} else {
				match crosser.c {
					Ok(prev) => S2Edge.vertex_crossing(crosser.a, crosser.b, prev, d)
					Err(NoVertex) => Bool.False
				}
			}
		(answer, next)
	}

	## Like `edge_or_vertex_crossing`, but with a sign: `1` when the edge
	## `cd` crosses `ab` from left to right, `-1` when it crosses from right
	## to left, and `0` when it does not cross. Shared vertices follow
	## `S2Edge.signed_vertex_crossing`.
	##
	## Summing the signs along a closed chain gives its winding number around
	## the point where `ab` crosses it.
	signed_edge_or_vertex_crossing : S2EdgeCrosser, S2Point -> (I8, S2EdgeCrosser)
	signed_edge_or_vertex_crossing = |crosser, d| {
		(crossing, next) = crosser.crossing_sign(d)
		answer =
			if crossing < 0 {
				0
			} else if crossing > 0 {
				next.last_interior_crossing_sign()
			} else {
				match crosser.c {
					Ok(prev) => S2Edge.signed_vertex_crossing(crosser.a, crosser.b, prev, d)
					Err(NoVertex) => 0
				}
			}
		(answer, next)
	}

	## After a `crossing_sign` that answered `1`, the direction of that
	## crossing: `1` when the edge crossed `ab` from left to right, and `-1`
	## when it crossed from right to left.
	##
	## Meaningless after any other answer.
	last_interior_crossing_sign : S2EdgeCrosser -> I8
	last_interior_crossing_sign = |crosser| crosser.acb

	## `crossing_sign` for the edge `cd`, restarting the chain at `c` unless
	## it already ends there.
	crossing_sign_edge : S2EdgeCrosser, S2Point, S2Point -> (I8, S2EdgeCrosser)
	crossing_sign_edge = |crosser, start, d| at(crosser, start).crossing_sign(d)

	## `edge_or_vertex_crossing` for the edge `cd`, restarting the chain at
	## `c` unless it already ends there.
	edge_or_vertex_crossing_edge : S2EdgeCrosser, S2Point, S2Point -> (Bool, S2EdgeCrosser)
	edge_or_vertex_crossing_edge = |crosser, start, d| at(crosser, start).edge_or_vertex_crossing(d)

	## `signed_edge_or_vertex_crossing` for the edge `cd`, restarting the
	## chain at `c` unless it already ends there.
	signed_edge_or_vertex_crossing_edge : S2EdgeCrosser, S2Point, S2Point -> (I8, S2EdgeCrosser)
	signed_edge_or_vertex_crossing_edge = |crosser, start, d| at(crosser, start).signed_edge_or_vertex_crossing(d)
}

## The crosser with its chain at `c`, restarted only when it is elsewhere.
at : S2EdgeCrosser, S2Point -> S2EdgeCrosser
at = |crosser, start|
	match crosser.c {
		Ok(previous) if previous == start => crosser
		_ => crosser.restart_at(start)
	}

# Two chains walked by upstream's S2EdgeCrosser at v0.14.0, through
# tools/s2_oracle.cc: one crossing back and forth through the edge and its
# endpoints, and one that shares vertices with it.
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	c = S2LatLng.from_degrees(5.0, -5.0).to_point()
	chain = [
		S2LatLng.from_degrees(-5.0, 2.0).to_point(),
		S2LatLng.from_degrees(5.0, 4.0).to_point(),
		S2LatLng.from_degrees(-5.0, 6.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(5.0, 12.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S2LatLng.from_degrees(-5.0, 20.0).to_point(),
	]
	(signs, lasts, _) = chain.fold(
		([], [], S2EdgeCrosser.new_with_c(a, b, c)),
		|(acc, acc_last, crosser), d| {
			(sign, next) = crosser.crossing_sign(d)
			(acc.append(sign), acc_last.append(next.last_interior_crossing_sign()), next)
		},
	)
	signs == [-1, 1, 1, 0, 0, 0, 0, 0] and lasts == [1, -1, 1, 0, -1, 0, 0, 1]
}
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	c = S2LatLng.from_degrees(5.0, -5.0).to_point()
	chain = [
		S2LatLng.from_degrees(-5.0, 2.0).to_point(),
		S2LatLng.from_degrees(5.0, 4.0).to_point(),
		S2LatLng.from_degrees(-5.0, 6.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(5.0, 12.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S2LatLng.from_degrees(-5.0, 20.0).to_point(),
	]
	(crossings, _) = chain.fold(
		([], S2EdgeCrosser.new_with_c(a, b, c)),
		|(acc, crosser), d| {
			(crossing, next) = crosser.edge_or_vertex_crossing(d)
			(acc.append(crossing), next)
		},
	)
	crossings == [Bool.False, Bool.True, Bool.True, Bool.False, Bool.False, Bool.False, Bool.True, Bool.True]
}
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	c = S2LatLng.from_degrees(5.0, -5.0).to_point()
	chain = [
		S2LatLng.from_degrees(-5.0, 2.0).to_point(),
		S2LatLng.from_degrees(5.0, 4.0).to_point(),
		S2LatLng.from_degrees(-5.0, 6.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(5.0, 12.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S2LatLng.from_degrees(-5.0, 20.0).to_point(),
	]
	(crossings, _) = chain.fold(
		([], S2EdgeCrosser.new_with_c(a, b, c)),
		|(acc, crosser), d| {
			(crossing, next) = crosser.signed_edge_or_vertex_crossing(d)
			(acc.append(crossing), next)
		},
	)
	crossings == [0, -1, 1, 0, 0, 0, -1, 1]
}
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	c = S2LatLng.from_degrees(5.0, -5.0).to_point()
	chain = [
		S2LatLng.from_degrees(-5.0, 2.0).to_point(),
		S2LatLng.from_degrees(5.0, 4.0).to_point(),
		S2LatLng.from_degrees(-5.0, 6.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(5.0, 12.0).to_point(),
		S2LatLng.from_degrees(0.0, 10.0).to_point(),
		S2LatLng.from_degrees(0.0, 0.0).to_point(),
		S2LatLng.from_degrees(-5.0, 20.0).to_point(),
	]
	# The two-edge forms, from a crosser with no chain, agree with S2Edge.
	crosser = S2EdgeCrosser.new(a, b)
	(_, failures) = chain.fold(
		(c, 0),
		|(prev, bad), d| {
			(sign, _) = crosser.crossing_sign_edge(prev, d)
			(any, _) = crosser.edge_or_vertex_crossing_edge(prev, d)
			(signed, _) = crosser.signed_edge_or_vertex_crossing_edge(prev, d)
			ok = sign == S2Edge.crossing_sign(a, b, prev, d) and any == S2Edge.edge_or_vertex_crossing(a, b, prev, d)
			(d, if (ok and (signed != 0) == any) bad else bad + 1)
		},
	)
	failures == 0
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	chain = [
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
		S2Point.new(0.0, 1.0, 0.0),
		S2Point.new(1.0, 1.0, 1.0).normalize(),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
	]
	(signs, lasts, _) = chain.fold(
		([], [], S2EdgeCrosser.new_with_c(a, b, c)),
		|(acc, acc_last, crosser), d| {
			(sign, next) = crosser.crossing_sign(d)
			(acc.append(sign), acc_last.append(next.last_interior_crossing_sign()), next)
		},
	)
	signs == [0, 0, 0, 0, 1] and lasts == [0, 1, 0, -1, 1]
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	chain = [
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
		S2Point.new(0.0, 1.0, 0.0),
		S2Point.new(1.0, 1.0, 1.0).normalize(),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
	]
	(crossings, _) = chain.fold(
		([], S2EdgeCrosser.new_with_c(a, b, c)),
		|(acc, crosser), d| {
			(crossing, next) = crosser.edge_or_vertex_crossing(d)
			(acc.append(crossing), next)
		},
	)
	crossings == [Bool.False, Bool.True, Bool.False, Bool.True, Bool.True]
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	chain = [
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
		S2Point.new(0.0, 1.0, 0.0),
		S2Point.new(1.0, 1.0, 1.0).normalize(),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
	]
	(crossings, _) = chain.fold(
		([], S2EdgeCrosser.new_with_c(a, b, c)),
		|(acc, crosser), d| {
			(crossing, next) = crosser.signed_edge_or_vertex_crossing(d)
			(acc.append(crossing), next)
		},
	)
	crossings == [0, 1, 0, -1, 1]
}
expect {
	a = S2Point.new(1.0, 0.0, 0.0)
	b = S2Point.new(0.0, 1.0, 0.0)
	c = S2Point.new(0.0, 0.0, 1.0)
	chain = [
		S2Point.new(1.0, 0.0, 0.0),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
		S2Point.new(0.0, 1.0, 0.0),
		S2Point.new(1.0, 1.0, 1.0).normalize(),
		S2Point.new(1.0, 1.0, -1.0).normalize(),
	]
	# The two-edge forms, from a crosser with no chain, agree with S2Edge.
	crosser = S2EdgeCrosser.new(a, b)
	(_, failures) = chain.fold(
		(c, 0),
		|(prev, bad), d| {
			(sign, _) = crosser.crossing_sign_edge(prev, d)
			(any, _) = crosser.edge_or_vertex_crossing_edge(prev, d)
			(signed, _) = crosser.signed_edge_or_vertex_crossing_edge(prev, d)
			ok = sign == S2Edge.crossing_sign(a, b, prev, d) and any == S2Edge.edge_or_vertex_crossing(a, b, prev, d)
			(d, if (ok and (signed != 0) == any) bad else bad + 1)
		},
	)
	failures == 0
}

expect {
	# Before the chain has started, the first vertex only starts it.
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	d = S2LatLng.from_degrees(-5.0, 2.0).to_point()
	(sign, next) = S2EdgeCrosser.new(a, b).crossing_sign(d)
	sign == -1 and next.c() == Ok(d) and S2EdgeCrosser.new(a, b).c() == Err(NoVertex)
}
expect {
	a = S2LatLng.from_degrees(0.0, 0.0).to_point()
	b = S2LatLng.from_degrees(0.0, 10.0).to_point()
	crosser = S2EdgeCrosser.new(a, b)
	crosser.a() == a and crosser.b() == b
}

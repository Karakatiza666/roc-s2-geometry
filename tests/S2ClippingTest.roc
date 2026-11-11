import s2.R1Interval
import s2.R2Point
import s2.R2Rect
import s2.S2EdgeClipping
import s2.S2Point
import ClippingCorpus

## Checks `S2EdgeClipping` against the answers of upstream's
## `s2edge_clipping.h` in `ClippingCorpus`, double for double.
S2ClippingTest := [].{

	point : (F64, F64, F64) -> S2Point
	point = |(x, y, z)| S2Point.new(x, y, z)

	uv : (F64, F64) -> R2Point
	uv = |(x, y)| R2Point.new(x, y)

	rect : (F64, F64, F64, F64) -> R2Rect
	rect = |(x0, x1, y0, y1)| R2Rect.new(R1Interval.new(x0, x1), R1Interval.new(y0, y1))

	## The number of cases for which the check fails.
	failures : List(a), (a -> Bool) -> U64
	failures = |cases, check| cases.fold(0, |acc, case| if (check(case)) acc else acc + 1)

	## The rectangle as `(x_lo, x_hi, y_lo, y_hi)`.
	bounds : R2Rect -> (F64, F64, F64, F64)
	bounds = |r| (r.x().lo(), r.x().hi(), r.y().lo(), r.y().hi())

	## The two ends as `(ax, ay, bx, by)`, or zeros for `Err`.
	ends : Try((R2Point, R2Point), _) -> (F64, F64, F64, F64)
	ends = |result| match result {
		Ok((a, b)) => (a.x(), a.y(), b.x(), b.y())
		Err(_) => (0.0, 0.0, 0.0, 0.0)
	}

	segments_match : { a : (F64, F64, F64), b : (F64, F64, F64), segments : List({ face : U64, a : (F64, F64), b : (F64, F64) }), clips : List(_) } -> Bool
	segments_match = |case| {
		got = S2EdgeClipping.get_face_segments(S2ClippingTest.point(case.a), S2ClippingTest.point(case.b))
		expected = case.segments.map(|s| { face: s.face, a: S2ClippingTest.uv(s.a), b: S2ClippingTest.uv(s.b) })
		got == expected
	}

	clips_match : { a : (F64, F64, F64), b : (F64, F64, F64), segments : List(_), clips : List({ face : U64, padding : F64, hit : Bool, uv : (F64, F64, F64, F64) }) } -> Bool
	clips_match = |case| {
		a = S2ClippingTest.point(case.a)
		b = S2ClippingTest.point(case.b)
		case.clips.all(
			|c| {
				result = S2EdgeClipping.clip_to_padded_face(a, b, c.face, c.padding)
				result.is_ok() == c.hit and S2ClippingTest.ends(result) == c.uv
			},
		)
	}
}

expect S2ClippingTest.failures(ClippingCorpus.faces, S2ClippingTest.segments_match) == 0
expect S2ClippingTest.failures(ClippingCorpus.faces, S2ClippingTest.clips_match) == 0

# clip_to_face is clip_to_padded_face with no padding.
expect S2ClippingTest.failures(
	ClippingCorpus.faces,
	|case| {
		a = S2ClippingTest.point(case.a)
		b = S2ClippingTest.point(case.b)
		[0, 1, 2, 3, 4, 5].all(|face| S2EdgeClipping.clip_to_face(a, b, face) == S2EdgeClipping.clip_to_padded_face(a, b, face, 0.0))
	},
)
	== 0

expect S2ClippingTest.failures(
	ClippingCorpus.edges,
	|case| S2EdgeClipping.intersects_rect(S2ClippingTest.uv(case.a), S2ClippingTest.uv(case.b), S2ClippingTest.rect(case.clip)) == case.hits,
)
	== 0
expect S2ClippingTest.failures(
	ClippingCorpus.edges,
	|case| {
		result = S2EdgeClipping.clip_edge(S2ClippingTest.uv(case.a), S2ClippingTest.uv(case.b), S2ClippingTest.rect(case.clip))
		result.is_ok() == case.clipped and S2ClippingTest.ends(result) == case.ends
	},
)
	== 0
expect S2ClippingTest.failures(
	ClippingCorpus.edges,
	|case| {
		bound = S2EdgeClipping.get_clipped_edge_bound(S2ClippingTest.uv(case.a), S2ClippingTest.uv(case.b), S2ClippingTest.rect(case.clip))
		S2ClippingTest.bounds(bound) == case.bound
	},
)
	== 0
expect S2ClippingTest.failures(
	ClippingCorpus.chained,
	|case| {
		result = S2EdgeClipping.clip_edge_bound(S2ClippingTest.uv(case.a), S2ClippingTest.uv(case.b), S2ClippingTest.rect(case.clip), S2ClippingTest.rect(case.bound))
		match result {
			Ok(bound) => case.ok and S2ClippingTest.bounds(bound) == case.result
			Err(NoIntersection) => !case.ok
		}
	},
)
	== 0

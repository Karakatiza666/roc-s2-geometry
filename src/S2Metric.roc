import S2CellId
import Internal/S2Math

## A quantity that scales with cell size, such as an edge length or an area.
##
## Every such quantity halves (for a length) or quarters (for an area) with
## each level, so one derivative plus the dimension describes it at every
## level: `value(level) = deriv * 2^(-dim * level)`.
##
## The named metrics below are for the quadratic projection S2 actually uses.
## Use them to pick a level from a target size, which is what a region coverer
## does:
##
##     S2Metric.min_width.max_level_for(0.001)
S2Metric := { deriv : F64, dim : U8 }.{

	## A one-dimensional metric, such as a length or an angle.
	length : F64 -> S2Metric
	length = |deriv| { deriv: deriv, dim: 1 }

	## A two-dimensional metric, such as an area.
	area : F64 -> S2Metric
	area = |deriv| { deriv: deriv, dim: 2 }

	deriv : S2Metric -> F64
	deriv = |m| m.deriv

	dim : S2Metric -> U8
	dim = |m| m.dim

	## The metric's value at the given level, in radians or steradians.
	value_at : S2Metric, U64 -> F64
	value_at = |m, level| S2Math.ldexp(m.deriv, -(m.dim.to_i32() * level.to_i32_wrap()))

	## The finest level at which the metric is still at most `value`, or level
	## 30 when no level is coarse enough.
	##
	## `max_diag.min_level_for(0.1)` is the coarsest cells whose diagonals are
	## all 0.1 or shorter.
	min_level_for : S2Metric, F64 -> U64
	min_level_for = |m, value| {
		if value <= 0.0 {
			return S2CellId.max_level
		}
		exponent = S2Math.frexp_exponent(value / m.deriv)
		shift = (m.dim - 1).to_u8_wrap()
		level = -((exponent - 1).shr_wrap(shift))
		S2Math.clamp_i64(level.to_i64(), 0, S2CellId.max_level.to_i64_wrap()).to_u64_wrap()
	}

	## The coarsest level at which the metric is still at least `value`, or
	## level 0 when no level is fine enough.
	max_level_for : S2Metric, F64 -> U64
	max_level_for = |m, value| {
		if value <= 0.0 {
			return S2CellId.max_level
		}
		exponent = S2Math.frexp_exponent(m.deriv / value)
		shift = (m.dim - 1).to_u8_wrap()
		level = (exponent - 1).shr_wrap(shift)
		S2Math.clamp_i64(level.to_i64(), 0, S2CellId.max_level.to_i64_wrap()).to_u64_wrap()
	}

	## The level at which the metric is closest to `value`.
	closest_level_for : S2Metric, F64 -> U64
	closest_level_for = |m, value| {
		two : F64
		two = 2.0
		factor = if m.dim == 1 {
			two.sqrt()
		} else {
			two
		}
		m.min_level_for(factor * value)
	}

	## The angle a cell edge spans as seen from the sphere's centre, at its
	## widest.
	max_angle_span : S2Metric
	max_angle_span = { deriv: 1.704897179199218452, dim: 1 }

	min_angle_span : S2Metric
	min_angle_span = { deriv: 1.3333333333333333, dim: 1 }

	## True for every projection, not just the quadratic one.
	avg_angle_span : S2Metric
	avg_angle_span = { deriv: 1.5707963267948966, dim: 1 }

	## The length of a cell edge, at its longest.
	max_edge : S2Metric
	max_edge = { deriv: 1.704897179199218452, dim: 1 }

	min_edge : S2Metric
	min_edge = { deriv: 0.9428090415820634, dim: 1 }

	avg_edge : S2Metric
	avg_edge = { deriv: 1.459213746386106062, dim: 1 }

	## The length of a cell diagonal, at its longest.
	max_diag : S2Metric
	max_diag = { deriv: 2.438654594434021032, dim: 1 }

	min_diag : S2Metric
	min_diag = { deriv: 1.2570787221094177, dim: 1 }

	avg_diag : S2Metric
	avg_diag = { deriv: 2.060422738998471683, dim: 1 }

	## The distance between opposite edges of a cell, at its widest.
	max_width : S2Metric
	max_width = { deriv: 1.704897179199218452, dim: 1 }

	## The narrowest a cell gets, which is what bounds how far a covering can
	## be off.
	min_width : S2Metric
	min_width = { deriv: 0.9428090415820634, dim: 1 }

	avg_width : S2Metric
	avg_width = { deriv: 1.434523672886099389, dim: 1 }

	max_area : S2Metric
	max_area = { deriv: 2.635799256963161491, dim: 2 }

	min_area : S2Metric
	min_area = { deriv: 1.2570787221094177, dim: 2 }

	## True for every projection: the sphere's area divided by six faces.
	avg_area : S2Metric
	avg_area = { deriv: 2.0943951023931953, dim: 2 }

	is_eq : S2Metric, S2Metric -> Bool
	is_eq = |a, b| a.deriv == b.deriv and a.dim == b.dim

	to_inspect : S2Metric -> Str
	to_inspect = |m| "S2Metric(deriv ${m.deriv.to_str()}, dim ${m.dim.to_str()})"
}

expect S2Metric.avg_area.value_at(0) == 2.0943951023931953
expect S2Metric.avg_area.value_at(1) == 2.0943951023931953 / 4.0
expect S2Metric.max_edge.value_at(2) == 1.704897179199218452 / 4.0
expect S2Metric.min_width.min_level_for(0.0) == 30
expect S2Metric.min_width.max_level_for(0.0) == 30
expect S2Metric.avg_area.min_level_for(100.0) == 0
expect S2Metric.avg_area.max_level_for(1e-30) == 30
expect {
	# min_level_for finds the first level at or below the target.
	failures : U64
	failures = (0.U64).until(30).fold(
		0,
		|acc, level| {
			value = S2Metric.max_diag.value_at(level)
			found = S2Metric.max_diag.min_level_for(value)
			if (found == level) acc else acc + 1
		},
	)
	failures == 0
}
expect {
	# max_level_for is the mirror image of min_level_for.
	failures : U64
	failures = (0.U64).until(30).fold(
		0,
		|acc, level| {
			value = S2Metric.min_width.value_at(level)
			found = S2Metric.min_width.max_level_for(value)
			if (found == level) acc else acc + 1
		},
	)
	failures == 0
}
expect {
	# The value at the level min_level_for picks never exceeds the target.
	target = 0.017453292519943295
	level = S2Metric.max_diag.min_level_for(target)
	S2Metric.max_diag.value_at(level) <= target
		and (level == 0 or S2Metric.max_diag.value_at(level - 1) > target)
}
expect S2Metric.avg_edge.closest_level_for(S2Metric.avg_edge.value_at(12)) == 12

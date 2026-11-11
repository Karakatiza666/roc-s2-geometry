import R2Point
import S2Point

## The cube-face coordinate system every S2 cell is defined in.
##
## A point on the sphere is projected onto one of six faces of a circumscribed
## cube, giving face coordinates `(u, v)` in `[-1, 1]`. Those are reparametrized
## as `(s, t)` in `[0, 1]`, which is what the discrete `(i, j)` cell indices
## divide up.
##
## The `s`-to-`u` step is the *quadratic* projection: it costs one extra
## multiply over the linear one but makes the largest cell only about 2.1 times
## the area of the smallest, instead of 5.2.
##
##     xyz  --face--> uv  --quadratic--> st  --scale--> ij
S2Coords := [].{

	## The number of cube faces.
	num_faces : U64
	num_faces = 6

	## The finest subdivision level, at which cells are about 1 cm across.
	max_level : U64
	max_level = 30

	## The number of leaf cells along one edge of a face.
	max_size : U64
	max_size = 1073741824

	## The bits a cell id spends on the position along the Hilbert curve.
	pos_bits : U8
	pos_bits = 61

	## The `(u, v)` coordinate for an `(s, t)` coordinate.
	st_to_uv : F64 -> F64
	st_to_uv = |s|
		if s >= 0.5 {
			(1.0 / 3.0) * (4.0 * s * s - 1.0)
		} else {
			(1.0 / 3.0) * (1.0 - 4.0 * (1.0 - s) * (1.0 - s))
		}

	## The `(s, t)` coordinate for a `(u, v)` coordinate.
	uv_to_st : F64 -> F64
	uv_to_st = |u|
		if u >= 0.0 {
			0.5 * (1.0 + 3.0 * u).sqrt()
		} else {
			1.0 - 0.5 * (1.0 - 3.0 * u).sqrt()
		}

	## The leaf-cell index containing the given `s` coordinate, clamped to
	## `[0, max_size - 1]`.
	st_to_ij : F64 -> U64
	st_to_ij = |s| {
		scaled = (S2Coords.max_size.to_f64() * s).to_i64_wrap()
		floored = if (scaled.to_f64() > S2Coords.max_size.to_f64() * s) scaled - 1 else scaled
		floored.max(0).min((S2Coords.max_size - 1).to_i64_wrap()).to_u64_wrap()
	}

	## The `s` coordinate of the centre of leaf cell `i`.
	ij_to_st_center : U64 -> F64
	ij_to_st_center = |i| (i.to_f64() + 0.5) / S2Coords.max_size.to_f64()

	## The `s` coordinate for a level-30 half-integer index `si`, which counts
	## in units of half a leaf cell so that cell centres land on integers.
	si_ti_to_st : U64 -> F64
	si_ti_to_st = |si| si.to_f64() / (2.0 * S2Coords.max_size.to_f64())

	## The half-integer index nearest the given `s` coordinate.
	st_to_si_ti : F64 -> U64
	st_to_si_ti = |s| {
		scaled = s * 2.0 * S2Coords.max_size.to_f64()
		rounded = if scaled < 0.0 {
			-(-scaled + 0.5)
		} else {
			scaled + 0.5
		}
		rounded.to_i64_wrap().max(0).to_u64_wrap()
	}

	## The point on the cube face for a `(u, v)` coordinate. The result is not
	## unit length.
	face_uv_to_xyz : U64, F64, F64 -> S2Point
	face_uv_to_xyz = |face, u, v|
		if face == 0 {
			S2Point.new(1.0, u, v)
		} else if face == 1 {
			S2Point.new(-u, 1.0, v)
		} else if face == 2 {
			S2Point.new(-u, -v, 1.0)
		} else if face == 3 {
			S2Point.new(-1.0, -v, -u)
		} else if face == 4 {
			S2Point.new(v, -1.0, -u)
		} else {
			S2Point.new(v, u, -1.0)
		}

	## The `(u, v)` coordinate of a point already known to lie on `face`.
	valid_face_xyz_to_uv : U64, S2Point -> R2Point
	valid_face_xyz_to_uv = |face, p|
		if face == 0 {
			R2Point.new(p.y() / p.x(), p.z() / p.x())
		} else if face == 1 {
			R2Point.new(-p.x() / p.y(), p.z() / p.y())
		} else if face == 2 {
			R2Point.new(-p.x() / p.z(), -p.y() / p.z())
		} else if face == 3 {
			R2Point.new(p.z() / p.x(), p.y() / p.x())
		} else if face == 4 {
			R2Point.new(p.z() / p.y(), -p.x() / p.y())
		} else {
			R2Point.new(-p.y() / p.z(), -p.x() / p.z())
		}

	## The face a point projects onto: the axis of its largest component,
	## offset by 3 when that component is negative.
	face_of : S2Point -> U64
	face_of = |p| {
		face = p.largest_abs_component()
		if p.coord(face) < 0.0 {
			face + 3
		} else {
			face
		}
	}

	## The face and `(u, v)` coordinate a point projects onto.
	xyz_to_face_uv : S2Point -> (U64, R2Point)
	xyz_to_face_uv = |p| {
		face = S2Coords.face_of(p)
		(face, S2Coords.valid_face_xyz_to_uv(face, p))
	}

	## The `(u, v)` coordinate of a point on a specific face, or `Err(NotOnFace)`
	## when the point is on the far side of the cube from it.
	face_xyz_to_uv : U64, S2Point -> Try(R2Point, [NotOnFace])
	face_xyz_to_uv = |face, p| {
		on_face =
			if face < 3 {
				p.coord(face) > 0.0
			} else {
				p.coord(face - 3) < 0.0
			}
		if on_face {
			Ok(S2Coords.valid_face_xyz_to_uv(face, p))
		} else {
			Err(NotOnFace)
		}
	}

	## The unit vector normal to the given face, which is the face centre.
	norm : U64 -> S2Point
	norm = |face| S2Coords.face_uv_to_xyz(face, 0.0, 0.0)

	## The right-handed normal of the great circle through the origin and the
	## edge at the given `u` running along the positive `v` axis.
	u_norm : U64, F64 -> S2Point
	u_norm = |face, u|
		if face == 0 {
			S2Point.new(u, -1.0, 0.0)
		} else if face == 1 {
			S2Point.new(1.0, u, 0.0)
		} else if face == 2 {
			S2Point.new(1.0, 0.0, u)
		} else if face == 3 {
			S2Point.new(-u, 0.0, 1.0)
		} else if face == 4 {
			S2Point.new(0.0, -u, 1.0)
		} else {
			S2Point.new(0.0, -1.0, -u)
		}

	## The right-handed normal of the great circle through the origin and the
	## edge at the given `v` running along the positive `u` axis.
	v_norm : U64, F64 -> S2Point
	v_norm = |face, v|
		if face == 0 {
			S2Point.new(-v, 0.0, 1.0)
		} else if face == 1 {
			S2Point.new(0.0, -v, 1.0)
		} else if face == 2 {
			S2Point.new(0.0, -1.0, -v)
		} else if face == 3 {
			S2Point.new(v, -1.0, 0.0)
		} else if face == 4 {
			S2Point.new(1.0, v, 0.0)
		} else {
			S2Point.new(1.0, 0.0, v)
		}

	## The direction of increasing `u` on the given face.
	u_axis : U64 -> S2Point
	u_axis = |face|
		if face == 0 {
			S2Point.new(0.0, 1.0, 0.0)
		} else if face == 1 {
			S2Point.new(-1.0, 0.0, 0.0)
		} else if face == 2 {
			S2Point.new(-1.0, 0.0, 0.0)
		} else if face == 3 {
			S2Point.new(0.0, 0.0, -1.0)
		} else if face == 4 {
			S2Point.new(0.0, 0.0, -1.0)
		} else {
			S2Point.new(0.0, 1.0, 0.0)
		}

	## The direction of increasing `v` on the given face.
	v_axis : U64 -> S2Point
	v_axis = |face|
		if face == 0 {
			S2Point.new(0.0, 0.0, 1.0)
		} else if face == 1 {
			S2Point.new(0.0, 0.0, 1.0)
		} else if face == 2 {
			S2Point.new(0.0, -1.0, 0.0)
		} else if face == 3 {
			S2Point.new(0.0, -1.0, 0.0)
		} else if face == 4 {
			S2Point.new(1.0, 0.0, 0.0)
		} else {
			S2Point.new(1.0, 0.0, 0.0)
		}
}

expect S2Coords.st_to_uv(0.5) == 0.0
expect S2Coords.st_to_uv(1.0) == 1.0
expect S2Coords.st_to_uv(0.0) == -1.0
expect (S2Coords.uv_to_st(S2Coords.st_to_uv(0.3)) - 0.3).abs() < 1e-15
expect (S2Coords.uv_to_st(S2Coords.st_to_uv(0.8)) - 0.8).abs() < 1e-15
expect S2Coords.st_to_ij(0.0) == 0
expect S2Coords.st_to_ij(1.0) == S2Coords.max_size - 1
expect S2Coords.st_to_ij(0.5) == S2Coords.max_size / 2
expect S2Coords.st_to_ij(-1.0) == 0
expect S2Coords.si_ti_to_st(2 * S2Coords.max_size) == 1.0
expect S2Coords.st_to_si_ti(1.0) == 2 * S2Coords.max_size
expect S2Coords.face_of(S2Point.new(1.0, 0.0, 0.0)) == 0
expect S2Coords.face_of(S2Point.new(0.0, 1.0, 0.0)) == 1
expect S2Coords.face_of(S2Point.new(0.0, 0.0, 1.0)) == 2
expect S2Coords.face_of(S2Point.new(-1.0, 0.0, 0.0)) == 3
expect S2Coords.face_of(S2Point.new(0.0, -1.0, 0.0)) == 4
expect S2Coords.face_of(S2Point.new(0.0, 0.0, -1.0)) == 5
expect S2Coords.norm(0) == S2Point.new(1.0, 0.0, 0.0)
expect S2Coords.norm(5) == S2Point.new(0.0, 0.0, -1.0)
expect S2Coords.face_uv_to_xyz(0, 0.0, 0.0) == S2Point.new(1.0, 0.0, 0.0)
expect {
	# Every face's uv round-trip must return the point it started from.
	failures : U64
	failures = (0.U64).until(6).fold(
		0,
		|acc, face| {
			p = S2Coords.face_uv_to_xyz(face, 0.3, -0.7).normalize()
			(got_face, uv) = S2Coords.xyz_to_face_uv(p)
			ok = got_face == face and (uv.x() - 0.3).abs() < 1e-15 and (uv.y() + 0.7).abs() < 1e-15
			if (ok) acc else acc + 1
		},
	)
	failures == 0
}
expect S2Coords.face_xyz_to_uv(0, S2Point.new(-1.0, 0.0, 0.0)) == Err(NotOnFace)
expect S2Coords.face_xyz_to_uv(0, S2Point.new(1.0, 0.5, 0.25)) == Ok(R2Point.new(0.5, 0.25))
expect {
	# The u and v axes are orthogonal to each other and to the face normal.
	failures : U64
	failures = (0.U64).until(6).fold(
		0,
		|acc, face| {
			n = S2Coords.norm(face)
			u = S2Coords.u_axis(face)
			v = S2Coords.v_axis(face)
			ok = u.dot(v) == 0.0 and u.dot(n) == 0.0 and v.dot(n) == 0.0 and u.cross(v) == n
			if (ok) acc else acc + 1
		},
	)
	failures == 0
}
expect {
	# The u-norm at u is perpendicular to both endpoints of that face edge.
	n = S2Coords.u_norm(2, 0.4)
	a = S2Coords.face_uv_to_xyz(2, 0.4, -1.0)
	b = S2Coords.face_uv_to_xyz(2, 0.4, 1.0)
	n.dot(a).abs() < 1e-15 and n.dot(b).abs() < 1e-15
}
expect {
	n = S2Coords.v_norm(3, -0.6)
	a = S2Coords.face_uv_to_xyz(3, -1.0, -0.6)
	b = S2Coords.face_uv_to_xyz(3, 1.0, -0.6)
	n.dot(a).abs() < 1e-15 and n.dot(b).abs() < 1e-15
}

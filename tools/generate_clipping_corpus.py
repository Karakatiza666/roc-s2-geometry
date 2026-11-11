#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Heorhii Bulakh
# SPDX-License-Identifier: UPL-1.0
"""Generate tests/ClippingCorpus.roc: upstream's edge clipping answers.

The cases follow upstream's s2edge_clipping_test.cc. Its FaceClipping test
starts with five simple edges and then clips edges that nearly follow one of
the twelve cube edges, with endpoints near cube corners, face midpoints and
edge midpoints. Its EdgeClipping test clips edges in the plane against random
rectangles and against one-dimensional, singleton and empty ones. Upstream
draws its random cases from a seeded generator and checks properties of the
answers. This script draws its own cases from a fixed seed and records
upstream's answers through the oracle (tools/s2_oracle.cc), so that the port
must give the same doubles.

Usage:

    python3 tools/generate_clipping_corpus.py .tmp/oracle14/build/s2_oracle > tests/ClippingCorpus.roc
    roc fmt tests
"""

import random
import subprocess
import sys

ORACLE = sys.argv[1]
EPS = 2.220446049250313e-16
rng = random.Random(20261111)


def ask(lines):
    out = subprocess.run(
        [ORACLE], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True
    ).stdout.splitlines()
    assert len(out) == len(lines), (len(out), len(lines))
    return out


def f(x):
    s = "%.17g" % x
    if "e" in s:
        m, e = s.split("e")
        if "." not in m:
            m += ".0"
        return f"{m}e{int(e)}"
    return s if "." in s else s + ".0"


def tup(vs):
    return "(" + ", ".join(f(v) for v in vs) + ")"


def q(vs):
    return " ".join(repr(float(v)) for v in vs)


def normalized(points):
    """The points as upstream's Normalize() leaves them."""
    out = ask([f"point2 mul N {q(p)} 1 1 1" for p in points])
    return [tuple(map(float, line.split())) for line in out]


# Face clipping ----------------------------------------------------------

FACE_UV = {
    0: lambda u, v: (1.0, u, v),
    1: lambda u, v: (-u, 1.0, v),
    2: lambda u, v: (-u, -v, 1.0),
    3: lambda u, v: (-1.0, -v, -u),
    4: lambda u, v: (v, -1.0, -u),
    5: lambda u, v: (v, u, -1.0),
}
BIUNIT = [(-1.0, -1.0), (1.0, -1.0), (1.0, 1.0), (-1.0, 1.0)]


def random_point():
    # A point uniform on the sphere, as s2random::Point draws it.
    while True:
        p = tuple(rng.uniform(-1.0, 1.0) for _ in range(3))
        n2 = sum(c * c for c in p)
        if 0 < n2 <= 1:
            n = n2 ** 0.5
            return tuple(c / n for c in p)


def perturbed_corner_or_midpoint(p, q_):
    """Upstream's PerturbedCornerOrMidpoint."""
    while True:
        i = rng.randrange(3) - 1
        j = rng.randrange(3) - 1
        a = tuple(i * pc + j * qc for pc, qc in zip(p, q_))
        r = rng.random()
        if r < 0.1:
            k = 1e-300 ** rng.random()
            a = tuple(ac + k * rc for ac, rc in zip(a, random_point()))
        elif r < 0.55:
            a = tuple(ac + 4 * EPS * rc for ac, rc in zip(a, random_point()))
        else:
            k = 1 + 4 * EPS * rng.random()
            a = tuple(ac * k for ac in a)
        if sum(c * c for c in a) >= 2.2250738585072014e-308:
            return a


SIMPLE = [
    ((1, -0.5, -0.5), (1, 0.5, 0.5)),
    ((1, 0, 0), (0, 1, 0)),
    ((0.75, 0, -1), (0.75, 0, 1)),
    ((1, 0, 0.75), (0, 1, 0.75)),
    ((1, 0.9, 0.95), (-1, 0.95, 0.9)),
]


def face_edges():
    raw = []
    for a, b in SIMPLE:
        raw.append((a, b))
        raw.append((b, a))
    for _ in range(60):
        face = rng.randrange(6)
        i = rng.randrange(4)
        j = (i + 1) & 3
        p = FACE_UV[face](*BIUNIT[i])
        q_ = FACE_UV[face](*BIUNIT[j])
        raw.append((perturbed_corner_or_midpoint(p, q_), perturbed_corner_or_midpoint(p, q_)))
    # A few edges in general position, an antipodal one and a degenerate one.
    for _ in range(8):
        raw.append((random_point(), random_point()))
    raw.append(((0.6, 0.0, 0.8), (-0.6, 0.0, -0.8)))
    raw.append(((0.0, 0.6, 0.8), (0.0, 0.6, 0.8)))
    points = normalized([p for edge in raw for p in edge])
    return [(points[2 * k], points[2 * k + 1]) for k in range(len(raw))]


PADDINGS = [0.0, 1e-15, 0.5]


def face_section():
    edges = face_edges()
    seg_out = ask([f"clip_segments {q(a)} {q(b)}" for a, b in edges])
    clip_queries = [
        f"clip_face {q(a)} {q(b)} {face} {pad!r}" for a, b in edges for face in range(6) for pad in PADDINGS
    ]
    clip_out = iter(ask(clip_queries))
    rows = []
    for (a, b), segs in zip(edges, seg_out):
        v = segs.split()
        segments = []
        for k in range(0, len(v), 5):
            face = int(v[k])
            nums = list(map(float, v[k + 1 : k + 5]))
            segments.append(f"{{ face: {face}, a: {tup(nums[0:2])}, b: {tup(nums[2:4])} }}")
        clips = []
        for face in range(6):
            for pad in PADDINGS:
                r = next(clip_out).split()
                if r[0] == "1":
                    clips.append(f"{{ face: {face}, padding: {f(pad)}, hit: Bool.True, uv: {tup(map(float, r[1:5]))} }}")
                else:
                    clips.append(f"{{ face: {face}, padding: {f(pad)}, hit: Bool.False, uv: (0.0, 0.0, 0.0, 0.0) }}")
        rows.append(
            f"{{ a: {tup(a)}, b: {tup(b)}, segments: [{', '.join(segments)}], clips: [{', '.join(clips)}] }}"
        )
    return rows


# Edge clipping in the plane ----------------------------------------------


def rects():
    out = []
    for _ in range(5):
        x1, y1, x2, y2 = (rng.uniform(-1.0, 1.0) for _ in range(4))
        out.append((min(x1, x2), max(x1, x2), min(y1, y2), max(y1, y2)))
    out.append((-0.7, -0.7, 0.3, 0.35))
    out.append((0.2, 0.5, 0.3, 0.3))
    out.append((-0.7, 0.3, 0.0, 0.0))
    out.append((0.3, 0.3, 0.8, 0.8))
    out.append((1.0, 0.0, 1.0, 0.0))
    return out


def choose_endpoint(r):
    """Upstream's ChooseEndpoint: inside, on the boundary, or anywhere."""
    x0, x1, y0, y1 = r
    empty = x0 > x1
    k = rng.randrange(4)
    if k == 0 and not empty:
        return (rng.uniform(x0, x1), rng.uniform(y0, y1))
    if k == 1 and not empty:
        if rng.random() < 0.5:
            return (rng.choice([x0, x1]), rng.uniform(y0, y1))
        return (rng.uniform(x0, x1), rng.choice([y0, y1]))
    if k == 2 and not empty:
        return (rng.choice([x0, x1]), rng.choice([y0, y1]))
    return (rng.uniform(-1.0, 1.0), rng.uniform(-1.0, 1.0))


def edge_section():
    cases = []
    for r in rects():
        for _ in range(12):
            cases.append((choose_endpoint(r), choose_endpoint(r), r))
    hit = ask([f"clip_rect_hit {q(a)} {q(b)} {q(r)}" for a, b, r in cases])
    clip = ask([f"clip_edge {q(a)} {q(b)} {q(r)}" for a, b, r in cases])
    bound_queries = []
    for a, b, r in cases:
        pair = (min(a[0], b[0]), max(a[0], b[0]), min(a[1], b[1]), max(a[1], b[1]))
        bound_queries.append(f"clip_bound {q(a)} {q(b)} {q(r)} {q(pair)}")
    bound = ask(bound_queries)
    rows = []
    for (a, b, r), h, c, bd in zip(cases, hit, clip, bound):
        c = c.split()
        ends = tuple(map(float, c[1:5])) if c[0] == "1" else (0.0, 0.0, 0.0, 0.0)
        bd = bd.split()
        clipped_bound = tuple(map(float, bd[-4:]))
        rows.append(
            f"{{ a: {tup(a)}, b: {tup(b)}, clip: {tup(r)}, hits: {'Bool.True' if h == '1' else 'Bool.False'}, "
            f"clipped: {'Bool.True' if c[0] == '1' else 'Bool.False'}, ends: {tup(ends)}, bound: {tup(clipped_bound)} }}"
        )
    # Clipping a bound that an earlier clip already shrank, as upstream does
    # when it clips one edge to the cells of a hierarchy.
    chained = []
    for _ in range(30):
        a = (rng.uniform(-1.0, 1.0), rng.uniform(-1.0, 1.0))
        b = (rng.uniform(-1.0, 1.0), rng.uniform(-1.0, 1.0))
        outer = (-0.6, 0.6, -0.6, 0.6)
        x1, y1, x2, y2 = (rng.uniform(-0.8, 0.8) for _ in range(4))
        inner = (min(x1, x2), max(x1, x2), min(y1, y2), max(y1, y2))
        first = ask([f"clip_bound {q(a)} {q(b)} {q(outer)} " + q((min(a[0], b[0]), max(a[0], b[0]), min(a[1], b[1]), max(a[1], b[1])))])[0].split()
        if first[0] != "1":
            continue
        start = tuple(map(float, first[1:5]))
        second = ask([f"clip_bound {q(a)} {q(b)} {q(inner)} {q(start)}"])[0].split()
        result = tuple(map(float, second[1:5])) if second[0] == "1" else (0.0, 0.0, 0.0, 0.0)
        chained.append(
            f"{{ a: {tup(a)}, b: {tup(b)}, clip: {tup(inner)}, bound: {tup(start)}, "
            f"ok: {'Bool.True' if second[0] == '1' else 'Bool.False'}, result: {tup(result)} }}"
        )
    return rows, chained


def main():
    faces = face_section()
    edges, chained = edge_section()
    w = []
    w.append("## Upstream's answers for edge clipping, the cases of `s2edge_clipping_test.cc`.")
    w.append("##")
    w.append("## Generated by `tools/generate_clipping_corpus.py` from upstream's")
    w.append("## `s2edge_clipping.h` through `tools/s2_oracle.cc`. Do not edit by hand.")
    w.append("##")
    w.append("## Internal to this package.")
    w.append("ClippingCorpus := [].{")
    w.append("")
    w.append("\t## Edges between unit-length points: the parts that `GetFaceSegments` gives, and")
    w.append("\t## `ClipToPaddedFace` of the edge for each face and padding, with the two ends")
    w.append("\t## as `(au, av, bu, bv)` when the edge meets the face.")
    w.append("\tfaces : List({ a : (F64, F64, F64), b : (F64, F64, F64), segments : List({ face : U64, a : (F64, F64), b : (F64, F64) }), clips : List({ face : U64, padding : F64, hit : Bool, uv : (F64, F64, F64, F64) }) })")
    w.append("\tfaces = [")
    for r in faces:
        w.append(f"\t\t{r},")
    w.append("\t]")
    w.append("")
    w.append("\t## Edges in the plane against a rectangle `(x_lo, x_hi, y_lo, y_hi)`: `IntersectsRect`,")
    w.append("\t## whether `ClipEdge` keeps a part, its ends as `(ax, ay, bx, by)`, and")
    w.append("\t## `GetClippedEdgeBound`.")
    w.append("\tedges : List({ a : (F64, F64), b : (F64, F64), clip : (F64, F64, F64, F64), hits : Bool, clipped : Bool, ends : (F64, F64, F64, F64), bound : (F64, F64, F64, F64) })")
    w.append("\tedges = [")
    for r in edges:
        w.append(f"\t\t{r},")
    w.append("\t]")
    w.append("")
    w.append("\t## `ClipEdgeBound` of a bound that an earlier clip shrank.")
    w.append("\tchained : List({ a : (F64, F64), b : (F64, F64), clip : (F64, F64, F64, F64), bound : (F64, F64, F64, F64), ok : Bool, result : (F64, F64, F64, F64) })")
    w.append("\tchained = [")
    for r in chained:
        w.append(f"\t\t{r},")
    w.append("\t]")
    w.append("}")
    print("\n".join(w))


main()

#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Heorhii Bulakh
# SPDX-License-Identifier: UPL-1.0
"""Generate tests/CodingCorpus.roc: upstream's binary encodings of S2 types.

The oracle (tools/s2_oracle.cc) writes each value with upstream's `Encode`
method and reads hex back through upstream's `Decode`. This script chooses the
values, asks the oracle for the bytes, and writes them as Roc data together
with the numbers they hold, read back out of the bytes so that the Roc side
builds exactly the value that upstream wrote.

It also asks upstream for a verdict on malformed input: whether `Decode`
accepts it, and what encoding of the decoded value it then gives. It checks
that upstream refuses every truncation of one sample of each type.

The compressed formats come from the fixtures of upstream's
s2point_compression_test.cc (regular loops snapped to a level, loops with some
points not snapped, a loop over several faces, a straight line, and a first
point on the edge of a face), and from polylines and polygons whose vertices
are mostly cell centres. Upstream's `S2EncodePointsCompressed` writes the
points, `EncodeMostCompact` the polylines, and `Encode` with its default hint
the polygons.

Usage:

    python3 tools/generate_coding_corpus.py .tmp/oracle14/build/s2_oracle > tests/CodingCorpus.roc
    roc fmt tests
"""

import math
import struct
import subprocess
import sys

ORACLE = sys.argv[1]


def ask(lines):
    out = subprocess.run(
        [ORACLE], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True
    ).stdout.splitlines()
    assert len(out) == len(lines), (len(out), len(lines))
    return out


def enc(queries):
    return ask(["code_enc " + q for q in queries])


def dec(kind, hexes):
    return ask([f"code_dec {kind} {h}" for h in hexes])


def f(x):
    s = "%.17g" % x
    if "e" in s:
        m, e = s.split("e")
        if "." not in m:
            m += ".0"
        return f"{m}e{int(e)}"
    return s if "." in s else s + ".0"


def doubles(b, n):
    return list(struct.unpack("<%dd" % n, b[: 8 * n]))


def tup(vs):
    return "(" + ", ".join(f(v) for v in vs) + ")"


def u32(b, o):
    return struct.unpack_from("<I", b, o)[0]


def points_list(vs):
    return "[" + ", ".join(tup(v) for v in vs) + "]"


def read_points(b, o, n):
    return [tuple(doubles(b[o + 24 * i :], 3)) for i in range(n)], o + 24 * n


def parse_loop(b, o):
    assert b[o] == 1
    n = u32(b, o + 1)
    pts, o = read_points(b, o + 5, n)
    o += 1 + 4
    assert b[o] == 1
    bound = tuple(doubles(b[o + 1 :], 4))
    return pts, bound, o + 33


# Compressed formats ------------------------------------------------------

def snap_points(points, level):
    out = ask([f"cell_snap {p[0]!r} {p[1]!r} {p[2]!r} {level}" for p in points])
    return [tuple(map(float, line.split())) for line in out]


def regular(n, km=0.1):
    # S2Testing::MakeRegularPoints around (1, 1, 1) with a radius in km.
    degrees = km / 6371.01 * 180 / math.pi
    v = list(map(float, ask([f"loop_regular N 1 1 1 {degrees!r} {n}"])[0].split()))
    return [tuple(v[3 * i : 3 * i + 3]) for i in range(n)]


def raw_chain(points):
    return f"{len(points)} " + " ".join("%r %r %r" % p for p in points)


def compression_fixtures():
    """The fixtures of upstream's S2PointCompressionTest, with the encoded size
    that upstream's test expects, or None."""
    loop_100 = regular(100)
    mixed_15 = list(loop_100)
    for i in range(15):
        mixed_15[3 * i] = snap_points([mixed_15[3 * i]], 30)[0]
    mixed_25 = list(loop_100)
    for i in range(25):
        mixed_25[4 * i] = snap_points([mixed_25[4 * i]], 30)[0]
    faces = []
    for face, u, v in ((0, -0.5, 0.5), (1, -0.5, 0.5), (1, 0.5, -0.5), (2, -0.5, 0.5), (2, 0.5, -0.5), (2, 0.5, 0.5)):
        xyz = {0: (1.0, u, v), 1: (-u, 1.0, v), 2: (-u, -v, 1.0)}[face]
        faces.append(normalized_point(xyz))
    line = []
    for i in range(100):
        u = st_to_uv(0.01 + 0.005 * i)
        v = st_to_uv(0.01 + 0.009 * i)
        line.append(normalized_point((1.0, u, v)))
    return [
        ("empty", 30, [], 1),
        ("loop_4", 30, snap_points(regular(4), 30), 39),
        ("loop_4_unsnapped", 30, regular(4), None),
        ("loop_4_level_14", 14, snap_points(regular(4), 14), 23),
        ("loop_100", 30, snap_points(loop_100, 30), 257),
        ("loop_100_unsnapped", 30, loop_100, 2756),
        ("loop_100_mixed_15", 30, mixed_15, 2381),
        ("loop_100_mixed_25", 30, mixed_25, 2131),
        ("loop_100_level_22", 22, snap_points(loop_100, 22), 148),
        ("multi_face", 30, snap_points(faces, 30), None),
        ("line", 30, snap_points(line, 30), 117),
        ("first_point_on_face_edge", 8, [
            (0.054299323861222645, -0.70606358900180299, 0.70606358900180299),
            (0.056482651436986935, -0.70781701406865505, 0.70413406726388494),
        ], None),
        ("level_0", 0, snap_points([(1.0, 0.0, 0.0), (0.0, -1.0, 0.0), (0.0, 0.0, 1.0)], 0), None),
    ]


def st_to_uv(s_):
    # S2::STtoUV, the quadratic projection.
    if s_ >= 0.5:
        return (1 / 3.0) * (4 * s_ * s_ - 1)
    return (1 / 3.0) * (1 - 4 * (1 - s_) * (1 - s_))


def normalized_point(p):
    return tuple(map(float, ask([f"point2 mul N {p[0]!r} {p[1]!r} {p[2]!r} 1 1 1"])[0].split()))


# Values -----------------------------------------------------------------

def circle(n, lat, lng, r):
    return [
        "L %.4f %.4f"
        % (lat + r * math.sin(2 * math.pi * i / n), lng + r * math.cos(2 * math.pi * i / n))
        for i in range(n)
    ]


def chain(items):
    return f"{len(items)} " + " ".join(items)


def level_cells(level, count, face=0, start=0):
    shift = 2 * (30 - level)
    return [(face << 61) | ((start + i) << (shift + 1)) | (1 << shift) for i in range(count)]


FACE0 = 1 << 60
SF_LEAF = 0x8085809E8E8D8C61
POINTS = ["1 0 0", "N 1 2 3", "N -3 4 -12", "-0 0 1", "L 37.7749 -122.4194", "0.6 0.8 0", "2 3 4"]
LATLNGS = [(0.5, -1.25), (0.0, 0.0), (1.5707963267948966, 3.141592653589793), (10.0, 20.0), (-0.0, 1e-300)]
CAPS = ["cap 1 0 0 10", "cap N 1 2 3 0", "cap L 37.7749 -122.4194 2", "cap 0 0 1 180", "cap_empty", "cap_full", "cap 1 0 0 90"]
RECTS = [
    "rect -0.5 0.5 -1 2",
    "rect_empty",
    "rect_full",
    "rect 0.1 0.2 3.0 -3.0",
    "rect -1.5707963267948966 0 -3.141592653589793 3.141592653589793",
    "rect 0.3 0.3 0.7 0.7",
]
CELL_IDS = [0, 1, FACE0, 5 << 61 | (1 << 60), SF_LEAF, SF_LEAF >> 40 << 40 | (1 << 39), (1 << 64) - 1, (1 << 63)]
VALID_CELLS = [FACE0, 5 << 61 | (1 << 60), SF_LEAF, level_cells(12, 1, 2, 12345)[0], level_cells(30, 1, 3, 98765)[0]]
UNIONS = [
    [],
    [FACE0],
    level_cells(12, 5, 4, 777),
    level_cells(8, 300, 0, 100),
    [5 << 61 | (1 << 60), FACE0, FACE0, 0, 5],
]
POINT_REGIONS = ["1 0 0", "N 1 2 3", "L 37.7749 -122.4194", "0 0 -1"]
LOOPS = [
    "loop_empty",
    "loop_full",
    "loop 3 L 0 0 L 0 5 L 5 0",
    "loop 3 L 0 0 L 5 0 L 0 5",
    "loop 4 L 80 0 L 80 90 L 80 180 L 80 -90",
    "loop 4 L -80 0 L -80 -90 L -80 180 L -80 90",
    "loop 4 L -10 170 L -10 -170 L 10 -170 L 10 170",
    "loop 3 L 0 0 L 0 0 L 0 5",
    "loop " + chain(circle(200, 30, 40, 10)),
]
LINES = [
    "line 0",
    "line 1 L 10 10",
    "line 2 L 0 0 L 0 5",
    "line 5 N 1 0 0 N 1 1 0 N 1 1 1 N 0 1 1 N -1 1 -1",
    "line " + chain(["L %d %d" % (i % 7 * 10 - 30, i * 3 - 150) for i in range(100)]),
]
SQUARE = "4 L 0 0 L 0 10 L 10 10 L 10 0"
POLYS = [
    "poly_empty",
    "poly_full",
    "poly 1 3 L 0 0 L 0 5 L 5 0",
    "poly 2 " + SQUARE + " 4 L 2 2 L 2 8 L 8 8 L 8 2",
    "poly 3 " + SQUARE + " 4 L 2 2 L 2 8 L 8 8 L 8 2 4 L 4 4 L 4 6 L 6 6 L 6 4",
    "poly 2 3 L 0 0 L 0 5 L 5 0 3 L 20 20 L 20 25 L 25 20",
    "poly 1 4 L 80 0 L 80 90 L 80 180 L 80 -90",
    "poly 1 3 L 0 0 L 5 0 L 0 5",
    "poly 2 " + chain(circle(50, 0, 0, 20)) + " " + chain(circle(30, 0, 0, 8)),
]


def main():
    out = []
    w = out.append
    w("## Upstream's binary encodings of S2 types, and its verdicts on malformed input.")
    w("##")
    w("## Generated by `tools/generate_coding_corpus.py` from upstream's `Encode` and")
    w("## `Decode`. Do not edit by hand.")
    w("##")
    w("## Internal to this package.")
    w("CodingCorpus := [].{")
    w("")

    def section(name, doc, typ, rows):
        w(f"\t## {doc}")
        w(f"\t{name} : List({typ})")
        w(f"\t{name} = [")
        for r in rows:
            w(f"\t\t{r},")
        w("\t]")
        w("")

    xyz = "(F64, F64, F64)"
    hexes = {}

    hs = enc([f"point {p}" for p in POINTS])
    hexes["point"] = hs
    section("points", "A point: 24 bytes.", f"{{ hex : Str, xyz : {xyz} }}",
            [f'{{ hex: "{h}", xyz: {tup(doubles(bytes.fromhex(h), 3))} }}' for h in hs])

    hs = enc([f"latlng {a} {b}" for a, b in LATLNGS])
    hexes["latlng"] = hs
    section("latlngs", "A position in radians: 16 bytes.", "{ hex : Str, lat : F64, lng : F64 }",
            [f'{{ hex: "{h}", lat: {f(doubles(bytes.fromhex(h), 2)[0])}, lng: {f(doubles(bytes.fromhex(h), 2)[1])} }}' for h in hs])

    hs = enc(CAPS)
    hexes["cap"] = hs
    section("caps", "A cap: a centre and a squared chord length, 32 bytes.", f"{{ hex : Str, center : {xyz}, length2 : F64 }}",
            [f'{{ hex: "{h}", center: {tup(doubles(bytes.fromhex(h), 4)[:3])}, length2: {f(doubles(bytes.fromhex(h), 4)[3])} }}' for h in hs])

    hs = enc(RECTS)
    hexes["rect"] = hs
    section("rects", "A rectangle: the version byte and four bounds, 33 bytes.",
            "{ hex : Str, lat_lo : F64, lat_hi : F64, lng_lo : F64, lng_hi : F64 }",
            [
                '{ hex: "%s", lat_lo: %s, lat_hi: %s, lng_lo: %s, lng_hi: %s }'
                % ((h,) + tuple(f(v) for v in doubles(bytes.fromhex(h)[1:], 4)))
                for h in hs
            ])

    hs = enc([f"cellid {i}" for i in CELL_IDS])
    hexes["cellid"] = hs
    section("cell_ids", "A cell id, valid or not: 8 bytes.", "{ hex : Str, id : U64 }",
            [f'{{ hex: "{h}", id: {i} }}' for h, i in zip(hs, CELL_IDS)])

    hs = enc([f"cell {i}" for i in VALID_CELLS])
    hexes["cell"] = hs
    section("cells", "A cell: the id of a valid cell, 8 bytes.", "{ hex : Str, id : U64 }",
            [f'{{ hex: "{h}", id: {i} }}' for h, i in zip(hs, VALID_CELLS)])

    hs = enc([f"union {len(u)} " + " ".join(map(str, u)) for u in UNIONS])
    hexes["union"] = hs
    section("unions", "A cell union as written, normalized or not.", "{ hex : Str, ids : List(U64) }",
            [f'{{ hex: "{h}", ids: [{", ".join(map(str, u))}] }}' for h, u in zip(hs, UNIONS)])

    hs = enc([f"pointregion {p}" for p in POINT_REGIONS])
    hexes["pointregion"] = hs
    section("point_regions", "A point region: the version byte and a point, 25 bytes.", f"{{ hex : Str, xyz : {xyz} }}",
            [f'{{ hex: "{h}", xyz: {tup(doubles(bytes.fromhex(h)[1:], 3))} }}' for h in hs])

    hs = enc(LOOPS)
    hexes["loop"] = hs
    rows = []
    for h in hs:
        pts, bound, _ = parse_loop(bytes.fromhex(h), 0)
        rows.append(f'{{ hex: "{h}", vertices: {points_list(pts)}, bound: {tup(bound)} }}')
    section("loops", "A loop of depth 0, with its vertices and its bound.",
            f"{{ hex : Str, vertices : List({xyz}), bound : (F64, F64, F64, F64) }}", rows)

    hs = enc(LINES)
    hexes["line"] = hs
    rows = []
    for h in hs:
        b = bytes.fromhex(h)
        pts, _ = read_points(b, 5, u32(b, 1))
        rows.append(f'{{ hex: "{h}", vertices: {points_list(pts)} }}')
    section("lines", "A polyline in the lossless format.", f"{{ hex : Str, vertices : List({xyz}) }}", rows)

    hs = enc(POLYS)
    hexes["poly"] = hs
    rows = []
    for h in hs:
        b = bytes.fromhex(h)
        n = u32(b, 3)
        o = 7
        loops = []
        for _ in range(n):
            pts, bound, o = parse_loop(b, o)
            loops.append(f"{{ vertices: {points_list(pts)}, bound: {tup(bound)} }}")
        rows.append(f'{{ hex: "{h}", loops: [{", ".join(loops)}] }}')
    section("polygons", "A polygon in the lossless format, with the vertices and the bound of each loop.",
            f"{{ hex : Str, loops : List({{ vertices : List({xyz}), bound : (F64, F64, F64, F64) }}) }}", rows)

    # Compressed points.
    fixtures = compression_fixtures()
    hs = enc([f"points {level} {raw_chain(pts)}" for _, level, pts, _ in fixtures])
    rows = []
    for (name, level, pts, size), h in zip(fixtures, hs):
        if size is not None:
            assert len(h) // 2 == size, (name, len(h) // 2, size)
        back = ask([f"code_dec points {level} {len(pts)} {h}"])[0].split()
        assert back[0] == "ok" and int(back[1]) == len(h) // 2, (name, back[:2])
        decoded = [tuple(map(float, back[2 + 3 * i : 5 + 3 * i])) for i in range(len(pts))]
        assert decoded == pts, name
        rows.append(f'{{ name: "{name}", level: {level}, points: {points_list(pts)}, hex: "{h}" }}')
    section("compressed_points", "Points in upstream's compressed format, which decode to the same points.",
            f"{{ name : Str, level : U64, points : List({xyz}), hex : Str }}", rows)
    point_sample = hs[1]

    # Polylines in the most compact format.
    snapped = {name: pts for name, _, pts, _ in fixtures}
    level_10 = ["N " + ask([f"cell_point_raw {c}"])[0] for c in level_cells(10, 4, 1, 3)]
    compact_lines = [
        [],
        snapped["loop_4"],
        snapped["loop_100_level_22"],
        snapped["loop_100_mixed_25"],
        snapped["loop_100_mixed_15"],
        snapped["multi_face"],
        snapped["line"],
        snapped["level_0"],
    ]
    hs = enc([f"line_compact {raw_chain(pts)}" for pts in compact_lines])
    hexes["line_compact"] = hs
    rows = [f'{{ vertices: {points_list(pts)}, hex: "{h}" }}' for pts, h in zip(compact_lines, hs)]
    section("compact_lines", "Polylines as `EncodeMostCompact` writes them, compressed or not.",
            f"{{ vertices : List({xyz}), hex : Str }}", rows)

    # Polygons with the default hint.
    hole = snap_points(regular(20, 0.03), 22)
    mixed_22 = list(snapped["loop_100_unsnapped"])
    for i in range(22):
        mixed_22[4 * i] = snap_points([mixed_22[4 * i]], 30)[0]
    polys = [
        "0",
        "1 1 0 0 -1",
        "1 " + raw_chain(snapped["level_0"]),
        "1 " + raw_chain(snapped["loop_4"]),
        "1 " + raw_chain(snapped["loop_100_level_22"]),
        "2 " + raw_chain(snapped["loop_100_level_22"]) + " " + raw_chain(hole),
        "1 " + raw_chain(snapped["loop_100_mixed_25"]),
        "1 " + raw_chain(snapped["loop_100_mixed_15"]),
        "1 4 " + " ".join(level_10),
        # 64 vertices, the fewest whose loop stores its bound.
        "1 " + raw_chain(snap_points(regular(64), 30)),
        # 78 of 100 vertices not snapped: just too many for the compressed
        # format, which 75 of 100 are not.
        "1 " + raw_chain(mixed_22),
    ]
    compact = enc([f"poly_compact {p}" for p in polys])
    lossless = enc([f"poly {p}" for p in polys])
    hexes["poly_compact"] = compact
    rows = []
    for c, l in zip(compact, lossless):
        b = bytes.fromhex(l)
        n = u32(b, 3)
        o = 7
        loops = []
        for _ in range(n):
            pts, bound, o = parse_loop(b, o)
            loops.append(f"{{ vertices: {points_list(pts)}, bound: {tup(bound)} }}")
        verdict = dec("poly", [c])[0]
        assert verdict.startswith("ok "), verdict
        rows.append(f'{{ hex: "{c}", loops: [{", ".join(loops)}], decoded: "{verdict[3:]}" }}')
    section("compact_polygons", "Polygons as `Encode` writes them by default, with the vertices and the bound of\n"
            "\t## each loop, and the lossless encoding of what `Decode` reads back from them.",
            f"{{ hex : Str, loops : List({{ vertices : List({xyz}), bound : (F64, F64, F64, F64) }}), decoded : Str }}", rows)

    # Verdicts on bytes that are not a plain encoding.
    cases = []  # (kind, name, hex)

    def add(kind, name, h):
        cases.append((kind, name, h))

    def mutate(h, offset, byte):
        b = bytearray(bytes.fromhex(h))
        b[offset] = byte
        return b.hex()

    samples = {
        "point": hexes["point"][1], "latlng": hexes["latlng"][0], "cap": hexes["cap"][2],
        "rect": hexes["rect"][0], "cellid": hexes["cellid"][4], "cell": hexes["cell"][2],
        "union": hexes["union"][2], "pointregion": hexes["pointregion"][1],
        "loop": hexes["loop"][2], "line": hexes["line"][3], "poly": hexes["poly"][4],
    }
    for kind in ("rect", "union", "pointregion", "loop", "line", "poly"):
        for v in (0, 2, 3, 4, 5, 255):
            add(kind, f"version {v}", mutate(samples[kind], 0, v))
    for kind in ("point", "latlng", "cap", "cellid", "cell"):
        add(kind, "trailing bytes", samples[kind] + "deadbeef")
    for kind in ("rect", "union", "pointregion", "loop", "line", "poly"):
        add(kind, "trailing bytes", samples[kind] + "deadbeef")
    # Fields upstream does not check.
    nl = u32(bytes.fromhex(samples["loop"]), 1)
    add("loop", "origin_inside byte 2", mutate(samples["loop"], 5 + 24 * nl, 2))
    tp = enc(["poly 1 3 L 0 0 L 0 5 L 5 0"])[0]
    add("poly", "huge depth", tp[: 2 * (7 + 6 + 24 * 3)] + "ffffff7f" + tp[2 * (7 + 10 + 24 * 3):])
    zero_loop = "01" + "00000000" + "00" + "00000000" + enc(["rect_empty"])[0]
    add("loop", "zero vertices", zero_loop)
    add("loop", "count too large", "01ffffffff" + "00" * 40)
    add("loop", "count 50000001", "0181f0fa02" + "00" * 40)
    add("union", "count too large", "01" + "ffffffffffffffff" + "00" * 16)
    add("union", "count 1000001", "01" + "41420f0000000000" + "00" * 16)
    add("union", "count 2 with 1 cell", "01" + "0200000000000000" + "00" * 8)
    add("union", "count 0", "01" + "0000000000000000")
    add("poly", "count too large", "010100ffffffff")
    add("poly", "count 10000001", "01010081969800")
    add("line", "count too large", "01ffffffff")
    for r in ("rect 2 3 0 1", "rect 1 0 0 1", "rect 0 1 0 4", "rect -0.5 0.5 -3.141592653589793 1"):
        add("rect", r, enc([r])[0])
    add("pointregion", "not unit length", enc(["pointregion 2 3 4"])[0])
    add("pointregion", "zero", enc(["pointregion 0 0 0"])[0])
    add("cell", "invalid id 0", hexes["cellid"][0])
    add("cell", "invalid id 1", hexes["cellid"][1])
    add("cell", "sentinel", hexes["cellid"][6])
    # A polygon holding an empty loop and a loop with no vertex: upstream drops both.
    tri = enc(["loop 3 L 0 0 L 0 5 L 5 0"])[0]
    tri_poly = enc(["poly 1 3 L 0 0 L 0 5 L 5 0"])[0]
    bound = tri_poly[-66:]
    for name, loops in (
        ("empty loop dropped", [tri, enc(["loop_empty"])[0]]),
        ("empty loop first", [enc(["loop_empty"])[0], tri]),
        ("zero vertex loop dropped", [zero_loop, tri]),
        ("full loop kept", [enc(["loop_full"])[0]]),
        ("only empty loops", [enc(["loop_empty"])[0], enc(["loop_empty"])[0]]),
    ):
        n = "%08x" % len(loops)
        n = bytes.fromhex(n)[::-1].hex()
        add("poly", name, "010100" + n + "".join(loops) + bound)
    # Compressed forms.
    snap = ["N " + ask([f"cell_point_raw {c}"])[0] for c in level_cells(10, 4, 1, 3)]
    snap_chain = "4 " + " ".join(snap)
    for name, q in (("compact snapped chain", f"line_compact {snap_chain}"), ("compact empty", "line_compact 0")):
        add("line", name, enc([q])[0])
    for name, q in (
        ("compact snapped loop", f"poly_compact 1 {snap_chain}"),
        ("compact square", "poly_compact 1 4 L 0 0 L 0 10 L 10 10 L 10 0"),
        ("compact empty", "poly_compact 0"),
    ):
        add("poly", name, enc([q])[0])
    # Malformed compressed bytes. The line and polygon samples are loop_4,
    # whose faces are one run on face 0 and whose first point takes 8 bytes.
    line4 = hexes["line_compact"][1]
    poly4 = hexes["poly_compact"][3]
    assert line4.startswith("021e04") and poly4.startswith("041e0104"), (line4, poly4)
    for kind, h, head in (("line", line4, 3), ("poly", poly4, 4)):
        add(kind, "compact level 31", mutate(h, 1, 31))
        add(kind, "compact trailing bytes", h + "deadbeef")
        # A face run of no points.
        add(kind, "compact face run of 0", mutate(h, head, 0))
        # More points written in full than there are points: the count after
        # the first point and the three varints of the others.
        b = bytes.fromhex(h)
        add(kind, "compact bad varint", h[: 2 * head] + "ffffffffffffffffffff7f" + h[2 * head + 2 :])
    # The off-center count of the line sample, at the end of its bytes.
    lb = bytearray(bytes.fromhex(line4))
    assert lb[-1] == 0
    add("line", "compact 5 off-center points", bytes(lb[:-1] + bytes([5])).hex())
    add("line", "compact off-center index 4", bytes(lb[:-1]).hex() + "0104" + "00" * 24)
    add("line", "compact off-center index 3", bytes(lb[:-1]).hex() + "0103" + "000000000000f03f" + "00" * 16)
    add("line", "compact count above bytes left", "021e05" + line4[6:])
    add("line", "compact count 0 then bytes", "021e00" + line4[6:])
    # Polygons: too many loops, a loop of no vertex, a bound flag on a loop
    # without a bound, an empty loop, and a huge depth.
    add("poly", "compact count 10000001", "041e" + "81ade204")
    add("poly", "compact loop of no vertex", "041e0100" + poly4[8:])
    pb = bytearray(bytes.fromhex(poly4))
    assert pb[-2:] == bytes([0, 0]), poly4
    add("poly", "compact bound flag", bytes(pb[:-2] + bytes([2, 0])).hex())
    add("poly", "compact bound flag and bound", bytes(pb[:-2] + bytes([2, 0])).hex() + enc(["rect 0.1 0.2 0.3 0.4"])[0])
    add("poly", "compact huge depth", bytes(pb[:-1]).hex() + "ffffffff0f")
    add("poly", "compact origin inside", bytes(pb[:-2] + bytes([1, 0])).hex())
    empty_loop = "01" + enc(["points 30 1 0 0 1"])[0] + "0000"
    add("poly", "compact empty loop dropped", "041e02" + poly4[6:] + empty_loop)
    add("poly", "compact only an empty loop", "041e01" + empty_loop)

    verdicts = []
    for kind in ("point", "latlng", "cap", "rect", "cellid", "cell", "union", "pointregion", "loop", "line", "poly"):
        group = [c for c in cases if c[0] == kind]
        results = dec(kind, [c[2] for c in group])
        for (k, name, h), r in zip(group, results):
            if r == "err":
                verdict = "-"
            elif r == "invalid":
                verdict = "invalid"
            else:
                assert r.startswith("ok "), r
                verdict = r[3:]
            verdicts.append((k, name, h, verdict))
    rows = [f'{{ kind: "{k}", name: "{n}", hex: "{h}", verdict: "{v}" }}' for k, n, h, v in verdicts]
    section(
        "verdicts",
        "Bytes that are not a plain encoding, and what upstream makes of them. The verdict is `-` when\n"
        "\t## `Decode` refuses them, `invalid` for a cell with an invalid id that upstream would build without\n"
        "\t## meaning, and\n"
        "\t## otherwise the hex of what `Encode` gives for the value that `Decode` read.",
        "{ kind : Str, name : Str, hex : Str, verdict : Str }",
        rows,
    )

    # Every truncation of one sample of each kind is refused, and of the
    # compressed line and polygon samples too.
    sample_list = list(samples.items()) + [("line", line4), ("poly", poly4)]
    for kind, h in sample_list:
        prefixes = [h[:i] or "-" for i in range(0, len(h), 2)]
        for r, p in zip(dec(kind, prefixes), prefixes):
            assert r == "err", (kind, p, r)
    w("\t## The sample of each kind whose truncations are all refused. Upstream refuses them too.")
    w("\ttruncation_samples : List({ kind : Str, hex : Str })")
    w("\ttruncation_samples = [")
    for kind, h in sample_list:
        w(f'\t\t{{ kind: "{kind}", hex: "{h}" }},')
    w("\t]")
    w("")
    # And every truncation of compressed points.
    prefixes = [point_sample[:i] or "-" for i in range(0, len(point_sample), 2)]
    for r, p in zip(ask([f"code_dec points 30 4 {x}" for x in prefixes]), prefixes):
        assert r == "err", (p, r)
    w("\t## Compressed points, four at level 30, whose truncations are all refused, as upstream refuses them.")
    w("\tpoint_truncation_sample : Str")
    w(f'\tpoint_truncation_sample = "{point_sample}"')
    w("}")
    print("\n".join(out))


main()

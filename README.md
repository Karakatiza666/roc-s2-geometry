# roc-s2-geometry

A port of Google's [S2 Geometry Library](https://s2geometry.io) v0.14.0 to Roc.

S2 represents geometry on the sphere, not on a projected plane. So there is no
distortion, no seam at the antimeridian and no special case at the poles. S2
divides the sphere into a hierarchy of cells, and a 64-bit `S2CellId` names
each cell. The ids are ordered so that cells near each other in space are
usually near each other in the ordering. A spatial question thus becomes a
range query that an ordinary database index can answer.

## Using it

```roc
app [main!] {
    s2: "https://github.com/Karakatiza666/roc-s2-geometry/releases/download/0.0.1/AiE9V4gw3PVhB1Y9j33CZ733U5wNyV6TDUUQ3ALXjmhi.tar.zst",
}

import s2.S2Cap
import s2.S2CellId
import s2.S2Earth
import s2.S2LatLng
import s2.S2RegionCoverer

main! = |_args| {
    san_francisco = S2LatLng.from_degrees(37.7749, -122.4194)

    # The level-13 cell that contains the point, as a token to store in a row.
    token = S2CellId.from_lat_lng(san_francisco).parent_at_level(13).to_token()
    echo!("${token}\n")

    # At most 16 cells that cover everything within 2 km of the point.
    around = S2Cap.from_center_angle(san_francisco.to_point(), S2Earth.from_km(2.0))
    covering = S2RegionCoverer.default().with_max_cells(16).with_max_level(16).covering(around)
    for id in covering {
        echo!("${id.to_token()}\n")
    }
    Ok({})
}
```

The release notes of each release give its exact URL. Inside a checkout,
`s2: "../roc-s2-geometry/src/main.roc"` also works.
[The API docs](https://karakatiza666.github.io/roc-s2-geometry/) are those of
the latest stable release.

`examples/covering.roc` is a complete command-line program. It needs no
platform, and CI runs it on every push:

```
$ roc examples/covering.roc -- 37.7749 -122.4194 2 12
leaf 8085809e8e8d8c61
cell 8085807c at level 13
cell 8085809 at level 12
...
```

## What is ported

| Module | What it is |
| --- | --- |
| `S1Angle` | A one-dimensional angle, the unit of every distance |
| `S1ChordAngle` | An angle stored as a squared chord length, so comparisons need no trigonometry |
| `S1Interval` | A closed interval on the circle, which can wrap through +/-pi |
| `R1Interval` | A closed interval on the real line |
| `R2Point` `R2Rect` | A point and an axis-aligned rectangle in the plane, for cube-face coordinates |
| `S2Point` | A vector in three dimensions, with triangle area and centroid |
| `S2LatLng` | A position in latitude and longitude |
| `S2Coords` | The cube-face projection: `xyz` to `uv` to `st` to `ij` |
| `S2Metric` | How the edges, diagonals, widths and areas of cells change with level |
| `S2CellId` | The 64-bit id of a cell, and all that follows from it: parents, children, neighbours, tokens, ranges |
| `S2Cell` | The geometry of a cell: vertices, edges, area, containment, distances |
| `S2CellUnion` | A normalized set of cells, with union, intersection and difference |
| `S2Cap` | A disc on the sphere |
| `S2LatLngRect` | A rectangle in latitude-longitude space |
| `S2RegionCoverer` | Approximates a region with a set of cells |
| `S2RegionTermIndexer` | Converts regions into index terms for a text search system |
| `S2Region` `S2RegionUnion` `S2RegionIntersection` | A region of any type behind one type, and the union and intersection of a list of regions |
| `S2Loop` `S2Polyline` | A simple closed polygon, and an open chain of edges |
| `S2Polygon` | Loops nested into a region with holes, with containment and intersection between two polygons |
| `S2PointRegion` | A single point as a region, so that a coverer can cover it |
| `S2PolylineSimplifier` | Tests whether one edge can replace a chain and pass near some points and away from others |
| `S2PolylineAlignment` | Vertex alignments between polylines by dynamic time warping, and the medoid or consensus of a set of polylines |
| `S2ConvexHullQuery` | The smallest convex loop around a set of points, polylines, loops and polygons |
| `S2Edge` | Edge crossings, intersections, interpolation, and distances between points and edges |
| `S2EdgeCrosser` | Tests one edge against a chain of edges, and reuses work between the tests |
| `S2EdgeClipping` | Clips an edge to the cube faces that it crosses, and clips an edge in a face plane to a rectangle |
| `S2Predicates` | Exact orientation, distance, circumcenter and Voronoi comparisons |
| `S2PaddedCell` | A cell with a padded `(u, v)` bound, for a walk down the cell hierarchy |
| `S2LatLngRectBounder` | The bounding rectangle of a chain of edges, one vertex at a time |
| `S2Projection` `S2EdgeTessellator` | The plate carree and Mercator projections, and the conversion of edges between geodesic and projected form |
| `S2TextFormat` | Reads and writes points, loops, polylines, polygons and cells as short text, e.g. `0:0, 0:5, 5:0` |
| `S2PointCompression` | The compressed encoding of points that are mostly cell centres |
| `S2Earth` | Converts angles to distances on the Earth, with the only fixed radius in the package |

`S2Point`, `S2LatLng`, `S2Cap`, `S2LatLngRect`, `S2CellId`, `S2Cell`,
`S2CellUnion`, `S2PointRegion`, `S2Loop`, `S2Polyline` and `S2Polygon` have
`encode : T -> List(U8)` and `decode : List(U8) -> Try(T, [...])`. They write
the same bytes as upstream's `Encode`, and read all that upstream's `Decode`
reads, the compressed formats included.

## What is not ported

| Not ported | Why |
| --- | --- |
| `S2ShapeIndex` and the shape interface | A large mutable index. A later release can add it |
| `S2BooleanOperation`, `S2Builder`, and polygon union, intersection and difference | They build new geometry, and they need the index and the snapping machinery of `S2Builder` |
| Closest-edge and other index queries, `S2Polygon.approx_equals` | They need the index |
| The encoded vector types of upstream's `s2coder` | Only the shape index uses them |

The predicates between two regions are ported: `S2Loop.contains`,
`S2Loop.intersects`, `S2Polygon.contains_polygon`,
`S2Polygon.intersects_polygon`, and the containment on `S2Cap`, `S2LatLngRect`
and `S2CellUnion`. Upstream uses its index to make them fast. Without an index
they take time proportional to the product of the two vertex counts, and they
give the same answers.

## Differences from upstream

The bounds of a cell are constructors on the bounding type. Roc modules cannot
import each other in a cycle, and `S2Cell`, `S2Cap` and `S2LatLngRect` would
form one. So write `S2LatLngRect.from_cell(cell)` and `S2Cap.from_cell(cell)`
in place of `cell.rect_bound()` and `cell.cap_bound()`.

A region is any type with three methods. Upstream has an `S2Region` base class.
Here `S2RegionCoverer` accepts any type that has `cell_union_bound`,
`contains_cell` and `may_intersect_cell`:

```roc
covering : S2RegionCoverer, r -> List(S2CellId)
    where [
        r.cell_union_bound : r -> List(S2CellId),
        r.contains_cell : r, S2Cell -> Bool,
        r.may_intersect_cell : r, S2Cell -> Bool,
    ]
```

`S2Cap`, `S2Cell`, `S2LatLngRect`, `S2CellUnion`, `S2Loop`, `S2Polyline`,
`S2Polygon` and `S2PointRegion` have these methods, and a type of your own can
have them too. For a type with a cap bound, `|r| r.cap_bound().cell_union_bound()`
is the usual `cell_union_bound`.

A list holds values of one type. To put regions of different types into a
union or an intersection, wrap each one in `S2Region`:

```roc
union = S2RegionUnion.new([S2Region.from_cap(cap), S2Region.from(rect)])
S2RegionCoverer.default().covering(union)
```

`S2Region.from` needs `cap_bound`, `rect_bound` and `contains_point` in
addition to the three methods above. A cap and a cell have no `rect_bound`,
for the reason given before, so they have `S2Region.from_cap` and
`S2Region.from_cell`.

A covering of a loop or a polygon can differ from the covering upstream gives:

- Upstream bounds an `S2Polygon` by the cells of its index. This port bounds
  it by the cells that cover its cap bound, as it does every other region
  except `S2Cell`.
- The `MayIntersect` of an upstream `S2Loop` is conservative. The
  `may_intersect_cell` of this port is exact.

## Exactness

Orientation is the predicate that all the geometry depends on: is the third of
three points to the left or the right of the line through the first two?
Floating point cannot answer this for points that are almost collinear. An
implementation that guesses gives contradictory answers, and those answers
break the algorithms that use them.

`S2Predicates.sign` therefore uses three steps:

1. A rounded determinant gives the answer when its error bound allows.
2. A second formula, made from the edge vectors, gives almost all the
   remaining answers.
3. If the answer is still uncertain, the determinant is calculated exactly
   with Shewchuk's floating-point expansions, in the internal module
   `S2Exact`. An expansion holds a sum of products of doubles as a list of
   non-overlapping doubles, and loses no bits.

A symbolic perturbation decides the points that are exactly collinear. So
the answer is never zero and never inconsistent. The distance, circumcenter
and Voronoi tests of `S2Predicates`, `S2Edge.intersection` and
`S2Point.robust_cross` use the same steps.

Upstream tries `long double` precision between the rounded and the exact step.
This port goes directly to exact arithmetic, which gives the same answers. For
`robust_cross`, the `long double` step of upstream can give a direction that
differs from the exact one in the last digit. Both are within the same error
bound.

The limits of this exactness:

- The error term of a product of two doubles is exact only if it does not
  underflow. A product smaller than about 1e-290 can lose bits or become zero.
  `robust_cross` scales its inputs first, so it stays exact unless it
  multiplies two tiny coordinates together.
- Roc has no `atan2`, and the port's own `atan2` and the builtin trigonometry
  can differ from the C library by one unit in the last place. So a latitude
  or a distance can also differ by one unit in the last place. This includes
  the loop bounds that `S2Polygon.decode` calculates for a compressed polygon,
  because the format stores no bound for a loop of fewer than 64 vertices.
- Without an index, the cell tests and distances of `S2Loop` and `S2Polygon`
  take linear time in the vertex count. `is_valid` and the predicates between
  two shapes take quadratic time.

## Development

| Path | What it is |
| --- | --- |
| `src/main.roc` | The public entry point. A release bundles it and the modules it imports |
| `src/Internal/` | The internal modules `S2Boundary`, `S2Coder`, `S2Crossing`, `S2Exact`, `S2Format`, `S2Lookup` and `S2Math`. `main.roc` does not expose them |
| `tests/main.roc` | The test entry point. It imports `src/` as `s2` and adds the corpus sweeps |
| `tests/` | The golden corpora and the modules that sweep them |
| `examples/` | Complete programs that use the package as an app does |
| `tools/` | The generators that write the corpora, and `s2_oracle.cc` |
| `scripts/all_tests.sh` | Format check, type check, tests, examples and docs |
| `scripts/bundle.sh` | Writes the release bundle to `dist/` and lists its files |
| `scripts/test_bundle.sh` | Runs the examples against a bundle file or a release URL |
| `.roc-version` | The compiler nightly that CI installs |

### Tests

```
scripts/all_tests.sh
scripts/bundle.sh && scripts/test_bundle.sh
```

The first script checks the format, type-checks both entry points, runs the
tests and the examples, and generates the docs. The second line bundles the
package and runs the examples against that bundle, served on localhost.
GitHub Actions runs both against the pinned nightly on Linux x64 and arm64,
macOS on Apple silicon and Intel, and Windows.

`roc test src/main.roc` runs the unit tests, which are next to the code that
they test. `roc test tests/main.roc` runs the corpus sweeps, and each sweep
checks all the cases in one golden corpus. It also runs the unit tests of the
modules that the sweeps import, but not of the other modules, so the script
runs both.

The corpora make the tests more than a self-consistency check, because their
expected values come from other implementations:

| Corpus | Source | Checks |
| --- | --- | --- |
| `CellIdCorpus` | s2sphere | ids, tokens, face/i/j/orientation, centres, ancestors, traversal, all three kinds of neighbour |
| `CellCorpus` | s2sphere | vertices, three area methods, rectangle and cap bounds |
| `RegionCorpus` | s2sphere | cap and rectangle measures, their bounds, and their predicates against cells |
| `CellUnionCorpus` | s2sphere | normalization, union, intersection, difference, containment |
| `CoverCorpus` | upstream C++ | coverings and interior coverings, cell for cell and in order |
| `ExactCorpus` | Python `fractions` | determinant signs |
| `LoopRelationCorpus` | `s2loop_test.cc` | containment, disjointness and covering of two loops |
| `PolygonCorpus` | `s2polygon_test.cc` | containment and intersection of polygons, nesting, point containment |
| `ClippingCorpus` | upstream C++ | the faces an edge crosses, clipping to padded faces and to rectangles |
| `CodingCorpus` | upstream C++ | the bytes of `encode`, and `decode` of upstream's bytes |

[s2sphere](https://github.com/sidewalklabs/s2sphere) is an independent Python
port of the same library. It ports an older coverer, so `CoverCorpus` comes
from upstream. "Upstream C++" is `tools/s2_oracle.cc` built against
s2geometry v0.14.0. The tables from upstream's tests are full of the
degenerate cases that containment predicates get wrong.

The two upstream tables state a relation between two shapes, not a list of
answers. So `S2LoopRelationTest` derives the answers that each relation
implies, as upstream's own test does, and checks every pair against both loops
and their complements. Upstream also checks its polygon relations against
complements, but that needs boolean operations. So `S2PolygonTest` checks only
the three relations.

s2sphere has no `S2Loop` or `S2Polyline`. So `S2ShapeTest` checks them against
cell geometry: a loop through the four vertices of a cell has exactly the area
of the cell, and a polyline around the cell is exactly as long as its four
edges.

The inline tests of many functions quote the output of `s2_oracle`, so their
expected values also come from upstream. The comment at the top of
`tools/s2_oracle.cc` lists the queries it answers.

### Regenerating the corpora

```
pip install s2sphere
python3 tools/generate_corpus.py --oracle path/to/s2_oracle

curl -sSLO https://raw.githubusercontent.com/google/s2geometry/v0.14.0/src/s2/s2loop_test.cc
curl -sSLO https://raw.githubusercontent.com/google/s2geometry/v0.14.0/src/s2/s2polygon_test.cc
python3 tools/generate_loop_corpus.py s2loop_test.cc
python3 tools/generate_polygon_corpus.py s2polygon_test.cc

python3 tools/generate_coding_corpus.py path/to/s2_oracle > tests/CodingCorpus.roc
python3 tools/generate_clipping_corpus.py path/to/s2_oracle > tests/ClippingCorpus.roc

roc fmt tests
```

`s2_oracle` is `tools/s2_oracle.cc`, compiled and linked against s2geometry
v0.14.0 and abseil-cpp 20250814.1. Without `--oracle`, `generate_corpus.py`
does not write `CoverCorpus`. With `--only cover`, it writes only
`CoverCorpus` and does not need s2sphere.

Build the oracle against libc++. Upstream keeps the coverer candidates in a
`std::priority_queue`, and the standard library decides the order of two
candidates with the same priority. That order can change which cells fit in
the budget. The port follows the heap of libc++, so a libstdc++ build can give
a different covering.

When a change touches `tools/` or a corpus, the `Corpora` workflow regenerates
the corpora from s2sphere and from upstream's test files. It fails if they
differ from the committed files. It does not regenerate `CoverCorpus`,
`CodingCorpus` or `ClippingCorpus`, because their oracle needs a C++ build of
upstream.

### The nightly compiler

`.roc-version` names the nightly that CI installs. It is a pin and not a
minimum: a different nightly can reject code that this one accepts.

Each Monday the `Update Roc` workflow tests the newest nightly. If the tests
pass, it opens a pull request that changes `.roc-version`. If a nightly breaks
the package, fix the code in that pull request.

### Releasing

Run the `Release` workflow by hand with a semver version such as `0.1.0`, with
no `v`. The workflow:

1. runs the checks,
2. compares the public API with the previous release (`roc bump`),
3. bundles `src/main.roc` and tests the bundle on all five runners,
4. publishes the release with the bundle and its docs,
5. deploys the docs to GitHub Pages and tests the published URL,
6. opens a pull request that puts the new URL in this README.

On a pull request the same workflow does a dry run.

## Licence

The package is [UPL-1.0](LICENSE), the licence of the Roc compiler. You can
use, change and redistribute it without restriction, if you keep the copyright
line and a reference to the UPL.

This repository copies no upstream source file. But the algorithms, the
constants, the lookup tables and the shape of the API follow
[google/s2geometry](https://github.com/google/s2geometry) v0.14.0, which is
Apache-2.0. Apache-2.0 lets a changed work have its own licence if the work
keeps upstream's notices. `NOTICE` keeps them, and `src/main.roc` repeats them
so that each release bundle has them.

| Files | Licence |
| --- | --- |
| `src/`, `examples/`, `scripts/`, `tools/`, and all other files in `tests/` | UPL-1.0, in `LICENSE` |
| `tests/LoopRelationCorpus.roc`, `tests/PolygonCorpus.roc` | Apache-2.0, in `LICENSES/Apache-2.0.txt` |

Those two corpora contain data from upstream's `s2loop_test.cc` and
`s2polygon_test.cc`. The release bundle does not contain them. The other
corpora are numbers that this project generated with
[s2sphere](https://github.com/sidewalklabs/s2sphere) (MIT), with
upstream's C++ through `tools/s2_oracle.cc`, and with Python's `fractions`
module. The repository contains no code from s2sphere or upstream. You need
them only to regenerate the corpora, not to build or test the package.

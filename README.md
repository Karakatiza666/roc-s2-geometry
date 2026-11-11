# roc-s2-geometry

A port of Google's [S2 Geometry Library](https://s2geometry.io) to Roc.

S2 represents geometry on the *sphere* rather than on a projected plane, so
there is no distortion, no seam at the antimeridian, and no special case at the
poles. Its central idea is a hierarchical decomposition of the sphere into
cells, each named by a 64-bit `S2CellId`, ordered so that cells near each other
in space are usually near each other in the ordering. That turns spatial
questions into range queries an ordinary database index can answer.

The example below assumes the package is in the app header under the
shorthand `pkg`; inside this repository the same code runs unqualified.

```roc
import pkg.S2Cap
import pkg.S2CellId
import pkg.S2Earth
import pkg.S2LatLng
import pkg.S2RegionCoverer

# The level-13 cell containing a point, as a token you could store in a row.
token =
    S2CellId.from_lat_lng(S2LatLng.from_degrees(37.7749, -122.4194))
        .parent_at_level(13)
        .to_token()

# Cells covering everything within 2 km of that point.
around =
    S2Cap.from_center_angle(
        S2LatLng.from_degrees(37.7749, -122.4194).to_point(),
        S2Earth.from_km(2.0),
    )

covering =
    S2RegionCoverer.default()
        .with_max_cells(16)
        .with_max_level(16)
        .covering(around)
```

## Using it

Name the package in an app header by its release URL:

```roc
app [main!] {
    pkg: "https://github.com/Karakatiza666/roc-s2-geometry/releases/download/<version>/<hash>.tar.zst",
}
```

Each release puts the exact URL in its release notes and in this README.
Inside a checkout, `pkg: "../roc-s2-geometry/src/main.roc"` works too.
[The API docs](https://karakatiza666.github.io/roc-s2-geometry/) are those of
the latest stable release.

`examples/covering.roc` is a complete program rather than a snippet. It needs
no platform, and CI runs it on every push, so it cannot go stale:

```
$ roc examples/covering.roc -- 37.7749 -122.4194 2 12
leaf 8085809e8e8d8c61
cell 8085807c at level 13
cell 8085809 at level 12
...
```

With no arguments it covers the same 2 km around San Francisco.

## What is here

| Module | What it is |
| --- | --- |
| `S1Angle` | A one-dimensional angle, the unit every distance is measured in |
| `S1ChordAngle` | The same angle as a squared chord length, so comparisons need no trigonometry |
| `S1Interval` | A closed interval on the circle, which may wrap through +/-pi |
| `R1Interval` | A closed interval on the real line |
| `R2Point` `R2Rect` | A point and an axis-aligned rectangle in the plane, used for cube-face coordinates |
| `S2Point` | A vector in three dimensions, plus triangle area and centroid |
| `S2LatLng` | A position in latitude and longitude |
| `S2Coords` | The cube-face projection: `xyz` to `uv` to `st` to `ij` |
| `S2Metric` | How cell edges, diagonals, widths and areas scale with level |
| `S2CellId` | A cell's 64-bit identity, and everything derived from it |
| `S2Cell` | A cell's geometry: vertices, edges, area, containment |
| `S2CellUnion` | A normalized set of cells, with union, intersection and difference |
| `S2Cap` | A disc on the sphere |
| `S2LatLngRect` | A rectangle in latitude-longitude space |
| `S2RegionCoverer` | Approximates any region by a set of cells |
| `S2Loop` `S2Polyline` | A simple closed polygon and an open chain of edges |
| `S2Polygon` | Loops nested into a region with holes, and the predicates between two of them |
| `S2Edge` | Edge crossings, intersections, interpolation and distances |
| `S2Predicates` | Orientation tests that are exact rather than merely careful |
| `S2Earth` | The one place that fixes a radius, converting angles to metres |

Deliberately not ported: `S2ShapeIndex`, and the *constructive* boolean
operations built on it. Those build new geometry out of old, as
`S2BooleanOperation` does when it returns the polygon where two others overlap,
and they carry the machinery upstream needs to snap and rebuild the result.

Asking whether one region contains or meets another is a different question,
and it is answered here: `S2Loop.contains`, `S2Loop.intersects`,
`S2Polygon.contains_polygon` and `S2Polygon.intersects_polygon`, along with the
containment already on `S2Cap`, `S2LatLngRect` and `S2CellUnion`. Upstream
routes those through its index for speed; without one they cost the product of
the two vertex counts, and the answers are the same.

`src/Internal/` holds `S2Boundary`, `S2Exact`, `S2Lookup` and `S2Math`.
`main.roc` does not expose them: they are the port's own machinery, and no
consumer names them.

| Path | What it is |
| --- | --- |
| `src/main.roc` | The public entry point. A release bundles it and the modules it reaches |
| `src/Internal/` | Hidden modules |
| `tests/main.roc` | The test entry point. It imports `src/` as `s2` and adds the corpus sweeps |
| `tests/` | The golden corpora and the modules that sweep them |
| `examples/` | Complete programs that use the package as an app would |
| `tools/` | The Python generators that write those corpora |
| `scripts/all_tests.sh` | Format check, type check, tests, examples and docs |
| `scripts/bundle.sh` | Writes the release bundle to `dist/` and lists its files |
| `scripts/test_bundle.sh` | Runs the examples against a bundle file or a release URL |
| `.roc-version` | The compiler nightly this is developed against, and the one CI installs |

## Two things that differ from upstream

**A cell's bounds are constructors on the bounding type.** Roc modules cannot
import each other in a cycle, and `S2Cell`, `S2Cap` and `S2LatLngRect` would
otherwise form one. So instead of `cell.rect_bound()` and `cell.cap_bound()`,
write `S2LatLngRect.from_cell(cell)` and `S2Cap.from_cell(cell)`. Every other
bound is a method where you would expect it.

**A region is any type with three methods.** Upstream has an `S2Region` base
class; here `S2RegionCoverer` is generic over any type providing `cap_bound`,
`contains_cell` and `may_intersect_cell`:

```roc
covering : S2RegionCoverer, r -> List(S2CellId)
    where [
        r.cap_bound : r -> S2Cap,
        r.contains_cell : r, S2Cell -> Bool,
        r.may_intersect_cell : r, S2Cell -> Bool,
    ]
```

`S2Cap`, `S2LatLngRect`, `S2CellUnion`, `S2Loop`, `S2Polyline` and `S2Polygon`
all satisfy it, and so can a type of your own.

The coverer starts from a few cells that cover the region's cap bound.
Upstream does the same for every region except `S2Polygon`, which it bounds
by the cells of its spatial index. This port has no such index, so a covering
of a polygon can differ from upstream's.

## Exactness

Orientation is the predicate everything else rests on: given three points, is
the third to the left or the right of the line through the first two? Floating
point cannot answer it for nearly collinear points, and an implementation that
guesses produces contradictory answers that break the algorithms above it.

`S2Predicates.sign` therefore escalates. A rounded determinant decides the
common case. When its error bound says the answer is uncertain, a second
formulation built from edge vectors decides almost everything else. When even
that is uncertain, the determinant is evaluated *exactly*, using Shewchuk's
floating-point expansions, which represent a sum of products of doubles as a
list of non-overlapping doubles and lose nothing at any step. That arithmetic
lives in the package's internal `S2Exact`.
Points that are exactly collinear are resolved by a symbolic perturbation, so
the answer is never zero and never inconsistent. The exact arithmetic has one
limit: the error term of a product of two doubles is exact only while it does
not underflow, so a product with a magnitude below about 1e-290 can lose bits
or become zero.

The costs of that fidelity are documented where they apply. `S2Point.robust_cross`
uses the long-standing stable formulation rather than upstream's current
exact-arithmetic one, so the direction it picks for exactly proportional inputs
is arbitrary rather than canonical. `S2Edge.intersection` is accurate to about
1e-15 radians for edges meeting at a healthy angle and degrades as that angle
shrinks. `S2Loop` and `S2Polygon` have no spatial index, so their
cell tests are linear in the vertex count, and `is_valid` and the predicates
between two shapes are quadratic.

## Tests

```
scripts/all_tests.sh
scripts/bundle.sh && scripts/test_bundle.sh
```

The first script checks the format, type-checks both entry points, runs the
tests and the examples, and generates the docs. The second line bundles the
package and runs the examples against that bundle, served on localhost.
GitHub Actions runs both on Linux x64 and arm64, macOS on Apple silicon and
Intel, and Windows, against the pinned nightly. When a change touches `tools/`
or a corpus, the `Corpora` workflow also regenerates the corpora from s2sphere
and from upstream's test files, and fails if they differ from the committed
ones. It does not regenerate `CoverCorpus`, because its oracle needs a C++
build of upstream.

There are 777 assertions. `roc test src/main.roc` runs the 666 unit tests
written alongside the modules they cover. `roc test tests/main.roc` runs the
111 corpus sweeps, each of which walks every case in one golden corpus. It
also runs the unit tests of every module the sweeps import, but not of a module
none of them imports, so the script runs both.

The corpora are what make this more than a self-consistency check. Four of them
come from running [s2sphere](https://github.com/sidewalklabs/s2sphere), an
independent Python port of the same C++ library, so the expected values come
from a third implementation rather than from this one. `CoverCorpus` comes from
upstream's own C++ `S2RegionCoverer` at v0.14.0. s2sphere ports an older
version of that algorithm, which gives different coverings. Two are the tables
out of upstream's own test suite, which is the reference answer for the
containment predicates and is full of the degenerate cases those predicates get
wrong:

| Corpus | Cases | Checks |
| --- | --- | --- |
| `CellIdCorpus` | 200 | ids, tokens, face/i/j/orientation, centres, ancestors, traversal, all three kinds of neighbour |
| `CellCorpus` | 150 | vertices, three area methods, rectangle and cap bounds |
| `RegionCorpus` | 120 | cap and rectangle measures, their bounds, and their predicates against cells |
| `CellUnionCorpus` | 60 | normalization, union, intersection, difference, containment |
| `CoverCorpus` | 40 | coverings and interior coverings, cell for cell and in order, from upstream's C++ through `tools/s2_oracle.cc` |
| `ExactCorpus` | 200 | determinant signs, against Python's rational arithmetic rather than another port |
| `LoopRelationCorpus` | 86 | which of two loops contains the other, whether they are disjoint, and whether they cover the sphere, from `s2loop_test.cc` |
| `PolygonCorpus` | 86 | polygon containment and intersection, nesting, and point containment, from `s2polygon_test.cc` |

`S2Loop` and `S2Polyline` have no counterpart in s2sphere, so `S2ShapeTest`
pins their measurements to cell geometry instead: a loop through a cell's four
vertices must enclose exactly the cell's area, and a polyline around its
boundary must be exactly as long as its four edges.

The two upstream tables state a relation, not a list of answers, so
`S2LoopRelationTest` re-derives what each one implies the way upstream's own
harness does, and checks every pair against both loops and their complements.
That is how 86 stated relations become several hundred assertions. Upstream
checks its polygon relations against complements too, which needs the boolean
operations this port leaves out, so `S2PolygonTest` checks the three relations
themselves.

To regenerate:

```
pip install s2sphere
python3 tools/generate_corpus.py --oracle path/to/s2_oracle

curl -sSLO https://raw.githubusercontent.com/google/s2geometry/v0.14.0/src/s2/s2loop_test.cc
curl -sSLO https://raw.githubusercontent.com/google/s2geometry/v0.14.0/src/s2/s2polygon_test.cc
python3 tools/generate_loop_corpus.py s2loop_test.cc
python3 tools/generate_polygon_corpus.py s2polygon_test.cc

roc fmt tests
```

`s2_oracle` is `tools/s2_oracle.cc` compiled and linked against
s2geometry v0.14.0 and the abseil-cpp it builds with (20250814.1 works). The
generator gives it the cases and reads back the coverings. Without
`--oracle`, the generator does not write `CoverCorpus`. With
`--only cover`, it writes only `CoverCorpus` and does not need s2sphere.

The same program also answers single queries, one per input line: the
trigonometry of `S1Angle`, the face and `(u, v, w)` conversions of `S2Coords`,
centroids, cell bounds and ranges, and more. The comment at the top of
`tools/s2_oracle.cc` lists them. The inline tests of those functions quote its
output, so their expected values come from upstream and not from this port.

Upstream keeps the candidates in a `std::priority_queue`. Two candidates with
the same priority leave it in an order that the C++ standard library decides,
and that order can change which cells the budget allows. The port follows the
heap of libc++, and the corpus was generated with libc++. A build of the
oracle against libstdc++ can give a different covering for such a tie.

### Working with the nightly compiler

`.roc-version` names the nightly this is developed against, and CI installs
exactly that build. It is a pin rather than a floor: the compiler is a moving
target, and a different nightly may reject code this one accepts.

Each Monday the `Update Roc` workflow tests the newest nightly. When the tests
pass, it opens a pull request that changes `.roc-version`. When a nightly
breaks the package, fix the code in that pull request.

### Releasing

Run the `Release` workflow by hand with a version such as `0.1.0` (semver, no
`v`). It runs the checks, compares the public API with the previous release
(`roc bump`), bundles `src/main.roc`, and tests the bundle on all five runners.
Then it publishes the release with the bundle and its docs, deploys the docs to
GitHub Pages, tests the published URL, and opens a pull request that puts the
new URL in this README. On a pull request the same workflow runs as a dry run.

## Licence

The package is [UPL-1.0](LICENSE), the licence the Roc compiler uses. You may
use, change and redistribute it without restriction. Keep the copyright line
and a reference to the UPL.

No upstream source file is copied here. But this is a port: the algorithms,
the constants, the lookup tables and the shape of the API follow
[google/s2geometry](https://github.com/google/s2geometry) at tag v0.14.0,
which is Apache-2.0. Apache-2.0 lets a changed work carry a licence of its
own, if it keeps upstream's notices. `NOTICE` keeps them, and
`src/main.roc` repeats them so that every release bundle carries them.

| Files | Licence |
| --- | --- |
| `src/`, `examples/`, `scripts/`, `tools/`, every other file in `tests/` | UPL-1.0, in `LICENSE` |
| `tests/LoopRelationCorpus.roc`, `tests/PolygonCorpus.roc` | Apache-2.0, in `LICENSES/Apache-2.0.txt` |

Those two corpora hold data extracted from upstream's `s2loop_test.cc` and
`s2polygon_test.cc`, and they are not in the release bundle. The other
corpora are numbers this project generated by running
[s2sphere](https://github.com/sidewalklabs/s2sphere) (MIT), by running
upstream's C++ region coverer through `tools/s2_oracle.cc`, and by
evaluating determinants with Python's `fractions` module. Neither s2sphere nor
upstream's source is bundled. You need them only to regenerate the corpora,
never to build or test.

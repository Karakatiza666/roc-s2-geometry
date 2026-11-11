// SPDX-FileCopyrightText: 2026 Heorhii Bulakh
// SPDX-License-Identifier: UPL-1.0
//
// Answers questions about google/s2geometry v0.14.0, one input line per
// query and one output line per answer, so that the Roc port can take its
// expected values from upstream rather than from itself. The generator
// tools/generate_corpus.py runs it to write tests/CoverCorpus.roc, and the
// inline tests of the other modules quote its output.
//
// Build it against google/s2geometry v0.14.0 and the abseil it was built
// with, then give it the queries on standard input. Numbers are read with
// strtod, so "0x1.8p3", "inf" and "nan" are all fine. Doubles are printed
// with %.17g, which round-trips. A cell id is an unsigned decimal integer.
//
// Coverings:
//
//   cap X Y Z DEGREES                 MAX_CELLS MIN_LEVEL MAX_LEVEL LEVEL_MOD
//   capll LAT LNG DEGREES             MAX_CELLS MIN_LEVEL MAX_LEVEL LEVEL_MOD
//   rect LAT1 LNG1 LAT2 LNG2          MAX_CELLS MIN_LEVEL MAX_LEVEL LEVEL_MOD
//   cells N ID_1 ... ID_N             MAX_CELLS MIN_LEVEL MAX_LEVEL LEVEL_MOD
//   wrap
//
// "cap" is S2Cap(S2Point(X, Y, Z), S1Angle::Degrees(DEGREES)). "capll" puts
// the centre at S2LatLng::FromDegrees(LAT, LNG). "rect" is
// S2LatLngRect::FromPointPair of two S2LatLng::FromDegrees points. "cells" is
// the normalized S2CellUnion of the given ids. For each region the answer is
// the covering, a "|", and the interior covering, as decimal cell ids in the
// order upstream returns them.
//
// "wrap" prints the token of S2CellId::FromFaceIJWrap(0, -1, 1073741823).
// That function is private, so the driver reaches it through the left edge
// neighbour of the leaf at face 0, i = 0, j = 1073741823, which upstream
// computes as FromFaceIJSame(0, -1, j, false).parent(30).
//
// Scalar functions (A, B, C are points written as three numbers, or in one
// of the two forms that "Point" below describes):
//
//   angle_trig RADIANS                sin cos tan of S1Angle, then SinCos()
//   angle_unsigned e6|e7 U            radians of S1Angle::UnsignedE6/E7(U)
//   angle_points A B                  radians of S1Angle(S2Point, S2Point)
//   chord radians|degrees R           length2 s1_max_error point_max_error
//   chord e5|e6|e7 N                  e5 e6 e7 (of the same chord)
//   chord_fast RADIANS                length2 of FastUpperBoundFrom
//   earth_lng meters|km D LAT_RAD     MetersToLongitudeRadians, KmTo...
//   earth_bearing LAT1 LNG1 LAT2 LNG2 radians (in radians)
//   point2 mul|div|min|max A B        the vector
//   point1 sqrt|floor|ceil|refdir A   the vector
//   coords_uvw FACE A                 FaceXYZtoUVW
//   coords_axis FACE AXIS             GetUVWAxis
//   coords_face FACE AXIS DIRECTION   GetUVWFace
//   coords_si_ti_xyz FACE SI TI       FaceSiTitoXYZ
//   coords_ij_st_min I                IJtoSTMin
//   coords_xyz_si_ti A                face si ti level of XYZtoFaceSiTi
//   aspect                            kMaxEdgeAspect kMaxDiagAspect
//   measure_angle A B C               S2::Angle
//   measure_turn A B C                S2::TurnAngle
//   centroid_planar A B C             S2::PlanarCentroid
//   centroid_true A B C               S2::TrueCentroid of a triangle
//   centroid_edge A B                 S2::TrueCentroid of an edge
//   cap_centroid A DEGREES            S2Cap::GetCentroid
//   latlng_string LAT_RAD LNG_RAD     ToStringInDegrees
//   latlng_unsigned e6|e7 LAT LNG     lat and lng radians of FromUnsignedE6/E7
//
// Cells and cell unions:
//
//   cell_center_st ID                 s t
//   cell_bound_st ID                  s_lo s_hi t_lo t_hi
//   cell_distance_from_begin ID       an integer
//   cell_ij_bound I J LEVEL           u_lo u_hi v_lo v_hi of IJLevelToBoundUV
//   cell_expand U_LO U_HI V_LO V_HI RADIANS   ExpandedByDistanceUV
//   cell_max_tile ID LIMIT            an id
//   cell_from_pos FACE POS LEVEL      FromFacePosLevel
//   cell_child_begin ID LEVEL         child_begin(LEVEL) then child_end(LEVEL)
//   cell_lsb_level LEVEL              lsb_for_level
//   cell_ancestor A B                 GetCommonAncestorLevel (-1 for none)
//   cell_si_ti ID                     face si ti of GetCenterSiTi
//   cell_point_raw ID                 ToPointRaw
//   union_min_max MIN MAX             FromMinMax
//   union_begin_end BEGIN END         FromBeginEnd
//   union_verbatim N ID_1 ... ID_N    FromVerbatim, then IsValid IsNormalized
//
// The last three print the ids of the union.
//
// Edges and predicates (L is a squared chord length, R radians, booleans
// print as 0 or 1):
//
//   edge_distance X A B               GetDistance, then the S1ChordAngle
//                                     length2 that AlwaysUpdateMinDistance gives
//   edge_update L min|max|interior X A B   flag and length2 after the update
//   edge_less X A B L                 IsDistanceLess IsInteriorDistanceLess
//   edge_min_error L                  GetUpdateMinDistanceMaxError
//   edge_fraction X A B               GetDistanceFraction
//   edge_project X A B                Project (also Project with a_cross_b
//                                     = RobustCrossProd(A, B), as 6 numbers)
//   edge_point line|left|right|ray A B R    the S1Angle and S1ChordAngle(R)
//                                     forms, as 6 numbers
//   edge_interpolate A B T            Interpolate
//   edge_pair min|max L A0 A1 B0 B1   flag and length2 after the update
//   edge_pair_less A0 A1 B0 B1 L      IsEdgePairDistanceLess
//   edge_pair_closest A0 A1 B0 B1     GetEdgePairClosestPoints, 6 numbers
//   edge_near A0 A1 B0 B1 R           IsEdgeBNearEdgeA
//   edge_cross A B C D                CrossingSign VertexCrossing
//                                     SignedVertexCrossing EdgeOrVertexCrossing
//                                     (the vertex ones only when two of the
//                                     points are equal, else 9)
//   edge_intersection A0 A1 B0 B1     GetIntersection, then the method it
//                                     used (2 stable, 4 exact)
//   crosser A B C N D_1 ... D_N       per D: CrossingSign EdgeOrVertexCrossing
//                                     SignedEdgeOrVertexCrossing
//                                     last_interior_crossing_sign, each from its
//                                     own S2EdgeCrosser walking the chain
//   pred_distances X A B              CompareDistances
//   pred_distance X Y L               CompareDistance
//   pred_dot A B                      SignDotProd
//   pred_edge_distance X A0 A1 L      CompareEdgeDistance
//   pred_edge_pair A0 A1 B0 B1 L      CompareEdgePairDistance
//   pred_directions A0 A1 B0 B1       CompareEdgeDirections
//
// Padded cells, cell distances, rectangles and the rectangle bounder (a
// rectangle RECT is LAT_LO LAT_HI LNG_LO LNG_HI in radians, passed to the
// R1Interval and S1Interval constructors):
//
//   padded ID PAD                     id level bound middle center entry exit
//   padded_child ID PAD I J           the same for S2PaddedCell(parent, I, J)
//   padded_child_ij ID PAD            GetChildIJ for pos 0..3, 8 integers
//   padded_shrink ID PAD U0 U1 V0 V1  ShrinkToFit
//   cell_dist_point ID P              GetDistance GetBoundaryDistance
//                                     GetMaxDistance, as length2
//   cell_dist_edge ID A B             GetDistance(A, B) GetMaxDistance(A, B)
//   cell_dist_cell ID1 ID2 L          GetDistance GetMaxDistance, then
//                                     IsDistanceLess IsDistanceLessOrEqual
//                                     IsMaxDistanceLess IsMaxDistanceLessOrEqual
//   rect_centroid RECT                GetCentroid
//   rect_boundary RECT V0 V1          BoundaryIntersects
//   rect_expand RECT R                ExpandedByDistance, as a RECT
//   rect_distance RECT RECT           GetDistance GetDirectedHausdorffDistance
//                                     GetHausdorffDistance, in radians
//   rect_distance_ll RECT LAT LNG     GetDistance(S2LatLng::FromRadians)
//   bounder N P_1 ... P_N             GetBound after AddPoint of each point
//   bounder_ll N LAT_1 LNG_1 ...      GetBound after AddLatLng (radians)
//   bounder_sub RECT                  ExpandForSubregions
//   bounder_error                     MaxErrorForTests, lat and lng radians
//
// Loops, polylines, polygons and the convex hull. A chain CHAIN is a count
// N and then N points. A polygon POLY is a loop count and then that many
// chains, given to the S2Polygon constructor (InitNested). Every shape is
// built with S2Debug::DISABLE, so invalid ones can be asked about. An error
// prints as its S2Error code number, then its message.
//
//   loop_info CHAIN                   error code or "ok", GetArea
//                                     S2::GetApproxArea S2::GetPerimeter
//                                     GetCurvature GetCurvatureMaxError
//                                     IsNormalized, "|", error message
//   loop_dist X CHAIN                 GetDistance GetDistanceToBoundary
//                                     (radians), Project ProjectToBoundary
//   loop_regular C RADIUS_DEG N       vertices of MakeRegularLoop
//   loop_cell ID                      vertices of S2Loop(S2Cell), then the
//                                     loop's GetRectBound as a RECT
//   loop_near R CHAIN CHAIN           BoundaryApproxEquals BoundaryNear
//   cub cap X DEG | rect RECT | cell ID | loop CHAIN | line CHAIN |
//       point X | poly POLY | union N ID_1 ... ID_N
//                                     GetCellUnionBound of the region
//   pl_valid CHAIN                    error
//   pl_snap CHAIN                     GetSnapLevel
//   pl_suffix F CHAIN                 GetSuffix point, then next_vertex
//   pl_unint X NEXT CHAIN             UnInterpolate
//   pl_project X CHAIN                Project point, then next_vertex
//   pl_right X CHAIN                  IsOnRight
//   pl_subsample R CHAIN              SubsampleVertices indices
//   pl_covers R CHAIN CHAIN           a.NearlyCovers(b) b.NearlyCovers(a)
//   pg_dist X POLY                    as loop_dist
//   pg_info POLY                      num_vertices GetSnapLevel IsNormalized,
//                                     then per loop: depth GetParent
//                                     GetLastDescendant
//   pg_invert POLY                    the inverted polygon: per loop its
//                                     depth and vertex count, then all
//                                     vertices in order
//   pg_near R POLY POLY               BoundaryEquals BoundaryApproxEquals
//                                     BoundaryNear
//   hull ITEM ...                     vertices of GetConvexHull, or "empty"
//                                     or "full". An ITEM is "p X",
//                                     "line CHAIN", "loop CHAIN" or
//                                     "poly POLY".
//
// Number formatting, text format, projections, tessellation, term indexing and
// region unions. TEXT is the rest of the line.
//
//   fmt_g PRECISION X                 printf("%.*g", PRECISION, X)
//   libm exp|log X                    the C library's exp or log
//   atod TEXT                         absl::SimpleAtod of the rest of the
//                                     line: the double, or "err"
//   tf_parse KIND TEXT                KIND is point, latlng, latlngs, points,
//                                     rect, cell, union, loop, line, polygon
//                                     or verbatim. Prints "ok", the result,
//                                     "|" and ToString of it, or "err" and
//                                     the message. A polygon's ToString has
//                                     its newlines written as \n.
//   tf_tostr KIND ...                 point X | latlng LAT RAD | rect RECT |
//                                     cell ID | union N ID_1 ... | loop CHAIN
//                                     | line CHAIN | poly POLY | points CHAIN
//                                     | polysep SEP POLY (SEP without spaces)
//   proj pc|merc SCALE OP ...         project P | unproject X Y |
//                                     from_ll LAT LNG | to_ll X Y |
//                                     interpolate F AX AY BX BY | wrap |
//                                     wrap_dest AX AY BX BY
//   tess_min                          kMinTolerance in radians
//   tess_proj pc|merc SCALE TOL N P_1 ... P_N     (TOL is RADIANS, deg:X or e7:N)
//                                     AppendProjected over the chain
//   tess_unproj pc|merc SCALE TOL N X_1 Y_1 ... X_N Y_N
//                                     AppendUnprojected over the chain
//   term_index MIN MAX MOD CELLS POINTS_ONLY SPACE MARKER PREFIX WHAT
//                                     MARKER is a character code and PREFIX
//                                     is "-" for none. WHAT is point P |
//                                     region SPEC | cells N ID_1 .... Prints
//                                     the index terms, "|", the query terms.
//   region_op union|inter N SPEC_1 ... SPEC_N QUERY
//                                     A SPEC is cap P DEG | rect RECT |
//                                     cell ID | point P | loop CHAIN |
//                                     line CHAIN | poly POLY | union N ID_1 ... |
//                                     ru N SPEC... | ri N SPEC.... QUERY is
//                                     CELLS N ID_1 ... POINTS M P_1 ...
//                                     MAX_CELLS MIN MAX MOD. Prints the
//                                     rectangle bound, cap bound, cell union
//                                     bound, then per cell Contains and
//                                     MayIntersect, per point Contains, then
//                                     the covering and interior covering.

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "s2/r2rect.h"
#include "s2/s1angle.h"
#include "s2/s1chord_angle.h"
#include "s2/s2cap.h"
#include "s2/s2cell_id.h"
#include "s2/s2cell_union.h"
#include "s2/s2centroids.h"
#include "s2/s2convex_hull_query.h"
#include "s2/s2coords.h"
#include "s2/s2earth.h"
#include "s2/s2edge_crosser.h"
#include "s2/s2edge_crossings.h"
#include "s2/s2edge_crossings_internal.h"
#include "s2/s2edge_distances.h"
#include "s2/s2cell.h"
#include "s2/s2error.h"
#include "s2/s2latlng.h"
#include "s2/s2latlng_rect.h"
#include "s2/s2latlng_rect_bounder.h"
#include "s2/s2loop.h"
#include "s2/s2loop_measures.h"
#include "s2/s2padded_cell.h"
#include "s2/s2predicates.h"
#include "s2/s2measures.h"
#include "s2/s2metrics.h"
#include "s2/s2point.h"
#include "s2/s2point_region.h"
#include "s2/s2polygon.h"
#include "s2/s2polyline.h"
#include "s2/s2pointutil.h"
#include "s2/s2region.h"
#include "s2/s2region_coverer.h"
#include "s2/s2edge_tessellator.h"
#include "s2/s2projections.h"
#include "s2/s2region_intersection.h"
#include "s2/s2region_term_indexer.h"
#include "s2/s2region_union.h"
#include "s2/s2text_format.h"
#include "absl/strings/numbers.h"

namespace {

void PrintIds(const std::vector<S2CellId>& ids) {
  for (size_t i = 0; i < ids.size(); ++i) {
    std::printf("%s%llu", i == 0 ? "" : " ",
                static_cast<unsigned long long>(ids[i].id()));
  }
}

void Cover(const S2Region& region, std::istringstream& in) {
  int max_cells, min_level, max_level, level_mod;
  in >> max_cells >> min_level >> max_level >> level_mod;
  S2RegionCoverer::Options options;
  options.set_max_cells(max_cells);
  options.set_min_level(min_level);
  options.set_max_level(max_level);
  options.set_level_mod(level_mod);
  S2RegionCoverer coverer(options);
  std::vector<S2CellId> covering, interior;
  coverer.GetCovering(region, &covering);
  coverer.GetInteriorCovering(region, &interior);
  PrintIds(covering);
  std::printf(" | ");
  PrintIds(interior);
  std::printf("\n");
}

double Number(std::istringstream& in) {
  std::string text;
  in >> text;
  return std::strtod(text.c_str(), nullptr);
}

// A point is three numbers. "N X Y Z" is S2Point(X, Y, Z).Normalize(), and
// "L LAT LNG" is S2LatLng::FromDegrees(LAT, LNG).ToPoint().
S2Point Point(std::istringstream& in) {
  std::string text;
  in >> text;
  if (text == "N") {
    double x = Number(in), y = Number(in), z = Number(in);
    return S2Point(x, y, z).Normalize();
  }
  if (text == "L") {
    double lat = Number(in), lng = Number(in);
    return S2LatLng::FromDegrees(lat, lng).ToPoint();
  }
  double x = std::strtod(text.c_str(), nullptr);
  double y = Number(in), z = Number(in);
  return S2Point(x, y, z);
}

S2CellId Id(std::istringstream& in) {
  unsigned long long id;
  in >> id;
  return S2CellId(id);
}

// Prints doubles separated by single spaces, ended by a newline.
void Print(std::initializer_list<double> values) {
  const char* separator = "";
  for (double value : values) {
    std::printf("%s%.17g", separator, value);
    separator = " ";
  }
  std::printf("\n");
}

void PrintPoint(const S2Point& p) { Print({p.x(), p.y(), p.z()}); }

void PrintRect(const R2Rect& r) {
  Print({r[0][0], r[0][1], r[1][0], r[1][1]});
}

void PrintUnion(const S2CellUnion& u) {
  PrintIds(u.cell_ids());
  std::printf("\n");
}

int Fail(const std::string& kind) {
  std::fprintf(stderr, "unknown case: %s\n", kind.c_str());
  return 1;
}


S2LatLngRect Rect(std::istringstream& in) {
  double a = Number(in), b = Number(in), c = Number(in), d = Number(in);
  return S2LatLngRect(R1Interval(a, b), S1Interval(c, d));
}

void PrintLatLngRect(const S2LatLngRect& r) {
  Print({r.lat().lo(), r.lat().hi(), r.lng().lo(), r.lng().hi()});
}

void PrintPadded(const S2PaddedCell& p) {
  std::printf("%llu %d ", static_cast<unsigned long long>(p.id().id()),
              p.level());
  const R2Rect& b = p.bound();
  const R2Rect& m = p.middle();
  S2Point c = p.GetCenter(), e = p.GetEntryVertex(), x = p.GetExitVertex();
  Print({b[0][0], b[0][1], b[1][0], b[1][1], m[0][0], m[0][1], m[1][0],
         m[1][1], c.x(), c.y(), c.z(), e.x(), e.y(), e.z(), x.x(), x.y(),
         x.z()});
}

std::vector<S2Point> Chain(std::istringstream& in) {
  int n;
  in >> n;
  std::vector<S2Point> points;
  for (int i = 0; i < n; ++i) points.push_back(Point(in));
  return points;
}

std::unique_ptr<S2Polygon> Polygon(std::istringstream& in) {
  int n;
  in >> n;
  std::vector<std::unique_ptr<S2Loop>> loops;
  for (int i = 0; i < n; ++i) {
    loops.push_back(std::make_unique<S2Loop>(Chain(in), S2Debug::DISABLE));
  }
  return std::make_unique<S2Polygon>(std::move(loops), S2Debug::DISABLE);
}

void PrintError(bool failed, const S2Error& error) {
  if (failed) {
    std::printf("%d %s\n", static_cast<int>(error.code()),
                std::string(error.message()).c_str());
  } else {
    std::printf("ok\n");
  }
}

void PrintPoints(const std::vector<S2Point>& points) {
  const char* separator = "";
  for (const S2Point& p : points) {
    std::printf("%s%.17g %.17g %.17g", separator, p.x(), p.y(), p.z());
    separator = " ";
  }
  std::printf("\n");
}

void PrintLoopVertices(const S2Loop& loop) {
  std::vector<S2Point> points;
  for (int i = 0; i < loop.num_vertices(); ++i) points.push_back(loop.vertex(i));
  PrintPoints(points);
}

void PrintCellIds(const std::vector<S2CellId>& ids) {
  PrintIds(ids);
  std::printf("\n");
}


std::string Rest(std::istringstream& in) {
  std::string text;
  std::getline(in, text);
  if (!text.empty() && text[0] == ' ') text.erase(0, 1);
  return text;
}

std::unique_ptr<S2Region> Spec(std::istringstream& in);

std::vector<std::unique_ptr<S2Region>> Specs(std::istringstream& in) {
  int n;
  in >> n;
  std::vector<std::unique_ptr<S2Region>> regions;
  for (int i = 0; i < n; ++i) regions.push_back(Spec(in));
  return regions;
}

std::unique_ptr<S2Region> Spec(std::istringstream& in) {
  std::string type;
  in >> type;
  if (type == "cap") {
    S2Point x = Point(in);
    return std::make_unique<S2Cap>(x, S1Angle::Degrees(Number(in)));
  } else if (type == "rect") {
    return std::make_unique<S2LatLngRect>(Rect(in));
  } else if (type == "cell") {
    return std::make_unique<S2Cell>(Id(in));
  } else if (type == "point") {
    return std::make_unique<S2PointRegion>(Point(in));
  } else if (type == "loop") {
    return std::make_unique<S2Loop>(Chain(in), S2Debug::DISABLE);
  } else if (type == "line") {
    return std::make_unique<S2Polyline>(Chain(in), S2Debug::DISABLE);
  } else if (type == "poly") {
    return Polygon(in);
  } else if (type == "union") {
    int count;
    in >> count;
    std::vector<S2CellId> cells;
    for (int i = 0; i < count; ++i) cells.push_back(Id(in));
    return std::make_unique<S2CellUnion>(std::move(cells));
  } else if (type == "ru") {
    return std::make_unique<S2RegionUnion>(Specs(in));
  } else if (type == "ri") {
    return std::make_unique<S2RegionIntersection>(Specs(in));
  }
  std::fprintf(stderr, "unknown spec: %s\n", type.c_str());
  std::exit(1);
}

void PrintStatusPoints(const std::vector<S2Point>& points) {
  std::printf("%d", static_cast<int>(points.size()));
  for (const S2Point& p : points) {
    std::printf(" %.17g %.17g %.17g", p.x(), p.y(), p.z());
  }
}

std::string EscapeNewlines(const std::string& text) {
  std::string out;
  for (char c : text) {
    if (c == '\n') out += "\\n"; else out += c;
  }
  return out;
}

void PrintPolygonStructure(const S2Polygon& polygon) {
  std::printf("%d", polygon.num_loops());
  for (int k = 0; k < polygon.num_loops(); ++k) {
    const S2Loop& loop = *polygon.loop(k);
    std::printf(" %d %d", loop.depth(), loop.num_vertices());
    for (int i = 0; i < loop.num_vertices(); ++i) {
      std::printf(" %.17g %.17g %.17g", loop.vertex(i).x(), loop.vertex(i).y(),
                  loop.vertex(i).z());
    }
  }
}

int TextFormat(const std::string& kind, std::istringstream& in) {
  if (kind == "tf_parse") {
    std::string type;
    in >> type;
    std::string text = Rest(in);
    if (type == "point") {
      auto r = s2textformat::MakePoint(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok %.17g %.17g %.17g | %s\n", r->x(), r->y(), r->z(),
                  s2textformat::ToString(*r).c_str());
    } else if (type == "latlng") {
      auto r = s2textformat::MakeLatLng(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok %.17g %.17g | %s\n", r->lat().radians(), r->lng().radians(),
                  s2textformat::ToString(*r).c_str());
    } else if (type == "latlngs") {
      auto r = s2textformat::ParseLatLngs(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok %d", static_cast<int>(r->size()));
      for (const S2LatLng& ll : *r) std::printf(" %.17g %.17g", ll.lat().radians(), ll.lng().radians());
      std::printf(" | %s\n", s2textformat::ToString(absl::Span<const S2LatLng>(*r)).c_str());
    } else if (type == "points") {
      auto r = s2textformat::ParsePoints(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok ");
      PrintStatusPoints(*r);
      std::printf(" | %s\n", s2textformat::ToString(absl::Span<const S2Point>(*r)).c_str());
    } else if (type == "rect") {
      auto r = s2textformat::MakeLatLngRect(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok %.17g %.17g %.17g %.17g | %s\n", r->lat().lo(), r->lat().hi(),
                  r->lng().lo(), r->lng().hi(), s2textformat::ToString(*r).c_str());
    } else if (type == "cell") {
      auto r = s2textformat::MakeCellId(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok %llu | %s\n", static_cast<unsigned long long>(r->id()),
                  s2textformat::ToString(*r).c_str());
    } else if (type == "union") {
      auto r = s2textformat::MakeCellUnion(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok ");
      PrintIds(r->cell_ids());
      std::printf(" | %s\n", s2textformat::ToString(*r).c_str());
    } else if (type == "loop") {
      auto r = s2textformat::MakeLoop(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::vector<S2Point> points;
      for (int i = 0; i < (*r)->num_vertices(); ++i) points.push_back((*r)->vertex(i));
      std::printf("ok ");
      PrintStatusPoints(points);
      std::printf(" | %s\n", s2textformat::ToString(**r).c_str());
    } else if (type == "line") {
      auto r = s2textformat::MakePolyline(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::vector<S2Point> points;
      for (int i = 0; i < (*r)->num_vertices(); ++i) points.push_back((*r)->vertex(i));
      std::printf("ok ");
      PrintStatusPoints(points);
      std::printf(" | %s\n", s2textformat::ToString(**r).c_str());
    } else if (type == "polygon" || type == "verbatim") {
      auto r = type == "polygon" ? s2textformat::MakePolygon(text)
                                 : s2textformat::MakeVerbatimPolygon(text);
      if (!r.ok()) { std::printf("err %s\n", std::string(r.status().message()).c_str()); return 0; }
      std::printf("ok ");
      PrintPolygonStructure(**r);
      std::printf(" | %s\n", EscapeNewlines(s2textformat::ToString(**r)).c_str());
    } else {
      return Fail(kind + " " + type);
    }
  } else if (kind == "tf_tostr") {
    std::string type;
    in >> type;
    std::string out;
    if (type == "point") {
      out = s2textformat::ToString(Point(in));
    } else if (type == "latlng") {
      double lat = Number(in), lng = Number(in);
      out = s2textformat::ToString(S2LatLng::FromRadians(lat, lng));
    } else if (type == "rect") {
      out = s2textformat::ToString(Rect(in));
    } else if (type == "cell") {
      out = s2textformat::ToString(Id(in));
    } else if (type == "union") {
      int count;
      in >> count;
      std::vector<S2CellId> ids;
      for (int i = 0; i < count; ++i) ids.push_back(Id(in));
      out = s2textformat::ToString(S2CellUnion::FromVerbatim(std::move(ids)));
    } else if (type == "loop") {
      out = s2textformat::ToString(S2Loop(Chain(in), S2Debug::DISABLE));
    } else if (type == "line") {
      out = s2textformat::ToString(S2Polyline(Chain(in), S2Debug::DISABLE));
    } else if (type == "poly") {
      out = EscapeNewlines(s2textformat::ToString(*Polygon(in)));
    } else if (type == "polysep") {
      std::string sep;
      in >> sep;
      out = s2textformat::ToString(*Polygon(in), sep);
    } else if (type == "points") {
      std::vector<S2Point> points = Chain(in);
      out = s2textformat::ToString(absl::Span<const S2Point>(points));
    } else {
      return Fail(kind + " " + type);
    }
    std::printf("%s\n", out.c_str());
  }
  return 0;
}

// A tolerance is "deg:X" for S1Angle::Degrees(X), "e7:N" for S1Angle::E7(N),
// or plain radians.
S1Angle Tolerance(std::istringstream& in) {
  std::string text;
  in >> text;
  if (text.rfind("deg:", 0) == 0) {
    return S1Angle::Degrees(std::strtod(text.c_str() + 4, nullptr));
  }
  if (text.rfind("e7:", 0) == 0) {
    return S1Angle::E7(static_cast<int32_t>(std::strtol(text.c_str() + 3, nullptr, 10)));
  }
  return S1Angle::Radians(std::strtod(text.c_str(), nullptr));
}

std::unique_ptr<S2::Projection> MakeProjection(std::istringstream& in) {
  std::string type;
  in >> type;
  double scale = Number(in);
  if (type == "pc") return std::make_unique<S2::PlateCarreeProjection>(scale);
  return std::make_unique<S2::MercatorProjection>(scale);
}

void PrintR2(const R2Point& p) { Print({p.x(), p.y()}); }

int Extras(const std::string& kind, std::istringstream& in) {
  if (kind == "fmt_g") {
    int precision;
    in >> precision;
    double x = Number(in);
    std::printf("%.*g\n", precision, x);
  } else if (kind == "libm") {
    std::string fn;
    in >> fn;
    double x = Number(in);
    Print({fn == "exp" ? std::exp(x) : std::log(x)});
  } else if (kind == "atod") {
    double value;
    if (absl::SimpleAtod(Rest(in), &value)) {
      std::printf("%.17g\n", value);
    } else {
      std::printf("err\n");
    }
  } else if (kind == "tf_parse" || kind == "tf_tostr") {
    return TextFormat(kind, in);
  } else if (kind == "proj") {
    auto proj = MakeProjection(in);
    std::string op;
    in >> op;
    if (op == "project") {
      PrintR2(proj->Project(Point(in)));
    } else if (op == "unproject") {
      double x = Number(in), y = Number(in);
      PrintPoint(proj->Unproject(R2Point(x, y)));
    } else if (op == "from_ll") {
      double lat = Number(in), lng = Number(in);
      PrintR2(proj->FromLatLng(S2LatLng::FromRadians(lat, lng)));
    } else if (op == "to_ll") {
      double x = Number(in), y = Number(in);
      S2LatLng ll = proj->ToLatLng(R2Point(x, y));
      Print({ll.lat().radians(), ll.lng().radians()});
    } else if (op == "interpolate") {
      double f = Number(in), ax = Number(in), ay = Number(in);
      double bx = Number(in), by = Number(in);
      PrintR2(proj->Interpolate(f, R2Point(ax, ay), R2Point(bx, by)));
    } else if (op == "wrap") {
      PrintR2(proj->wrap_distance());
    } else if (op == "wrap_dest") {
      double ax = Number(in), ay = Number(in);
      double bx = Number(in), by = Number(in);
      PrintR2(proj->WrapDestination(R2Point(ax, ay), R2Point(bx, by)));
    } else {
      return Fail(kind + " " + op);
    }
  } else if (kind == "tess_min") {
    Print({S2EdgeTessellator::kMinTolerance().radians()});
  } else if (kind == "tess_proj") {
    auto proj = MakeProjection(in);
    S1Angle tolerance = Tolerance(in);
    S2EdgeTessellator tess(proj.get(), tolerance);
    std::vector<S2Point> chain = Chain(in);
    std::vector<R2Point> vertices;
    for (size_t i = 0; i + 1 < chain.size(); ++i) {
      tess.AppendProjected(chain[i], chain[i + 1], &vertices);
    }
    std::printf("%d", static_cast<int>(vertices.size()));
    for (const R2Point& v : vertices) std::printf(" %.17g %.17g", v.x(), v.y());
    std::printf("\n");
  } else if (kind == "tess_unproj") {
    auto proj = MakeProjection(in);
    S1Angle tolerance = Tolerance(in);
    S2EdgeTessellator tess(proj.get(), tolerance);
    int n;
    in >> n;
    std::vector<R2Point> chain;
    for (int i = 0; i < n; ++i) {
      double x = Number(in), y = Number(in);
      chain.push_back(R2Point(x, y));
    }
    std::vector<S2Point> vertices;
    for (size_t i = 0; i + 1 < chain.size(); ++i) {
      tess.AppendUnprojected(chain[i], chain[i + 1], &vertices);
    }
    PrintStatusPoints(vertices);
    std::printf("\n");
  } else if (kind == "term_index") {
    S2RegionTermIndexer::Options options;
    int min_level, max_level, level_mod, max_cells, points_only, space, marker;
    in >> min_level >> max_level >> level_mod >> max_cells >> points_only >>
        space >> marker;
    std::string prefix;
    in >> prefix;
    if (prefix == "-") prefix = "";
    options.set_min_level(min_level);
    options.set_max_level(max_level);
    options.set_level_mod(level_mod);
    options.set_max_cells(max_cells);
    options.set_index_contains_points_only(points_only != 0);
    options.set_optimize_for_space(space != 0);
    options.set_marker_character(static_cast<char>(marker));
    S2RegionTermIndexer indexer(options);
    std::string what;
    in >> what;
    std::vector<std::string> index_terms, query_terms;
    if (what == "point") {
      S2Point p = Point(in);
      index_terms = indexer.GetIndexTerms(p, prefix);
      query_terms = indexer.GetQueryTerms(p, prefix);
    } else if (what == "region") {
      auto region = Spec(in);
      if (points_only == 0) index_terms = indexer.GetIndexTerms(*region, prefix);
      query_terms = indexer.GetQueryTerms(*region, prefix);
    } else if (what == "cells") {
      int count;
      in >> count;
      std::vector<S2CellId> ids;
      for (int i = 0; i < count; ++i) ids.push_back(Id(in));
      S2CellUnion covering = S2CellUnion::FromVerbatim(std::move(ids));
      if (points_only == 0) {
        index_terms = indexer.GetIndexTermsForCanonicalCovering(covering, prefix);
      }
      query_terms = indexer.GetQueryTermsForCanonicalCovering(covering, prefix);
    } else {
      return Fail(kind + " " + what);
    }
    const char* sep = "";
    for (const std::string& t : index_terms) { std::printf("%s%s", sep, t.c_str()); sep = " "; }
    std::printf(" |");
    for (const std::string& t : query_terms) std::printf(" %s", t.c_str());
    std::printf("\n");
  } else if (kind == "region_op") {
    std::string op;
    in >> op;
    std::unique_ptr<S2Region> region;
    auto regions = Specs(in);
    S2RegionUnion* u = nullptr;
    if (op == "union") {
      region = std::make_unique<S2RegionUnion>(std::move(regions));
    } else {
      region = std::make_unique<S2RegionIntersection>(std::move(regions));
    }
    (void)u;
    S2LatLngRect rect = region->GetRectBound();
    S2Cap cap = region->GetCapBound();
    std::vector<S2CellId> bound;
    region->GetCellUnionBound(&bound);
    std::printf("%.17g %.17g %.17g %.17g | %.17g %.17g %.17g %.17g | ",
                rect.lat().lo(), rect.lat().hi(), rect.lng().lo(), rect.lng().hi(),
                cap.center().x(), cap.center().y(), cap.center().z(),
                cap.radius().length2());
    PrintIds(bound);
    std::string word;
    in >> word;  // CELLS
    int count;
    in >> count;
    std::printf(" |");
    for (int i = 0; i < count; ++i) {
      S2Cell cell(Id(in));
      std::printf(" %d%d", region->Contains(cell) ? 1 : 0,
                  region->MayIntersect(cell) ? 1 : 0);
    }
    in >> word;  // POINTS
    in >> count;
    std::printf(" |");
    for (int i = 0; i < count; ++i) {
      std::printf(" %d", region->Contains(Point(in)) ? 1 : 0);
    }
    std::printf(" | ");
    int max_cells, min_level, max_level, level_mod;
    in >> max_cells >> min_level >> max_level >> level_mod;
    S2RegionCoverer::Options options;
    options.set_max_cells(max_cells);
    options.set_min_level(min_level);
    options.set_max_level(max_level);
    options.set_level_mod(level_mod);
    S2RegionCoverer coverer(options);
    std::vector<S2CellId> covering, interior;
    coverer.GetCovering(*region, &covering);
    coverer.GetInteriorCovering(*region, &interior);
    PrintIds(covering);
    std::printf(" | ");
    PrintIds(interior);
    std::printf("\n");
  } else {
    return Fail(kind);
  }
  return 0;
}

int Shapes(const std::string& kind, std::istringstream& in) {
  if (kind == "loop_info") {
    S2Loop loop(Chain(in), S2Debug::DISABLE);
    S2Error error;
    bool failed = loop.FindValidationError(&error);
    if (failed) {
      std::printf("%d ", static_cast<int>(error.code()));
    } else {
      std::printf("ok ");
    }
    std::printf("%.17g %.17g %.17g %.17g %.17g %d | %s\n", loop.GetArea(),
                S2::GetApproxArea(loop.vertices_span()),
                S2::GetPerimeter(loop.vertices_span()).radians(),
                loop.GetCurvature(), loop.GetCurvatureMaxError(),
                loop.IsNormalized() ? 1 : 0,
                failed ? std::string(error.message()).c_str() : "");
  } else if (kind == "loop_dist" || kind == "pg_dist") {
    S2Point x = Point(in);
    S1Angle d, b;
    S2Point p, q;
    if (kind == "loop_dist") {
      S2Loop loop(Chain(in), S2Debug::DISABLE);
      d = loop.GetDistance(x);
      b = loop.GetDistanceToBoundary(x);
      p = loop.Project(x);
      q = loop.ProjectToBoundary(x);
    } else {
      auto polygon = Polygon(in);
      d = polygon->GetDistance(x);
      b = polygon->GetDistanceToBoundary(x);
      p = polygon->Project(x);
      q = polygon->ProjectToBoundary(x);
    }
    Print({d.radians(), b.radians(), p.x(), p.y(), p.z(), q.x(), q.y(), q.z()});
  } else if (kind == "loop_regular") {
    S2Point c = Point(in);
    double degrees = Number(in);
    int n;
    in >> n;
    PrintLoopVertices(*S2Loop::MakeRegularLoop(c, S1Angle::Degrees(degrees), n));
  } else if (kind == "loop_cell") {
    S2Loop loop{S2Cell(Id(in))};
    PrintLoopVertices(loop);
    PrintLatLngRect(loop.GetRectBound());
  } else if (kind == "loop_near") {
    S1Angle r = S1Angle::Radians(Number(in));
    S2Loop a(Chain(in), S2Debug::DISABLE);
    S2Loop b(Chain(in), S2Debug::DISABLE);
    std::printf("%d %d\n", a.BoundaryApproxEquals(b, r) ? 1 : 0,
                a.BoundaryNear(b, r) ? 1 : 0);
  } else if (kind == "cub") {
    std::string type;
    in >> type;
    std::vector<S2CellId> ids;
    if (type == "cap") {
      S2Point x = Point(in);
      S2Cap(x, S1Angle::Degrees(Number(in))).GetCellUnionBound(&ids);
    } else if (type == "rect") {
      Rect(in).GetCellUnionBound(&ids);
    } else if (type == "cell") {
      S2Cell(Id(in)).GetCellUnionBound(&ids);
    } else if (type == "loop") {
      S2Loop(Chain(in), S2Debug::DISABLE).GetCellUnionBound(&ids);
    } else if (type == "line") {
      S2Polyline(Chain(in), S2Debug::DISABLE).GetCellUnionBound(&ids);
    } else if (type == "point") {
      S2PointRegion(Point(in)).GetCellUnionBound(&ids);
    } else if (type == "poly") {
      Polygon(in)->GetCellUnionBound(&ids);
    } else if (type == "union") {
      int count;
      in >> count;
      std::vector<S2CellId> cells;
      for (int i = 0; i < count; ++i) cells.push_back(Id(in));
      S2CellUnion(std::move(cells)).GetCellUnionBound(&ids);
    } else {
      return Fail(kind + " " + type);
    }
    PrintCellIds(ids);
  } else if (kind == "pl_valid") {
    S2Polyline line(Chain(in), S2Debug::DISABLE);
    S2Error error;
    PrintError(line.FindValidationError(&error), error);
  } else if (kind == "pl_snap") {
    std::printf("%d\n", S2Polyline(Chain(in), S2Debug::DISABLE).GetSnapLevel());
  } else if (kind == "pl_suffix") {
    double f = Number(in);
    S2Polyline line(Chain(in), S2Debug::DISABLE);
    int next;
    S2Point p = line.GetSuffix(f, &next);
    std::printf("%.17g %.17g %.17g %d\n", p.x(), p.y(), p.z(), next);
  } else if (kind == "pl_unint") {
    S2Point x = Point(in);
    int next;
    in >> next;
    S2Polyline line(Chain(in), S2Debug::DISABLE);
    Print({line.UnInterpolate(x, next)});
  } else if (kind == "pl_project") {
    S2Point x = Point(in);
    S2Polyline line(Chain(in), S2Debug::DISABLE);
    int next;
    S2Point p = line.Project(x, &next);
    std::printf("%.17g %.17g %.17g %d\n", p.x(), p.y(), p.z(), next);
  } else if (kind == "pl_right") {
    S2Point x = Point(in);
    S2Polyline line(Chain(in), S2Debug::DISABLE);
    std::printf("%d\n", line.IsOnRight(x) ? 1 : 0);
  } else if (kind == "pl_subsample") {
    S1Angle r = S1Angle::Radians(Number(in));
    S2Polyline line(Chain(in), S2Debug::DISABLE);
    std::vector<int> indices;
    line.SubsampleVertices(r, &indices);
    for (size_t i = 0; i < indices.size(); ++i) {
      std::printf("%s%d", i == 0 ? "" : " ", indices[i]);
    }
    std::printf("\n");
  } else if (kind == "pl_covers") {
    S1Angle r = S1Angle::Radians(Number(in));
    S2Polyline a(Chain(in), S2Debug::DISABLE);
    S2Polyline b(Chain(in), S2Debug::DISABLE);
    std::printf("%d %d\n", a.NearlyCovers(b, r) ? 1 : 0,
                b.NearlyCovers(a, r) ? 1 : 0);
  } else if (kind == "pg_info") {
    auto polygon = Polygon(in);
    std::printf("%d %d %d", polygon->num_vertices(), polygon->GetSnapLevel(),
                polygon->IsNormalized() ? 1 : 0);
    for (int k = 0; k < polygon->num_loops(); ++k) {
      std::printf(" %d %d %d", polygon->loop(k)->depth(), polygon->GetParent(k),
                  polygon->GetLastDescendant(k));
    }
    std::printf("\n");
  } else if (kind == "pg_invert") {
    auto polygon = Polygon(in);
    polygon->Invert();
    std::vector<S2Point> points;
    for (int k = 0; k < polygon->num_loops(); ++k) {
      const S2Loop& loop = *polygon->loop(k);
      std::printf("%d %d ", loop.depth(), loop.num_vertices());
      for (int i = 0; i < loop.num_vertices(); ++i) {
        points.push_back(loop.vertex(i));
      }
    }
    PrintPoints(points);
  } else if (kind == "pg_near") {
    S1Angle r = S1Angle::Radians(Number(in));
    auto a = Polygon(in);
    auto b = Polygon(in);
    std::printf("%d %d %d\n", a->BoundaryEquals(*b) ? 1 : 0,
                a->BoundaryApproxEquals(*b, r) ? 1 : 0,
                a->BoundaryNear(*b, r) ? 1 : 0);
  } else if (kind == "hull") {
    S2ConvexHullQuery query;
    std::string item;
    while (in >> item) {
      if (item == "p") {
        query.AddPoint(Point(in));
      } else if (item == "line") {
        query.AddPolyline(S2Polyline(Chain(in), S2Debug::DISABLE));
      } else if (item == "loop") {
        query.AddLoop(S2Loop(Chain(in), S2Debug::DISABLE));
      } else if (item == "poly") {
        query.AddPolygon(*Polygon(in));
      } else {
        return Fail(kind + " " + item);
      }
    }
    std::unique_ptr<S2Loop> hull = query.GetConvexHull();
    if (hull->is_empty()) {
      std::printf("empty\n");
    } else if (hull->is_full()) {
      std::printf("full\n");
    } else {
      PrintLoopVertices(*hull);
    }
  } else {
    return Extras(kind, in);
  }
  return 0;
}

int Answer(const std::string& kind, std::istringstream& in) {
  if (kind == "edge_distance") {
    S2Point x = Point(in), a = Point(in), b = Point(in);
    S1ChordAngle d = S1ChordAngle::Infinity();
    S2::UpdateMinDistance(x, a, b, &d);
    Print({S2::GetDistance(x, a, b).radians(), d.length2()});
  } else if (kind == "edge_update") {
    double l = Number(in);
    std::string op;
    in >> op;
    S2Point x = Point(in), a = Point(in), b = Point(in);
    S1ChordAngle d = S1ChordAngle::FromLength2(l);
    bool f;
    if (op == "min") f = S2::UpdateMinDistance(x, a, b, &d);
    else if (op == "max") f = S2::UpdateMaxDistance(x, a, b, &d);
    else if (op == "interior") f = S2::UpdateMinInteriorDistance(x, a, b, &d);
    else return Fail(kind + " " + op);
    Print({f ? 1.0 : 0.0, d.length2()});
  } else if (kind == "edge_less") {
    S2Point x = Point(in), a = Point(in), b = Point(in);
    S1ChordAngle l = S1ChordAngle::FromLength2(Number(in));
    std::printf("%d %d\n", S2::IsDistanceLess(x, a, b, l) ? 1 : 0,
                S2::IsInteriorDistanceLess(x, a, b, l) ? 1 : 0);
  } else if (kind == "edge_min_error") {
    Print({S2::GetUpdateMinDistanceMaxError(
        S1ChordAngle::FromLength2(Number(in)))});
  } else if (kind == "edge_fraction") {
    S2Point x = Point(in), a = Point(in), b = Point(in);
    Print({S2::GetDistanceFraction(x, a, b)});
  } else if (kind == "edge_project") {
    S2Point x = Point(in), a = Point(in), b = Point(in);
    S2Point p = S2::Project(x, a, b);
    S2Point q = S2::Project(x, a, b, S2::RobustCrossProd(a, b));
    Print({p.x(), p.y(), p.z(), q.x(), q.y(), q.z()});
  } else if (kind == "edge_point") {
    std::string op;
    in >> op;
    S2Point a = Point(in), b = Point(in);
    double r = Number(in);
    S1Angle angle = S1Angle::Radians(r);
    S1ChordAngle chord(angle);
    S2Point p, q;
    if (op == "line") {
      p = S2::GetPointOnLine(a, b, angle);
      q = S2::GetPointOnLine(a, b, chord);
    } else if (op == "left") {
      p = S2::GetPointToLeft(a, b, angle);
      q = S2::GetPointToLeft(a, b, chord);
    } else if (op == "right") {
      p = S2::GetPointToRight(a, b, angle);
      q = S2::GetPointToRight(a, b, chord);
    } else if (op == "ray") {
      p = S2::GetPointOnRay(a, b, angle);
      q = S2::GetPointOnRay(a, b, chord);
    } else {
      return Fail(kind + " " + op);
    }
    Print({p.x(), p.y(), p.z(), q.x(), q.y(), q.z()});
  } else if (kind == "edge_interpolate") {
    S2Point a = Point(in), b = Point(in);
    PrintPoint(S2::Interpolate(a, b, Number(in)));
  } else if (kind == "edge_pair") {
    std::string op;
    in >> op;
    S1ChordAngle d = S1ChordAngle::FromLength2(Number(in));
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    bool f;
    if (op == "min") f = S2::UpdateEdgePairMinDistance(a0, a1, b0, b1, &d);
    else if (op == "max") f = S2::UpdateEdgePairMaxDistance(a0, a1, b0, b1, &d);
    else return Fail(kind + " " + op);
    Print({f ? 1.0 : 0.0, d.length2()});
  } else if (kind == "edge_pair_less") {
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    S1ChordAngle l = S1ChordAngle::FromLength2(Number(in));
    std::printf("%d\n", S2::IsEdgePairDistanceLess(a0, a1, b0, b1, l) ? 1 : 0);
  } else if (kind == "edge_pair_closest") {
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    auto r = S2::GetEdgePairClosestPoints(a0, a1, b0, b1);
    Print({r.first.x(), r.first.y(), r.first.z(), r.second.x(), r.second.y(),
           r.second.z()});
  } else if (kind == "edge_near") {
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    S1Angle t = S1Angle::Radians(Number(in));
    std::printf("%d\n", S2::IsEdgeBNearEdgeA(a0, a1, b0, b1, t) ? 1 : 0);
  } else if (kind == "edge_cross") {
    S2Point a = Point(in), b = Point(in), c = Point(in), d = Point(in);
    bool shared = a == c || a == d || b == c || b == d || a == b || c == d;
    std::printf("%d %d %d %d\n", S2::CrossingSign(a, b, c, d),
                shared ? (S2::VertexCrossing(a, b, c, d) ? 1 : 0) : 9,
                shared ? S2::SignedVertexCrossing(a, b, c, d) : 9,
                S2::EdgeOrVertexCrossing(a, b, c, d) ? 1 : 0);
  } else if (kind == "edge_intersection") {
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    int tally[static_cast<int>(S2::internal::IntersectionMethod::NUM_METHODS)] =
        {};
    S2::internal::intersection_method_tally_ = tally;
    S2Point x = S2::GetIntersection(a0, a1, b0, b1);
    S2::internal::intersection_method_tally_ = nullptr;
    int method = 0;
    while (tally[method] == 0) ++method;
    std::printf("%.17g %.17g %.17g %d\n", x.x(), x.y(), x.z(), method);
  } else if (kind == "crosser") {
    S2Point a = Point(in), b = Point(in), c = Point(in);
    int n;
    in >> n;
    std::vector<S2Point> d;
    for (int i = 0; i < n; ++i) d.push_back(Point(in));
    S2EdgeCrosser c1(&a, &b, &c), c2(&a, &b, &c), c3(&a, &b, &c);
    const char* separator = "";
    for (int i = 0; i < n; ++i) {
      int s = c1.CrossingSign(&d[i]);
      int e = c2.EdgeOrVertexCrossing(&d[i]) ? 1 : 0;
      int g = c3.SignedEdgeOrVertexCrossing(&d[i]);
      std::printf("%s%d %d %d %d", separator, s, e, g,
                  c1.last_interior_crossing_sign());
      separator = " ";
    }
    std::printf("\n");
  } else if (kind == "pred_distances") {
    S2Point x = Point(in), a = Point(in), b = Point(in);
    std::printf("%d\n", s2pred::CompareDistances(x, a, b));
  } else if (kind == "pred_distance") {
    S2Point x = Point(in), y = Point(in);
    std::printf("%d\n", s2pred::CompareDistance(
                            x, y, S1ChordAngle::FromLength2(Number(in))));
  } else if (kind == "pred_dot") {
    S2Point a = Point(in), b = Point(in);
    std::printf("%d\n", s2pred::SignDotProd(a, b));
  } else if (kind == "pred_edge_distance") {
    S2Point x = Point(in), a0 = Point(in), a1 = Point(in);
    std::printf("%d\n", s2pred::CompareEdgeDistance(
                            x, a0, a1, S1ChordAngle::FromLength2(Number(in))));
  } else if (kind == "pred_edge_pair") {
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    std::printf("%d\n", s2pred::CompareEdgePairDistance(
                            a0, a1, b0, b1,
                            S1ChordAngle::FromLength2(Number(in))));
  } else if (kind == "pred_directions") {
    S2Point a0 = Point(in), a1 = Point(in), b0 = Point(in), b1 = Point(in);
    std::printf("%d\n", s2pred::CompareEdgeDirections(a0, a1, b0, b1));
  } else if (kind == "padded") {
    S2CellId id = Id(in);
    PrintPadded(S2PaddedCell(id, Number(in)));
  } else if (kind == "padded_child") {
    S2CellId id = Id(in);
    double pad = Number(in);
    int i, j;
    in >> i >> j;
    S2PaddedCell parent(id, pad);
    PrintPadded(S2PaddedCell(parent, i, j));
  } else if (kind == "padded_child_ij") {
    S2CellId id = Id(in);
    S2PaddedCell p(id, Number(in));
    for (int pos = 0; pos < 4; ++pos) {
      int i, j;
      p.GetChildIJ(pos, &i, &j);
      std::printf("%s%d %d", pos == 0 ? "" : " ", i, j);
    }
    std::printf("\n");
  } else if (kind == "padded_shrink") {
    S2CellId id = Id(in);
    S2PaddedCell p(id, Number(in));
    double u0 = Number(in), u1 = Number(in), v0 = Number(in), v1 = Number(in);
    std::printf("%llu\n", static_cast<unsigned long long>(
                              p.ShrinkToFit(R2Rect(R1Interval(u0, u1),
                                                   R1Interval(v0, v1)))
                                  .id()));
  } else if (kind == "cell_dist_point") {
    S2Cell cell(Id(in));
    S2Point p = Point(in);
    Print({cell.GetDistance(p).length2(), cell.GetBoundaryDistance(p).length2(),
           cell.GetMaxDistance(p).length2()});
  } else if (kind == "cell_dist_edge") {
    S2Cell cell(Id(in));
    S2Point a = Point(in), b = Point(in);
    Print({cell.GetDistance(a, b).length2(),
           cell.GetMaxDistance(a, b).length2()});
  } else if (kind == "cell_dist_cell") {
    S2Cell c1(Id(in));
    S2Cell c2(Id(in));
    S1ChordAngle l = S1ChordAngle::FromLength2(Number(in));
    std::printf("%.17g %.17g %d %d %d %d\n", c1.GetDistance(c2).length2(),
                c1.GetMaxDistance(c2).length2(),
                c1.IsDistanceLess(c2, l) ? 1 : 0,
                c1.IsDistanceLessOrEqual(c2, l) ? 1 : 0,
                c1.IsMaxDistanceLess(c2, l) ? 1 : 0,
                c1.IsMaxDistanceLessOrEqual(c2, l) ? 1 : 0);
  } else if (kind == "rect_centroid") {
    PrintPoint(Rect(in).GetCentroid());
  } else if (kind == "rect_boundary") {
    S2LatLngRect r = Rect(in);
    S2Point v0 = Point(in), v1 = Point(in);
    std::printf("%d\n", r.BoundaryIntersects(v0, v1) ? 1 : 0);
  } else if (kind == "rect_expand") {
    S2LatLngRect r = Rect(in);
    PrintLatLngRect(r.ExpandedByDistance(S1Angle::Radians(Number(in))));
  } else if (kind == "rect_distance") {
    S2LatLngRect a = Rect(in);
    S2LatLngRect b = Rect(in);
    Print({a.GetDistance(b).radians(),
           a.GetDirectedHausdorffDistance(b).radians(),
           a.GetHausdorffDistance(b).radians()});
  } else if (kind == "rect_distance_ll") {
    S2LatLngRect a = Rect(in);
    double lat = Number(in), lng = Number(in);
    Print({a.GetDistance(S2LatLng::FromRadians(lat, lng)).radians()});
  } else if (kind == "bounder" || kind == "bounder_ll") {
    int n;
    in >> n;
    S2LatLngRectBounder bounder;
    for (int i = 0; i < n; ++i) {
      if (kind == "bounder") {
        bounder.AddPoint(Point(in));
      } else {
        double lat = Number(in), lng = Number(in);
        bounder.AddLatLng(S2LatLng::FromRadians(lat, lng));
      }
    }
    PrintLatLngRect(bounder.GetBound());
  } else if (kind == "bounder_sub") {
    PrintLatLngRect(S2LatLngRectBounder::ExpandForSubregions(Rect(in)));
  } else if (kind == "bounder_error") {
    S2LatLng e = S2LatLngRectBounder::MaxErrorForTests();
    Print({e.lat().radians(), e.lng().radians()});
  } else {
    return Shapes(kind, in);
  }
  return 0;
}

}  // namespace

int main() {
  std::string line;
  while (std::getline(std::cin, line)) {
    std::istringstream in(line);
    std::string kind;
    if (!(in >> kind)) continue;
    if (kind == "cap") {
      double x = Number(in), y = Number(in), z = Number(in);
      double degrees = Number(in);
      Cover(S2Cap(S2Point(x, y, z), S1Angle::Degrees(degrees)), in);
    } else if (kind == "capll") {
      double lat = Number(in), lng = Number(in), degrees = Number(in);
      S2Point center = S2LatLng::FromDegrees(lat, lng).ToPoint();
      Cover(S2Cap(center, S1Angle::Degrees(degrees)), in);
    } else if (kind == "rect") {
      double lat1 = Number(in), lng1 = Number(in);
      double lat2 = Number(in), lng2 = Number(in);
      Cover(S2LatLngRect::FromPointPair(S2LatLng::FromDegrees(lat1, lng1),
                                        S2LatLng::FromDegrees(lat2, lng2)),
            in);
    } else if (kind == "cells") {
      int count;
      in >> count;
      std::vector<S2CellId> ids;
      for (int i = 0; i < count; ++i) ids.push_back(Id(in));
      Cover(S2CellUnion(std::move(ids)), in);
    } else if (kind == "wrap") {
      S2CellId neighbors[4];
      S2CellId::FromFaceIJ(0, 0, 1073741823).GetEdgeNeighbors(neighbors);
      std::printf("%s\n", neighbors[3].ToToken().c_str());
    } else if (kind == "angle_trig") {
      S1Angle a = S1Angle::Radians(Number(in));
      S1Angle::SinCosPair sc = a.SinCos();
      Print({sin(a), cos(a), tan(a), sc.sin, sc.cos});
    } else if (kind == "angle_unsigned") {
      std::string unit;
      in >> unit;
      unsigned long long u;
      in >> u;
      S1Angle a = unit == "e6" ? S1Angle::UnsignedE6(static_cast<uint32_t>(u))
                               : S1Angle::UnsignedE7(static_cast<uint32_t>(u));
      Print({a.radians()});
    } else if (kind == "angle_points") {
      S2Point a = Point(in), b = Point(in);
      Print({S1Angle(a, b).radians()});
    } else if (kind == "chord") {
      std::string unit;
      in >> unit;
      double v = Number(in);
      S1ChordAngle c = S1ChordAngle::Zero();
      if (unit == "radians") c = S1ChordAngle::Radians(v);
      else if (unit == "degrees") c = S1ChordAngle::Degrees(v);
      else if (unit == "e5") c = S1ChordAngle::E5(static_cast<int32_t>(v));
      else if (unit == "e6") c = S1ChordAngle::E6(static_cast<int32_t>(v));
      else if (unit == "e7") c = S1ChordAngle::E7(static_cast<int32_t>(v));
      else return Fail(kind + " " + unit);
      Print({c.length2(), c.GetS1AngleConstructorMaxError(),
             c.GetS2PointConstructorMaxError(), static_cast<double>(c.e5()),
             static_cast<double>(c.e6()), static_cast<double>(c.e7())});
    } else if (kind == "chord_fast") {
      Print({S1ChordAngle::FastUpperBoundFrom(S1Angle::Radians(Number(in)))
                 .length2()});
    } else if (kind == "earth_lng") {
      std::string unit;
      in >> unit;
      double d = Number(in), lat = Number(in);
      Print({unit == "km" ? S2Earth::KmToLongitudeRadians(d, lat)
                          : S2Earth::MetersToLongitudeRadians(d, lat)});
    } else if (kind == "earth_bearing") {
      double lat1 = Number(in), lng1 = Number(in);
      double lat2 = Number(in), lng2 = Number(in);
      Print({S2Earth::GetInitialBearing(S2LatLng::FromRadians(lat1, lng1),
                                        S2LatLng::FromRadians(lat2, lng2))
                 .radians()});
    } else if (kind == "point2") {
      std::string op;
      in >> op;
      S2Point a = Point(in), b = Point(in);
      if (op == "mul") PrintPoint(a.MulComponents(b));
      else if (op == "div") PrintPoint(a.DivComponents(b));
      else if (op == "min") PrintPoint(Min(a, b));
      else if (op == "max") PrintPoint(Max(a, b));
      else return Fail(kind + " " + op);
    } else if (kind == "point1") {
      std::string op;
      in >> op;
      S2Point a = Point(in);
      if (op == "sqrt") PrintPoint(a.Sqrt());
      else if (op == "floor") PrintPoint(a.Floor());
      else if (op == "ceil") PrintPoint(a.Ceil());
      else if (op == "refdir") PrintPoint(S2::RefDir(a));
      else return Fail(kind + " " + op);
    } else if (kind == "coords_uvw") {
      int face;
      in >> face;
      PrintPoint(S2::FaceXYZtoUVW(face, Point(in)));
    } else if (kind == "coords_axis") {
      int face, axis;
      in >> face >> axis;
      PrintPoint(S2::GetUVWAxis(face, axis));
    } else if (kind == "coords_face") {
      int face, axis, direction;
      in >> face >> axis >> direction;
      std::printf("%d\n", S2::GetUVWFace(face, axis, direction));
    } else if (kind == "coords_si_ti_xyz") {
      int face;
      unsigned int si, ti;
      in >> face >> si >> ti;
      PrintPoint(S2::FaceSiTitoXYZ(face, si, ti));
    } else if (kind == "coords_ij_st_min") {
      int i;
      in >> i;
      Print({S2::IJtoSTMin(i)});
    } else if (kind == "coords_xyz_si_ti") {
      int face;
      unsigned int si, ti;
      int level = S2::XYZtoFaceSiTi(Point(in), &face, &si, &ti);
      std::printf("%d %u %u %d\n", face, si, ti, level);
    } else if (kind == "aspect") {
      Print({S2::kMaxEdgeAspect, S2::kMaxDiagAspect});
    } else if (kind == "measure_angle") {
      S2Point a = Point(in), b = Point(in), c = Point(in);
      Print({S2::Angle(a, b, c)});
    } else if (kind == "measure_turn") {
      S2Point a = Point(in), b = Point(in), c = Point(in);
      Print({S2::TurnAngle(a, b, c)});
    } else if (kind == "centroid_planar") {
      S2Point a = Point(in), b = Point(in), c = Point(in);
      PrintPoint(S2::PlanarCentroid(a, b, c));
    } else if (kind == "centroid_true") {
      S2Point a = Point(in), b = Point(in), c = Point(in);
      PrintPoint(S2::TrueCentroid(a, b, c));
    } else if (kind == "centroid_edge") {
      S2Point a = Point(in), b = Point(in);
      PrintPoint(S2::TrueCentroid(a, b));
    } else if (kind == "cap_centroid") {
      S2Point a = Point(in);
      PrintPoint(S2Cap(a, S1Angle::Degrees(Number(in))).GetCentroid());
    } else if (kind == "latlng_string") {
      double lat = Number(in), lng = Number(in);
      std::printf("%s\n",
                  S2LatLng::FromRadians(lat, lng).ToStringInDegrees().c_str());
    } else if (kind == "latlng_unsigned") {
      std::string unit;
      in >> unit;
      unsigned long long lat, lng;
      in >> lat >> lng;
      S2LatLng ll =
          unit == "e6"
              ? S2LatLng::FromUnsignedE6(static_cast<uint32_t>(lat),
                                         static_cast<uint32_t>(lng))
              : S2LatLng::FromUnsignedE7(static_cast<uint32_t>(lat),
                                         static_cast<uint32_t>(lng));
      Print({ll.lat().radians(), ll.lng().radians()});
    } else if (kind == "cell_center_st") {
      R2Point p = Id(in).GetCenterST();
      Print({p[0], p[1]});
    } else if (kind == "cell_bound_st") {
      PrintRect(Id(in).GetBoundST());
    } else if (kind == "cell_distance_from_begin") {
      std::printf("%lld\n",
                  static_cast<long long>(Id(in).distance_from_begin()));
    } else if (kind == "cell_ij_bound") {
      int ij[2], level;
      in >> ij[0] >> ij[1] >> level;
      PrintRect(S2CellId::IJLevelToBoundUV(ij, level));
    } else if (kind == "cell_expand") {
      double u0 = Number(in), u1 = Number(in), v0 = Number(in), v1 = Number(in);
      double distance = Number(in);
      PrintRect(S2CellId::ExpandedByDistanceUV(
          R2Rect(R1Interval(u0, u1), R1Interval(v0, v1)),
          S1Angle::Radians(distance)));
    } else if (kind == "cell_max_tile") {
      S2CellId id = Id(in);
      S2CellId limit = Id(in);
      std::printf("%llu\n",
                  static_cast<unsigned long long>(id.maximum_tile(limit).id()));
    } else if (kind == "cell_from_pos") {
      int face, level;
      unsigned long long pos;
      in >> face >> pos >> level;
      std::printf("%llu\n", static_cast<unsigned long long>(
                                 S2CellId::FromFacePosLevel(face, pos, level).id()));
    } else if (kind == "cell_child_begin") {
      S2CellId id = Id(in);
      int level;
      in >> level;
      std::printf("%llu %llu\n",
                  static_cast<unsigned long long>(id.child_begin(level).id()),
                  static_cast<unsigned long long>(id.child_end(level).id()));
    } else if (kind == "cell_lsb_level") {
      int level;
      in >> level;
      std::printf("%llu\n", static_cast<unsigned long long>(
                                 S2CellId::lsb_for_level(level)));
    } else if (kind == "cell_ancestor") {
      S2CellId a = Id(in);
      S2CellId b = Id(in);
      std::printf("%d\n", a.GetCommonAncestorLevel(b));
    } else if (kind == "cell_si_ti") {
      int si, ti;
      int face = Id(in).GetCenterSiTi(&si, &ti);
      std::printf("%d %d %d\n", face, si, ti);
    } else if (kind == "cell_point_raw") {
      PrintPoint(Id(in).ToPointRaw());
    } else if (kind == "union_min_max") {
      S2CellId a = Id(in);
      S2CellId b = Id(in);
      PrintUnion(S2CellUnion::FromMinMax(a, b));
    } else if (kind == "union_begin_end") {
      S2CellId a = Id(in);
      S2CellId b = Id(in);
      PrintUnion(S2CellUnion::FromBeginEnd(a, b));
    } else if (kind == "union_verbatim") {
      int count;
      in >> count;
      std::vector<S2CellId> ids;
      for (int i = 0; i < count; ++i) ids.push_back(Id(in));
      S2CellUnion u = S2CellUnion::FromVerbatim(std::move(ids));
      PrintIds(u.cell_ids());
      std::printf(" | %d %d\n", u.IsValid() ? 1 : 0, u.IsNormalized() ? 1 : 0);
    } else if (Answer(kind, in) != 0) {
      return 1;
    }
  }
  return 0;
}

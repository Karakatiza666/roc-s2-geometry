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
// Scalar functions (A, B, C are points written as three numbers):
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

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
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
#include "s2/s2coords.h"
#include "s2/s2earth.h"
#include "s2/s2latlng.h"
#include "s2/s2latlng_rect.h"
#include "s2/s2measures.h"
#include "s2/s2metrics.h"
#include "s2/s2point.h"
#include "s2/s2pointutil.h"
#include "s2/s2region.h"
#include "s2/s2region_coverer.h"

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

S2Point Point(std::istringstream& in) {
  double x = Number(in), y = Number(in), z = Number(in);
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
    } else {
      return Fail(kind);
    }
  }
  return 0;
}

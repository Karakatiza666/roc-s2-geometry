// SPDX-FileCopyrightText: 2026 Heorhii Bulakh
// SPDX-License-Identifier: UPL-1.0
//
// Prints the coverings that upstream's S2RegionCoverer gives for a list of
// regions. tools/generate_corpus.py runs it to write tests/CoverCorpus.roc.
//
// Build it against google/s2geometry v0.14.0 and the abseil it was built
// with, then give it the cases on standard input, one per line:
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
// the normalized S2CellUnion of the given ids.
//
// For each region it prints one line: the covering, a "|", and the interior
// covering, as decimal cell ids in the order upstream returns them.
//
// "wrap" prints the token of S2CellId::FromFaceIJWrap(0, -1, 1073741823).
// That function is private, so the driver reaches it through the left edge
// neighbour of the leaf at face 0, i = 0, j = 1073741823, which upstream
// computes as FromFaceIJSame(0, -1, j, false).parent(30).

#include <cstdint>
#include <cstdio>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "s2/s1angle.h"
#include "s2/s2cap.h"
#include "s2/s2cell_id.h"
#include "s2/s2cell_union.h"
#include "s2/s2latlng.h"
#include "s2/s2latlng_rect.h"
#include "s2/s2point.h"
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
      for (int i = 0; i < count; ++i) {
        unsigned long long id;
        in >> id;
        ids.push_back(S2CellId(id));
      }
      Cover(S2CellUnion(std::move(ids)), in);
    } else if (kind == "wrap") {
      S2CellId neighbors[4];
      S2CellId::FromFaceIJ(0, 0, 1073741823).GetEdgeNeighbors(neighbors);
      std::printf("%s\n", neighbors[3].ToToken().c_str());
    } else {
      std::fprintf(stderr, "unknown case: %s\n", kind.c_str());
      return 1;
    }
  }
  return 0;
}

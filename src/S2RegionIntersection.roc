import R1Interval
import S1Angle
import S1Interval
import S2Cap
import S2RegionUnion
import S2CellUnion
import S2LatLng
import S2Loop
import S2Polyline
import S2PointRegion
import S2RegionCoverer
import S2Cap
import S2Cell
import S2CellId
import S2LatLngRect
import S2Point
import S2Region

## The intersection of some regions. Upstream's `S2RegionIntersection`.
##
## The regions may be of different types, each wrapped with `S2Region.from`.
## An intersection is a region itself, so a coverer can cover it, and it can
## be wrapped again to go inside another intersection or a union.
##
##     both = S2RegionIntersection.new([S2Region.from(cap), S2Region.from(rect)])
##     S2RegionCoverer.default().covering(both)
S2RegionIntersection := { regions : List(S2Region) }.{

	## The intersection of the regions. With no regions it is the whole sphere.
	new : List(S2Region) -> S2RegionIntersection
	new = |regions| { regions: regions }

	## The number of regions.
	num_regions : S2RegionIntersection -> U64
	num_regions = |both| both.regions.len()

	## The `i`-th region, if there is one.
	region_at : S2RegionIntersection, U64 -> Try(S2Region, [OutOfBounds])
	region_at = |both, index| both.regions.get(index).map_err(|_| OutOfBounds)

	## The regions.
	regions : S2RegionIntersection -> List(S2Region)
	regions = |both| both.regions

	## A cap that contains the intersection: the cap bound of its rectangle
	## bound.
	cap_bound : S2RegionIntersection -> S2Cap
	cap_bound = |both| both.rect_bound().cap_bound()

	## The intersection of every region's rectangle bound.
	rect_bound : S2RegionIntersection -> S2LatLngRect
	rect_bound = |both|
		both.regions.fold(
			S2LatLngRect.full(),
			|bound, region| bound.intersection(region.rect_bound()),
		)

	## A few cells that cover the intersection: those of its cap bound.
	cell_union_bound : S2RegionIntersection -> List(S2CellId)
	cell_union_bound = |both| both.cap_bound().cell_union_bound()

	## True when every region contains the cell.
	contains_cell : S2RegionIntersection, S2Cell -> Bool
	contains_cell = |both, cell| both.regions.all(|region| region.contains_cell(cell))

	## True when every region may meet the cell.
	may_intersect_cell : S2RegionIntersection, S2Cell -> Bool
	may_intersect_cell = |both, cell| both.regions.all(|region| region.may_intersect_cell(cell))

	## True when every region contains the point.
	contains_point : S2RegionIntersection, S2Point -> Bool
	contains_point = |both, p| both.regions.all(|region| region.contains_point(p))
}

query_cells : List(S2Cell)
query_cells = [S2Cell.from_cell_id(S2CellId.from_id(1152921504606846976)), S2Cell.from_cell_id(S2CellId.from_id(5170132372221329408)), S2Cell.from_cell_id(S2CellId.from_id(2305843009213693952)), S2Cell.from_cell_id(S2CellId.from_id(8070450532247928832)), S2Cell.from_cell_id(S2CellId.from_id(3458764513820540928))]

query_points : List(S2Point)
query_points = [S2LatLng.from_degrees(35.0, 40.0).to_point(), S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(10.0, 10.0).to_point(), S2LatLng.from_degrees(12.0, 14.0).to_point(), S2LatLng.from_degrees(40.0, 40.0).to_point(), S2LatLng.from_degrees(-35.0, -40.0).to_point()]

# Upstream's region unions and intersections, through tools/s2_oracle.cc. The
# first two are S2RegionUnionTest.Basic: the union of two point regions, whose
# covering with one cell is face 0, and the empty union. The query cells are
# face 0, 2/033 and three more faces, and the query points are
# 35:40, 0:0, 10:10, 12:14, 40:40 and -35:-40.

# The bounds below are compared to within 1e-14, because the port rounds a
# bound in its last place differently from upstream in some cases. Everything
# else is exact.

# I1 two overlapping caps.
i1_region : () -> S2RegionIntersection
i1_region = || S2RegionIntersection.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(12.0, 14.0).to_point(), S1Angle.from_degrees(5.0)))])

i1_coverer : S2RegionCoverer
i1_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i1_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.12217304763960306, 0.26179938779914946), S1Interval.new(0.15512491550406615, 0.26314912155817627)), 1.0e-14)
expect i1_region().cap_bound().center().approx_eq(S2Point.new(0.96023796644218706, 0.20380131276899796, 0.19080899537654483), 1.0e-14)
expect (i1_region().cap_bound().radius().length2() - 0.0077135710197755291).abs() < 1.0e-14
expect i1_region().cell_union_bound() == [S2CellId.from_id(1224979098644774912), S2CellId.from_id(1657324662872342528), S2CellId.from_id(1369094286720630784), S2CellId.from_id(1513209474796486656)]
expect query_cells.map(|c| (i1_region().contains_cell(c), i1_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| i1_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.True, Bool.False, Bool.False]
expect i1_coverer.covering(i1_region()) == [S2CellId.from_id(1176565402650542080), S2CellId.from_id(1217097799296876544), S2CellId.from_id(1220194024040693760), S2CellId.from_id(1221601398924247040), S2CellId.from_id(1223853198737932288), S2CellId.from_id(1229482698272145408), S2CellId.from_id(1271140994825322496), S2CellId.from_id(1273392794639007744)]
expect i1_coverer.interior_covering(i1_region()) == [S2CellId.from_id(1223571723761221632), S2CellId.from_id(1224134673714642944), S2CellId.from_id(1224697623668064256), S2CellId.from_id(1226104998551617536), S2CellId.from_id(1229271592039612416), S2CellId.from_id(1232649291760140288), S2CellId.from_id(1272548369708875776), S2CellId.from_id(1273111319662297088)]

# I2 cap and rectangle.
i2_region : () -> S2RegionIntersection
i2_region = || S2RegionIntersection.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from(S2LatLngRect.new(R1Interval.new(0.1, 0.3), S1Interval.new(0.1, 0.35)))])

i2_coverer : S2RegionCoverer
i2_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i2_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.10000000000000001, 0.26179938779914946), S1Interval.new(0.10000000000000001, 0.26314912155817627)), 1.0e-14)
expect i2_region().cap_bound().center().approx_eq(S2Point.new(0.96751105796294989, 0.17763183326787857, 0.17991465901728582), 1.0e-14)
expect (i2_region().cap_bound().radius().length2() - 0.013050702763424113).abs() < 1.0e-14
expect i2_region().cell_union_bound() == [S2CellId.from_id(1224979098644774912), S2CellId.from_id(1080863910568919040), S2CellId.from_id(1945555039024054272), S2CellId.from_id(360287970189639680)]
expect query_cells.map(|c| (i2_region().contains_cell(c), i2_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| i2_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.True, Bool.False, Bool.False]
expect i2_coverer.covering(i2_region()) == [S2CellId.from_id(1175439502743699456), S2CellId.from_id(1220475499017404416), S2CellId.from_id(1229482698272145408), S2CellId.from_id(1274518694545850368)]
expect i2_coverer.interior_covering(i2_region()) == [S2CellId.from_id(1174595077813567488), S2CellId.from_id(1175158027766988800), S2CellId.from_id(1176565402650542080), S2CellId.from_id(1222445823854379008), S2CellId.from_id(1223853198737932288), S2CellId.from_id(1226104998551617536), S2CellId.from_id(1271985419755454464), S2CellId.from_id(1273392794639007744)]

# I3 empty.
i3_region : () -> S2RegionIntersection
i3_region = || S2RegionIntersection.new([])

i3_coverer : S2RegionCoverer
i3_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i3_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.1415926535897931, 3.1415926535897931)), 1.0e-14)
expect i3_region().cap_bound().center().approx_eq(S2Point.new(0.0, 0.0, 1.0), 1.0e-14)
expect (i3_region().cap_bound().radius().length2() - 4.0).abs() < 1.0e-14
expect i3_region().cell_union_bound() == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880), S2CellId.from_id(8070450532247928832), S2CellId.from_id(10376293541461622784), S2CellId.from_id(12682136550675316736)]
expect query_cells.map(|c| (i3_region().contains_cell(c), i3_region().may_intersect_cell(c))) == [(Bool.True, Bool.True), (Bool.True, Bool.True), (Bool.True, Bool.True), (Bool.True, Bool.True), (Bool.True, Bool.True)]
expect query_points.map(|p| i3_region().contains_point(p)) == [Bool.True, Bool.True, Bool.True, Bool.True, Bool.True, Bool.True]
expect i3_coverer.covering(i3_region()) == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880), S2CellId.from_id(8070450532247928832), S2CellId.from_id(10376293541461622784), S2CellId.from_id(12682136550675316736)]
expect i3_coverer.interior_covering(i3_region()) == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880), S2CellId.from_id(8070450532247928832), S2CellId.from_id(10376293541461622784), S2CellId.from_id(12682136550675316736)]

# I4 disjoint caps.
i4_region : () -> S2RegionIntersection
i4_region = || S2RegionIntersection.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(-40.0, 100.0).to_point(), S1Angle.from_degrees(20.0)))])

i4_coverer : S2RegionCoverer
i4_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i4_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(1.0, 0.0), S1Interval.new(3.1415926535897931, -3.1415926535897931)), 1.0e-14)
expect i4_region().cap_bound().center().approx_eq(S2Point.new(1.0, 0.0, 0.0), 1.0e-14)
expect (i4_region().cap_bound().radius().length2() - -1.0).abs() < 1.0e-14
expect i4_region().cell_union_bound() == [S2CellId.from_id(1152921504606846980), S2CellId.from_id(1152921504606846972), S2CellId.from_id(1921535841011411628), S2CellId.from_id(384307168202282324)]
expect query_cells.map(|c| (i4_region().contains_cell(c), i4_region().may_intersect_cell(c))) == [(Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| i4_region().contains_point(p)) == [Bool.False, Bool.False, Bool.False, Bool.False, Bool.False, Bool.False]
expect i4_coverer.covering(i4_region()) == []
expect i4_coverer.interior_covering(i4_region()) == []

# I5 rect and face.
i5_region : () -> S2RegionIntersection
i5_region = || S2RegionIntersection.new([S2Region.from(S2LatLngRect.new(R1Interval.new(0.1, 0.3), S1Interval.new(0.1, 0.35))), S2Region.from_cell(S2Cell.from_face(0))])

i5_coverer : S2RegionCoverer
i5_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i5_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.10000000000000001, 0.29999999999999999), S1Interval.new(0.10000000000000001, 0.34999999999999998)), 1.0e-14)
expect i5_region().cap_bound().center().approx_eq(S2Point.new(0.95536312461486816, 0.21865908882906851, 0.19866933079506122), 1.0e-14)
expect (i5_region().cap_bound().radius().length2() - 0.02520887624577375).abs() < 1.0e-14
expect i5_region().cell_union_bound() == [S2CellId.from_id(1441151880758558720), S2CellId.from_id(864691128455135232), S2CellId.from_id(2017612633061982208), S2CellId.from_id(288230376151711744)]
expect query_cells.map(|c| (i5_region().contains_cell(c), i5_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| i5_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.True, Bool.False, Bool.False]
expect i5_coverer.covering(i5_region()) == [S2CellId.from_id(1175439502743699456), S2CellId.from_id(1211468299762663424), S2CellId.from_id(1220475499017404416), S2CellId.from_id(1242993497154256896), S2CellId.from_id(1266637395197952000), S2CellId.from_id(1268044770081505280), S2CellId.from_id(1269733619941769216), S2CellId.from_id(1274518694545850368)]
expect i5_coverer.interior_covering(i5_region()) == [S2CellId.from_id(1176565402650542080), S2CellId.from_id(1214845999483191296), S2CellId.from_id(1217097799296876544), S2CellId.from_id(1229482698272145408), S2CellId.from_id(1235112197806358528), S2CellId.from_id(1241867597247414272), S2CellId.from_id(1271140994825322496), S2CellId.from_id(1273392794639007744)]

# I6 cap and loop.
i6_region : () -> S2RegionIntersection
i6_region = || S2RegionIntersection.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from(S2Loop.from_points([S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point(), S2LatLng.from_degrees(20.0, 0.0).to_point()]))])

i6_coverer : S2RegionCoverer
i6_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i6_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.087266462599716502, 0.26179938779914946), S1Interval.new(0.085916728840689599, 0.26314912155817627)), 1.0e-14)
expect i6_region().cap_bound().center().approx_eq(S2Point.new(0.9698463103929541, 0.17101007166283433, 0.17364817766693036), 1.0e-14)
expect (i6_region().cap_bound().radius().length2() - 0.015309663264696205).abs() < 1.0e-14
expect i6_region().cell_union_bound() == [S2CellId.from_id(1441151880758558720), S2CellId.from_id(864691128455135232), S2CellId.from_id(2017612633061982208), S2CellId.from_id(288230376151711744)]
expect query_cells.map(|c| (i6_region().contains_cell(c), i6_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| i6_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.False, Bool.False, Bool.False]
expect i6_coverer.covering(i6_region()) == [S2CellId.from_id(1167839678372511744), S2CellId.from_id(1168138745535266816), S2CellId.from_id(1175439502743699456), S2CellId.from_id(1220475499017404416), S2CellId.from_id(1273392794639007744), S2CellId.from_id(1275644594452692992), S2CellId.from_id(1277896394266378240), S2CellId.from_id(1282048150172860416)]
expect i6_coverer.interior_covering(i6_region()) == [S2CellId.from_id(1174032127860146176), S2CellId.from_id(1174595077813567488), S2CellId.from_id(1175158027766988800), S2CellId.from_id(1175720977720410112), S2CellId.from_id(1177972777534095360), S2CellId.from_id(1178535727487516672), S2CellId.from_id(1222445823854379008), S2CellId.from_id(1275363119475982336)]

# I7 cap and cell union.
i7_region : () -> S2RegionIntersection
i7_region = || S2RegionIntersection.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from(S2CellUnion.from_ids([1152921504606846976, 5170132372221329408]))])

i7_coverer : S2RegionCoverer
i7_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect i7_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.087266462599716502, 0.26179938779914946), S1Interval.new(0.085916728840689599, 0.26314912155817627)), 1.0e-14)
expect i7_region().cap_bound().center().approx_eq(S2Point.new(0.9698463103929541, 0.17101007166283433, 0.17364817766693036), 1.0e-14)
expect (i7_region().cap_bound().radius().length2() - 0.015309663264696205).abs() < 1.0e-14
expect i7_region().cell_union_bound() == [S2CellId.from_id(1441151880758558720), S2CellId.from_id(864691128455135232), S2CellId.from_id(2017612633061982208), S2CellId.from_id(288230376151711744)]
expect query_cells.map(|c| (i7_region().contains_cell(c), i7_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| i7_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.True, Bool.False, Bool.False]
expect i7_coverer.covering(i7_region()) == [S2CellId.from_id(1167910047116689408), S2CellId.from_id(1168050784605044736), S2CellId.from_id(1168138745535266816), S2CellId.from_id(1175439502743699456), S2CellId.from_id(1220475499017404416), S2CellId.from_id(1229482698272145408), S2CellId.from_id(1274518694545850368), S2CellId.from_id(1282048150172860416)]
expect i7_coverer.interior_covering(i7_region()) == [S2CellId.from_id(1176565402650542080), S2CellId.from_id(1222445823854379008), S2CellId.from_id(1223853198737932288), S2CellId.from_id(1226104998551617536), S2CellId.from_id(1271985419755454464), S2CellId.from_id(1273392794639007744), S2CellId.from_id(1274800169522561024), S2CellId.from_id(1275363119475982336)]

# `num_regions`, `region_at` and `regions`.
expect {
	cap = S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))
	both = S2RegionIntersection.new([S2Region.from_cap(cap), S2Region.from(S2LatLngRect.from_cap(cap))])
	both.num_regions() == 2 and both.regions().len() == 2 and both.region_at(1).is_ok() and both.region_at(2).is_err()
}
# The empty intersection is the whole sphere.
expect S2RegionIntersection.new([]).rect_bound() == S2LatLngRect.full()
expect S2RegionIntersection.new([]).contains_point(S2LatLng.from_degrees(10.0, 10.0).to_point())
expect S2RegionIntersection.new([]).contains_cell(S2Cell.from_face(2))
# An intersection can be a member of a union and of another intersection.
expect {
	a = S2LatLng.from_degrees(10.0, 10.0).to_point()
	cap = S2Cap.from_center_angle(a, S1Angle.from_degrees(5.0))
	inner = S2RegionIntersection.new([S2Region.from_cap(cap)])
	S2RegionIntersection.new([S2Region.from(inner)]).contains_point(a)
		and S2RegionUnion.new([S2Region.from(inner)]).contains_point(a)
}

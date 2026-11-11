import R1Interval
import S1Angle
import S1Interval
import S2Cap
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

## The union of some regions. Upstream's `S2RegionUnion`.
##
## The regions may be of different types, each wrapped with `S2Region.from`.
## A union is a region itself, so a coverer can cover it, and it can be
## wrapped again to go inside another union.
##
##     union = S2RegionUnion.new([S2Region.from(cap), S2Region.from(rect)])
##     S2RegionCoverer.default().covering(union)
S2RegionUnion := { regions : List(S2Region) }.{

	## The union of the regions. With no regions it is empty.
	new : List(S2Region) -> S2RegionUnion
	new = |regions| { regions: regions }

	## The union with one more region.
	add : S2RegionUnion, S2Region -> S2RegionUnion
	add = |union, region| { regions: union.regions.append(region) }

	## The number of regions.
	num_regions : S2RegionUnion -> U64
	num_regions = |union| union.regions.len()

	## The `i`-th region, if there is one.
	region_at : S2RegionUnion, U64 -> Try(S2Region, [OutOfBounds])
	region_at = |union, index| union.regions.get(index).map_err(|_| OutOfBounds)

	## The regions.
	regions : S2RegionUnion -> List(S2Region)
	regions = |union| union.regions

	## A cap that contains the union: the cap bound of its rectangle bound.
	cap_bound : S2RegionUnion -> S2Cap
	cap_bound = |union| union.rect_bound().cap_bound()

	## The smallest rectangle that contains every region's rectangle bound.
	rect_bound : S2RegionUnion -> S2LatLngRect
	rect_bound = |union|
		union.regions.fold(
			S2LatLngRect.empty(),
			|bound, region| bound.union(region.rect_bound()),
		)

	## A few cells that cover the union: those of its cap bound.
	cell_union_bound : S2RegionUnion -> List(S2CellId)
	cell_union_bound = |union| union.cap_bound().cell_union_bound()

	## True when one region contains the cell. This can be false for a cell
	## that the regions contain only together.
	contains_cell : S2RegionUnion, S2Cell -> Bool
	contains_cell = |union, cell| union.regions.any(|region| region.contains_cell(cell))

	## True when a region may meet the cell.
	may_intersect_cell : S2RegionUnion, S2Cell -> Bool
	may_intersect_cell = |union, cell| union.regions.any(|region| region.may_intersect_cell(cell))

	## True when a region contains the point.
	contains_point : S2RegionUnion, S2Point -> Bool
	contains_point = |union, p| union.regions.any(|region| region.contains_point(p))
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

# U1 Basic (S2RegionUnionTest.Basic).
u1_region : () -> S2RegionUnion
u1_region = || S2RegionUnion.new([S2Region.from(S2PointRegion.new(S2LatLng.from_degrees(35.0, 40.0).to_point())), S2Region.from(S2PointRegion.new(S2LatLng.from_degrees(-35.0, -40.0).to_point()))])

u1_coverer : S2RegionCoverer
u1_coverer = S2RegionCoverer.default().with_max_cells(1).with_max_level(30)

expect u1_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(-0.6108652381980153, 0.6108652381980153), S1Interval.new(-0.69813170079773179, 0.69813170079773179)), 1.0e-14)
expect u1_region().cap_bound().center().approx_eq(S2Point.new(1.0, 0.0, 0.0), 1.0e-14)
expect (u1_region().cap_bound().radius().length2() - 0.7449862568057336).abs() < 1.0e-14
expect u1_region().cell_union_bound() == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880), S2CellId.from_id(8070450532247928832), S2CellId.from_id(10376293541461622784), S2CellId.from_id(12682136550675316736)]
expect query_cells.map(|c| (u1_region().contains_cell(c), u1_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| u1_region().contains_point(p)) == [Bool.True, Bool.False, Bool.False, Bool.False, Bool.False, Bool.True]
expect u1_coverer.covering(u1_region()) == [S2CellId.from_id(1152921504606846976)]
expect u1_coverer.interior_covering(u1_region()) == []

# U2 empty (S2RegionUnionTest.Basic, the empty union).
u2_region : () -> S2RegionUnion
u2_region = || S2RegionUnion.new([])

u2_coverer : S2RegionCoverer
u2_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(30)

expect u2_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(1.0, 0.0), S1Interval.new(3.1415926535897931, -3.1415926535897931)), 1.0e-14)
expect u2_region().cap_bound().center().approx_eq(S2Point.new(1.0, 0.0, 0.0), 1.0e-14)
expect (u2_region().cap_bound().radius().length2() - -1.0).abs() < 1.0e-14
expect u2_region().cell_union_bound() == [S2CellId.from_id(1152921504606846980), S2CellId.from_id(1152921504606846972), S2CellId.from_id(1921535841011411628), S2CellId.from_id(384307168202282324)]
expect query_cells.map(|c| (u2_region().contains_cell(c), u2_region().may_intersect_cell(c))) == [(Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| u2_region().contains_point(p)) == [Bool.False, Bool.False, Bool.False, Bool.False, Bool.False, Bool.False]
expect u2_coverer.covering(u2_region()) == []
expect u2_coverer.interior_covering(u2_region()) == []

# U3 two caps.
u3_region : () -> S2RegionUnion
u3_region = || S2RegionUnion.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(12.0, 14.0).to_point(), S1Angle.from_degrees(5.0)))])

u3_coverer : S2RegionCoverer
u3_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect u3_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.087266462599716502, 0.29670597283903599), S1Interval.new(0.085916728840689599, 0.33356727505434614)), 1.0e-14)
expect u3_region().cap_bound().center().approx_eq(S2Point.new(0.96011449430933171, 0.20438220348291097, 0.1908089953765448), 1.0e-14)
expect (u3_region().cap_bound().radius().length2() - 0.025930781037318842).abs() < 1.0e-14
expect u3_region().cell_union_bound() == [S2CellId.from_id(1441151880758558720), S2CellId.from_id(864691128455135232), S2CellId.from_id(2017612633061982208), S2CellId.from_id(288230376151711744)]
expect query_cells.map(|c| (u3_region().contains_cell(c), u3_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| u3_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.True, Bool.False, Bool.False]
expect u3_coverer.covering(u3_region()) == [S2CellId.from_id(1167839678372511744), S2CellId.from_id(1168138745535266816), S2CellId.from_id(1175439502743699456), S2CellId.from_id(1214845999483191296), S2CellId.from_id(1220475499017404416), S2CellId.from_id(1242993497154256896), S2CellId.from_id(1274518694545850368), S2CellId.from_id(1282048150172860416)]
expect u3_coverer.interior_covering(u3_region()) == [S2CellId.from_id(1176565402650542080), S2CellId.from_id(1223853198737932288), S2CellId.from_id(1226104998551617536), S2CellId.from_id(1230608598178988032), S2CellId.from_id(1232860397992673280), S2CellId.from_id(1242149072224124928), S2CellId.from_id(1271985419755454464), S2CellId.from_id(1273392794639007744)]

# U4 cap, rect and cell.
u4_region : () -> S2RegionUnion
u4_region = || S2RegionUnion.new([S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 10.0).to_point(), S1Angle.from_degrees(5.0))), S2Region.from(S2LatLngRect.new(R1Interval.new(0.1, 0.3), S1Interval.new(0.1, 0.35))), S2Region.from_cell(S2Cell.from_cell_id(S2CellId.from_id(5170132372221329408)))])

u4_coverer : S2RegionCoverer
u4_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect u4_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.087266462599716502, 0.96850898065993285), S1Interval.new(-4.4408920985006262e-16, 0.34999999999999998)), 1.0e-14)
expect u4_region().cap_bound().center().approx_eq(S2Point.new(0.85067864183184105, 0.1504073142831078, 0.50370972607373476), 1.0e-14)
expect (u4_region().cap_bound().radius().length2() - 0.21731450384411466).abs() < 1.0e-14
expect u4_region().cell_union_bound() == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880)]
expect query_cells.map(|c| (u4_region().contains_cell(c), u4_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.True, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| u4_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.True, Bool.False, Bool.False]
expect u4_coverer.covering(u4_region()) == [S2CellId.from_id(1167839678372511744), S2CellId.from_id(1168138745535266816), S2CellId.from_id(1175439502743699456), S2CellId.from_id(1211468299762663424), S2CellId.from_id(1220475499017404416), S2CellId.from_id(1242993497154256896), S2CellId.from_id(1279022294173220864), S2CellId.from_id(5170132372221329408)]
expect u4_coverer.interior_covering(u4_region()) == [S2CellId.from_id(1176565402650542080), S2CellId.from_id(1214845999483191296), S2CellId.from_id(1217097799296876544), S2CellId.from_id(1223853198737932288), S2CellId.from_id(1229482698272145408), S2CellId.from_id(1235112197806358528), S2CellId.from_id(1241867597247414272), S2CellId.from_id(5170132372221329408)]

# U5 a point, a cap and a loop.
u5_region : () -> S2RegionUnion
u5_region = || S2RegionUnion.new([S2Region.from(S2PointRegion.new(S2LatLng.from_degrees(10.0, 10.0).to_point())), S2Region.from_cap(S2Cap.from_center_angle(S2LatLng.from_degrees(-40.0, 100.0).to_point(), S1Angle.from_degrees(20.0))), S2Region.from(S2Loop.from_points([S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 20.0).to_point(), S2LatLng.from_degrees(20.0, 0.0).to_point()]))])

u5_coverer : S2RegionCoverer
u5_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect u5_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(-1.0471975511965979, 0.34906585039886634), S1Interval.new(0.0, 2.2081519137860366)), 1.0e-14)
expect u5_region().cap_bound().center().approx_eq(S2Point.new(0.42282394206297613, 0.83919135814056978, -0.34202014332566855), 1.0e-14)
expect (u5_region().cap_bound().radius().length2() - 1.4393064803846483).abs() < 1.0e-14
expect u5_region().cell_union_bound() == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880), S2CellId.from_id(8070450532247928832), S2CellId.from_id(10376293541461622784), S2CellId.from_id(12682136550675316736)]
expect query_cells.map(|c| (u5_region().contains_cell(c), u5_region().may_intersect_cell(c))) == [(Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.True)]
expect query_points.map(|p| u5_region().contains_point(p)) == [Bool.False, Bool.False, Bool.True, Bool.False, Bool.False, Bool.False]
expect u5_coverer.covering(u5_region()) == [S2CellId.from_id(384307145295790080), S2CellId.from_id(1080863910568919040), S2CellId.from_id(1224979098644774912), S2CellId.from_id(1945555039024054272), S2CellId.from_id(2594073385365405696), S2CellId.from_id(3170534137668829184), S2CellId.from_id(12393906174523604992), S2CellId.from_id(12898309332789100544)]
expect u5_coverer.interior_covering(u5_region()) == [S2CellId.from_id(2751699372323373056), S2CellId.from_id(2864289363007635456), S2CellId.from_id(2900318160026599424), S2CellId.from_id(2936346957045563392), S2CellId.from_id(3008404551083491328), S2CellId.from_id(12344366578622529536), S2CellId.from_id(12447949370052050944), S2CellId.from_id(12483978167071014912)]

# U6 cell union and polyline.
u6_region : () -> S2RegionUnion
u6_region = || S2RegionUnion.new([S2Region.from(S2CellUnion.from_ids([1152921504606846976, 5170132372221329408])), S2Region.from(S2Polyline.from_points([S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(10.0, 10.0).to_point()]))])

u6_coverer : S2RegionCoverer
u6_coverer = S2RegionCoverer.default().with_max_cells(8).with_max_level(12)

expect u6_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(-0.7853981633974485, 0.96850898065993285), S1Interval.new(-0.78539816339744828, 0.78539816339744828)), 1.0e-14)
expect u6_region().cap_bound().center().approx_eq(S2Point.new(0.99581173044518312, 0.0, 0.091427553329234051), 1.0e-14)
expect (u6_region().cap_bound().radius().length2() - 1.1334863554476091).abs() < 1.0e-14
expect u6_region().cell_union_bound() == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(3458764513820540928), S2CellId.from_id(5764607523034234880), S2CellId.from_id(8070450532247928832), S2CellId.from_id(10376293541461622784), S2CellId.from_id(12682136550675316736)]
expect query_cells.map(|c| (u6_region().contains_cell(c), u6_region().may_intersect_cell(c))) == [(Bool.True, Bool.True), (Bool.True, Bool.True), (Bool.False, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| u6_region().contains_point(p)) == [Bool.True, Bool.True, Bool.True, Bool.True, Bool.False, Bool.True]
expect u6_coverer.covering(u6_region()) == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(5170132372221329408)]
expect u6_coverer.interior_covering(u6_region()) == [S2CellId.from_id(1152921504606846976), S2CellId.from_id(5170132372221329408)]

# U7 one cell.
u7_region : () -> S2RegionUnion
u7_region = || S2RegionUnion.new([S2Region.from_cell(S2Cell.from_cell_id(S2CellId.from_id(5170132372221329408)))])

u7_coverer : S2RegionCoverer
u7_coverer = S2RegionCoverer.default().with_max_cells(4).with_max_level(12)

expect u7_region().rect_bound().approx_eq(S2LatLngRect.new(R1Interval.new(0.7767604976861231, 0.96850898065993285), S1Interval.new(-4.4408920985006262e-16, 0.26625204915092582)), 1.0e-14)
expect u7_region().cap_bound().center().approx_eq(S2Point.new(0.63712279461079568, 0.085322263712798316, 0.76602523189660898), 1.0e-14)
expect (u7_region().cap_bound().radius().length2() - 0.017297644581297088).abs() < 1.0e-14
expect u7_region().cell_union_bound() == [S2CellId.from_id(4899916394579099648), S2CellId.from_id(1441151880758558720), S2CellId.from_id(5476377146882523136), S2CellId.from_id(864691128455135232)]
expect query_cells.map(|c| (u7_region().contains_cell(c), u7_region().may_intersect_cell(c))) == [(Bool.False, Bool.False), (Bool.True, Bool.True), (Bool.False, Bool.False), (Bool.False, Bool.False), (Bool.False, Bool.False)]
expect query_points.map(|p| u7_region().contains_point(p)) == [Bool.False, Bool.False, Bool.False, Bool.False, Bool.False, Bool.False]
expect u7_coverer.covering(u7_region()) == [S2CellId.from_id(5170132372221329408)]
expect u7_coverer.interior_covering(u7_region()) == [S2CellId.from_id(5170132372221329408)]

# `add`, `num_regions`, `region_at` and `regions` (upstream's Add, num_regions
# and region). S2RegionUnionTest.Basic adds a third point to a union of two.
expect {
	a = S2LatLng.from_degrees(35.0, 40.0).to_point()
	b = S2LatLng.from_degrees(-35.0, -40.0).to_point()
	c = S2LatLng.from_degrees(10.0, 10.0).to_point()
	two = S2RegionUnion.new([S2Region.from(S2PointRegion.new(a)), S2Region.from(S2PointRegion.new(b))])
	three = two.add(S2Region.from(S2PointRegion.new(c)))
	two.num_regions() == 2
		and three.num_regions() == 3
		and three.regions().len() == 3
		and !two.contains_point(c)
		and three.contains_point(c)
		and three.region_at(2).map_ok(|region| region.contains_point(c)) == Ok(Bool.True)
		and three.region_at(3).is_err()
}
# S2RegionUnionTest.Basic: the empty union has an empty cap bound and an empty
# rectangle bound.
expect S2RegionUnion.new([]).cap_bound() == S2Cap.empty() and S2RegionUnion.new([]).rect_bound() == S2LatLngRect.empty()
# A union can be a member of another union.
expect {
	a = S2LatLng.from_degrees(35.0, 40.0).to_point()
	inner = S2RegionUnion.new([S2Region.from(S2PointRegion.new(a))])
	S2RegionUnion.new([S2Region.from(inner)]).contains_point(a)
}

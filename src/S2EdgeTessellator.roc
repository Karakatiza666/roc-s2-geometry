import R2Point
import S1Angle
import S1ChordAngle
import S2Edge
import S2LatLng
import S2Point
import S2Projection

## Turns an edge between two points into a chain of edges that stays near it.
## Upstream's `S2EdgeTessellator`.
##
## An edge on the sphere is a geodesic, and an edge in the plane of a map
## projection is a straight line. They are different curves between the same
## two ends, and a map shows a polygon right only if it follows the edges
## the polygon means.
##
## - `append_projected` takes a geodesic edge and appends the vertices of a
##   chain of straight planar edges, which stays within the tolerance of the
##   geodesic.
## - `append_unprojected` takes a straight planar edge and appends the
##   vertices of a chain of geodesic edges, which stays within the tolerance
##   of the straight line.
##
##     proj = S2Projection.plate_carree(180.0)
##     tess = S2EdgeTessellator.new(proj, S1Angle.from_degrees(0.01))
##     vertices = tess.append_projected([], a, b)
##
## Both functions can be called again with their own result to add more
## edges. The first call adds all the vertices of the first edge, and each
## later call omits the first vertex of its edge, which must be the last
## vertex that is already there. When the projection wraps, every vertex is
## as close as it can be to the one before it, so a vertex can lie outside
## the usual range of coordinates. The edge from 0:170 to 0:-170 has the
## vertices `(170, 0)` and `(190, 0)`.
##
## To make a loop from the result of `append_unprojected`, drop the last
## vertex, which repeats the first.
S2EdgeTessellator := { projection : S2Projection, scaled_tolerance : S1ChordAngle }.{

	## The smallest tolerance that works: 1e-13 radians, a distance of less
	## than a micrometre on the Earth. Anything smaller is much finer than
	## the errors of the projection and the interpolation.
	min_tolerance : () -> S1Angle
	min_tolerance = || S1Angle.from_radians(1.0e-13)

	## A tessellator for the projection, with the given tolerance: the
	## largest distance on the sphere between an edge and its chain. A
	## tolerance below `min_tolerance` is raised to it.
	new : S2Projection, S1Angle -> S2EdgeTessellator
	new = |projection, tolerance| {
		floor = S2EdgeTessellator.min_tolerance()
		used = if (tolerance < floor) floor else tolerance
		# Instead of scaling the error estimate, the tolerance is scaled by
		# a constant, as upstream does. See the algorithm notes there.
		{
			projection: projection,
			scaled_tolerance: S1ChordAngle.from_angle(S1Angle.from_radians(scale_factor * used.radians())),
		}
	}

	## Appends the projected vertices of the geodesic edge from `a` to `b`
	## to `vertices`, and returns the longer list.
	##
	## When `vertices` is not empty, its last vertex should be the projection
	## of `a`.
	append_projected : S2EdgeTessellator, List(R2Point), S2Point, S2Point -> List(R2Point)
	append_projected = |tess, vertices, a, b| {
		proj = tess.projection
		projected_a = proj.project(a)
		start =
			match vertices.last() {
				Ok(previous) => (proj.wrap_destination(previous, projected_a), vertices)
				Err(_) => (projected_a, vertices.append(projected_a))
			}
		(pa, so_far) = start
		projected_edge(tess, pa, a, proj.project(b), b, so_far)
	}

	## Appends the vertices of the geodesic chain for the planar edge from
	## `pa` to `pb` to `vertices`, and returns the longer list.
	##
	## When `vertices` is not empty, its last vertex should be the point of
	## `pa`.
	append_unprojected : S2EdgeTessellator, List(S2Point), R2Point, R2Point -> List(S2Point)
	append_unprojected = |tess, vertices, pa, pb| {
		proj = tess.projection
		a = proj.unproject(pa)
		b = proj.unproject(pb)
		so_far = if (vertices.is_empty()) vertices.append(a) else vertices
		unprojected_edge(tess, pa, a, pb, b, so_far)
	}
}

## The fraction at which an edge and its chain are compared, a distance from
## either end. It is the root of the equation in upstream's notes, and the
## two error curves they describe have the same value there.
interpolation_fraction : F64
interpolation_fraction = 0.31215691082248312

## The value of those two curves at that fraction. The error at the fractions
## is divided by it, or the tolerance is multiplied by it.
scale_factor : F64
scale_factor = 0.83829992569888509

## An estimate of the largest distance between the geodesic from `a` to `b`
## and the planar edge from `pa` to `pb`: the larger of the distances at two
## fractions along them. An edge of more than 90 degrees is always too long.
estimate_max_error : S2EdgeTessellator, R2Point, S2Point, R2Point, S2Point -> S1ChordAngle
estimate_max_error = |tess, pa, a, pb, b| {
	if a.dot(b) < -1.0e-14 {
		return S1ChordAngle.infinity()
	}
	proj = tess.projection
	t1 = interpolation_fraction
	t2 = 1.0 - interpolation_fraction
	mid1 = S2Edge.interpolate(a, b, t1)
	mid2 = S2Edge.interpolate(a, b, t2)
	pmid1 = proj.unproject(proj.interpolate(t1, pa, pb))
	pmid2 = proj.unproject(proj.interpolate(t2, pa, pb))
	S1ChordAngle.from_points(mid1, pmid1).max(S1ChordAngle.from_points(mid2, pmid2))
}

## Splits the geodesic edge `a` to `b` until each part is close enough to its
## planar edge, and appends the planar vertices after the first. The
## recursion is at most about 45 deep, because every split halves the edge
## and the tolerance has a lower limit.
projected_edge : S2EdgeTessellator, R2Point, S2Point, R2Point, S2Point, List(R2Point) -> List(R2Point)
projected_edge = |tess, pa, a, pb_in, b, vertices| {
	proj = tess.projection
	pb = proj.wrap_destination(pa, pb_in)
	if estimate_max_error(tess, pa, a, pb, b).is_lte(tess.scaled_tolerance) {
		vertices.append(pb)
	} else {
		mid = (a + b).normalize()
		pmid = proj.wrap_destination(pa, proj.project(mid))
		first_half = projected_edge(tess, pa, a, pmid, mid, vertices)
		projected_edge(tess, pmid, mid, pb, b, first_half)
	}
}

## Splits the planar edge `pa` to `pb` until each part is close enough to its
## geodesic, and appends the points on the sphere after the first.
unprojected_edge : S2EdgeTessellator, R2Point, S2Point, R2Point, S2Point, List(S2Point) -> List(S2Point)
unprojected_edge = |tess, pa, a, pb_in, b, vertices| {
	proj = tess.projection
	pb = proj.wrap_destination(pa, pb_in)
	if estimate_max_error(tess, pa, a, pb, b).is_lte(tess.scaled_tolerance) {
		vertices.append(b)
	} else {
		pmid = proj.interpolate(0.5, pa, pb)
		mid = proj.unproject(pmid)
		first_half = unprojected_edge(tess, pa, a, pmid, mid, vertices)
		unprojected_edge(tess, pmid, mid, pb, b, first_half)
	}
}

# Helpers of the tests below.
tess_projected : S2Projection, S1Angle, List(S2Point) -> List(R2Point)
tess_projected = |proj, tolerance, chain| {
	tess = S2EdgeTessellator.new(proj, tolerance)
	(0..<chain.len().minus_wrap(1)).iter().fold(
		[],
		|vertices, i| tess.append_projected(vertices, chain.get(i) ?? S2Point.zero(), chain.get(i + 1) ?? S2Point.zero()),
	)
}

tess_unprojected : S2Projection, S1Angle, List(R2Point) -> List(S2Point)
tess_unprojected = |proj, tolerance, chain| {
	tess = S2EdgeTessellator.new(proj, tolerance)
	(0..<chain.len().minus_wrap(1)).iter().fold(
		[],
		|vertices, i| tess.append_unprojected(vertices, chain.get(i) ?? R2Point.origin(), chain.get(i + 1) ?? R2Point.origin()),
	)
}

## True when there are `n` vertices and the sampled ones agree to within the
## rounding differences of the port's own trigonometry.
matches_r2 : List(R2Point), U64, List((U64, R2Point)) -> Bool
matches_r2 = |vertices, n, samples|
	vertices.len() == n
		and samples.all(
			|(i, expected)| match vertices.get(i) {
				Ok(actual) => actual.approx_eq(expected, 1.0e-11)
				Err(_) => Bool.False
			},
		)

matches_s2 : List(S2Point), U64, List((U64, S2Point)) -> Bool
matches_s2 = |vertices, n, samples|
	vertices.len() == n
		and samples.all(
			|(i, expected)| match vertices.get(i) {
				Ok(actual) => actual.approx_eq(expected, 1.0e-13)
				Err(_) => Bool.False
			},
		)

# Upstream's s2edge_tessellator_test.cc cases, through tools/s2_oracle.cc: the
# cases named in the comments below, and a few more. Each compares the number
# of vertices exactly and the vertices to within the one-ulp differences that
# the port's own trigonometry and the fdlibm `exp` and `log` can make.
# ProjectedNoTessellation.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01), [S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0)]) |> matches_r2(2, [(0, R2Point.new(0.0, 0.0)), (1, R2Point.new(90.0, 0.0))])
# ProjectedWrapping.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01), [S2LatLng.from_degrees(0.0, -170.0).to_point(), S2LatLng.from_degrees(0.0, 170.0).to_point()]) |> matches_r2(2, [(0, R2Point.new(-170.0, 0.0)), (1, R2Point.new(-190.0, 0.0))])
# ProjectedWrappingMultipleCrossings.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_e7(1), [S2LatLng.from_degrees(0.0, 160.0).to_point(), S2LatLng.from_degrees(0.0, -40.0).to_point(), S2LatLng.from_degrees(0.0, 120.0).to_point(), S2LatLng.from_degrees(0.0, -80.0).to_point(), S2LatLng.from_degrees(10.0, 120.0).to_point(), S2LatLng.from_degrees(10.0, -40.0).to_point(), S2LatLng.from_degrees(0.0, 160.0).to_point()]) |> matches_r2(68801, [(0, R2Point.new(160.0, 0.0)), (6255, R2Point.new(574.96998886690369, 25.049367189233411)), (12509, R2Point.new(541.44106185300052, 27.012674470077371)), (18764, R2Point.new(494.10838268608779, 16.124445407571297)), (25018, R2Point.new(453.49473952632167, 31.135075396420003)), (31273, R2Point.new(420.23086482019119, 43.614859023952199)), (37527, R2Point.new(379.80634473632074, 43.621700804513672)), (43782, R2Point.new(346.53188299381782, 31.150990037607322)), (50036, R2Point.new(305.94724366919877, 16.102522535669305)), (56291, R2Point.new(258.59128017534579, 27.010701137442435)), (62545, R2Point.new(225.06129039172515, 25.054950749768057)), (68800, R2Point.new(160.0, 0.0))])
# InfiniteRecursionBug.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.5696123057604772e-10), [S2LatLng.from_degrees(3.0, 21.0).to_point(), S2LatLng.from_degrees(1.0, -159.0).to_point()]) |> matches_r2(36, [(0, R2Point.new(21.0, 3.0000000000000004)), (1, R2Point.new(21.000000000000071, 47.000000000000021)), (2, R2Point.new(21.000000000000178, 69.000000000000028)), (3, R2Point.new(21.000000000000387, 80.000000000000043)), (4, R2Point.new(21.000000000000863, 85.500000000000043)), (5, R2Point.new(21.00000000000222, 88.250000000000028)), (6, R2Point.new(21.000000000010356, 89.625000000000043)), (7, R2Point.new(21.000000000124235, 89.968750000000028)), (8, R2Point.new(21.000000000397549, 89.990234375000043)), (9, R2Point.new(21.000000000883432, 89.995605468750028)), (10, R2Point.new(21.00000000227168, 89.998291015625028)), (11, R2Point.new(21.00000001060117, 89.999633789062543)), (12, R2Point.new(21.00000012721399, 89.999969482421903)), (13, R2Point.new(21.000000407084766, 89.999990463256864)), (14, R2Point.new(21.000000904632824, 89.999995708465605)), (15, R2Point.new(21.000002326198718, 89.999998331069989)), (16, R2Point.new(21.000010855594827, 89.999999642372174)), (17, R2Point.new(21.000130267275456, 89.99999997019772)), (18, R2Point.new(21.000416856337662, 89.999999990686817)), (19, R2Point.new(200.99583160561659, 89.999999999068649)), (20, R2Point.new(200.99965262206572, 89.999999988824101)), (21, R2Point.new(200.99992556169158, 89.999999947845893)), (22, R2Point.new(200.99997105175729, 89.999999865889521)), (23, R2Point.new(200.99998697328897, 89.999999701976748)), (24, R2Point.new(200.99999592915248, 89.999999046325655)), (25, R2Point.new(200.99999966076268, 89.999988555908175)), (26, R2Point.new(200.99999992730628, 89.999946594238253)), (27, R2Point.new(200.99999997173023, 89.999862670898409)), (28, R2Point.new(200.99999998727858, 89.999694824218722)), (29, R2Point.new(200.99999999602454, 89.999023437499972)), (30, R2Point.new(200.99999999966872, 89.988281249999972)), (31, R2Point.new(200.999999999929, 89.945312499999972)), (32, R2Point.new(200.99999999997237, 89.859374999999972)), (33, R2Point.new(200.99999999998758, 89.687499999999972)), (34, R2Point.new(200.99999999999613, 88.999999999999972)), (35, R2Point.new(201.0, 1.0))])
# ProjectedAccuracy.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_e7(1), [S2LatLng.from_degrees(-89.999, -170.0).to_point(), S2LatLng.from_degrees(50.0, 100.0).to_point()]) |> matches_r2(912, [(0, R2Point.new(-170.0, -89.998999999999995)), (83, R2Point.new(-228.02869560268687, -89.998111343203192)), (166, R2Point.new(-249.88762083944647, -89.994303907753064)), (248, R2Point.new(-256.7512673850207, -89.982347730104095)), (331, R2Point.new(-258.90420858567035, -89.947652780244908)), (414, R2Point.new(-259.65930725744892, -89.83123480946756)), (497, R2Point.new(-259.88705732166994, -89.487303691526961)), (580, R2Point.new(-259.96237586006873, -88.427734036384209)), (663, R2Point.new(-259.98735571244418, -85.009765504628476)), (745, R2Point.new(-259.99501418301918, -75.234374947187405)), (828, R2Point.new(-259.99789442055663, -42.421874974759724)), (911, R2Point.new(-260.0, 50.0))])
# ProjectedAccuracyMidpointEquator.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.5696098420815538e-07), [S2LatLng.from_degrees(50.0, 80.0).to_point(), S2LatLng.from_degrees(-50.0, -80.0).to_point()]) |> matches_r2(3025, [(0, R2Point.new(80.0, 50.0)), (275, R2Point.new(63.481546184385572, 47.277085585281753)), (550, R2Point.new(49.137378352691869, 42.464872949598302)), (825, R2Point.new(37.123892058527709, 36.143178344326294)), (1100, R2Point.new(27.031567763449623, 28.810146359909165)), (1375, R2Point.new(11.116326425489845, 13.133111764424619)), (1649, R2Point.new(-11.116326425489845, -13.133111764424619)), (1924, R2Point.new(-27.031567763449623, -28.810146359909165)), (2199, R2Point.new(-37.123892058527709, -36.143178344326294)), (2474, R2Point.new(-49.137378352691869, -42.464872949598302)), (2749, R2Point.new(-63.481546184385572, -47.277085585281753)), (3024, R2Point.new(-80.0, -50.0))])
# ProjectedAccuracyCrossEquator.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_e7(1), [S2LatLng.from_degrees(-20.0, -20.0).to_point(), S2LatLng.from_degrees(20.0, 20.0).to_point()]) |> matches_r2(5385, [(0, R2Point.new(-20.0, -20.0)), (489, R2Point.new(-17.444464330473956, -17.693750584446263)), (979, R2Point.new(-14.949156406918577, -15.350530849924898)), (1468, R2Point.new(-12.514515111439872, -12.985052714444169)), (1958, R2Point.new(-8.5980263255928921, -9.0397641000601663)), (2447, R2Point.new(-3.9567315784182955, -4.1997819526161067)), (2937, R2Point.new(3.9567315784182955, 4.1997819526161067)), (3426, R2Point.new(8.5980263255928921, 9.0397641000601663)), (3916, R2Point.new(12.514515111439872, 12.985052714444169)), (4405, R2Point.new(14.949156406918577, 15.350530849924898)), (4895, R2Point.new(17.444464330473956, 17.693750584446263)), (5384, R2Point.new(20.0, 20.0))])
# ProjectedAccuracySeattleToNewYork.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.5696098420815538e-07), [S2LatLng.from_degrees(47.6062, -122.3321).to_point(), S2LatLng.from_degrees(40.7128, -74.0059).to_point()]) |> matches_r2(1025, [(0, R2Point.new(-122.33210000000001, 47.606200000000001)), (93, R2Point.new(-117.65445051831881, 47.885650372483752)), (186, R2Point.new(-112.94354758885864, 47.973529069992196)), (279, R2Point.new(-108.23419854311634, 47.868595879450595)), (372, R2Point.new(-103.56112372810196, 47.572330529296877)), (465, R2Point.new(-98.957041881666569, 47.088834006244646)), (559, R2Point.new(-94.403190380485626, 46.416467588815649)), (652, R2Point.new(-90.020850885113518, 45.57804231232538)), (745, R2Point.new(-85.779618269853387, 44.577294296789489)), (838, R2Point.new(-81.692445750783605, 43.425159126337775)), (931, R2Point.new(-77.766926375951499, 42.13311816820962)), (1024, R2Point.new(-74.005899999999997, 40.712800000000001))])
# Mercator cross equator.
expect tess_projected(S2Projection.mercator(180.0), S1Angle.from_radians(1.5696098420815538e-05), [S2LatLng.from_degrees(-30.0, -100.0).to_point(), S2LatLng.from_degrees(40.0, 60.0).to_point()]) |> matches_r2(248, [(0, R2Point.new(-100.0, -31.472923730945382)), (22, R2Point.new(-88.17521921406491, -21.676243060528332)), (45, R2Point.new(-74.148921000134635, -8.0798350329356072)), (67, R2Point.new(-52.031402499376604, 14.595838159516513)), (90, R2Point.new(-40.743938006935331, 24.989081209059925)), (112, R2Point.new(-28.289583514803013, 34.641265123854772)), (135, R2Point.new(-12.740189095768249, 43.685772143290656)), (157, R2Point.new(4.9192679237297838, 49.950974795397897)), (180, R2Point.new(18.639555354075767, 52.013685443041105)), (202, R2Point.new(28.608338746439177, 52.017848210187161)), (225, R2Point.new(42.331926979242141, 49.965953395213774)), (247, R2Point.new(59.999999999999993, 43.711503213210868))])
# Mercator long edge.
expect tess_projected(S2Projection.mercator(180.0), S1Angle.from_radians(1.5696098420815538e-05), [S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 179.0).to_point()]) |> matches_r2(3, [(0, R2Point.new(0.0, 0.0)), (1, R2Point.new(89.500000000000114, 0.0)), (2, R2Point.new(179.0, 0.0))])
# Mercator single point edge.
expect tess_projected(S2Projection.mercator(180.0), S1Angle.from_radians(1.5696098420815538e-07), [S2LatLng.from_degrees(12.0, 34.0).to_point(), S2LatLng.from_degrees(12.0, 34.0).to_point()]) |> matches_r2(2, [(0, R2Point.new(34.000000000000007, 12.088704312420576)), (1, R2Point.new(34.000000000000007, 12.088704312420576))])
# UnwrappingDcheckRegression.
expect tess_projected(S2Projection.mercator(0.5), S1Angle.from_e7(1), [S2LatLng.from_degrees(-16.876721435218865, -179.98654798480896).to_point(), S2LatLng.from_degrees(-16.874909244632697, -179.99188923836962).to_point(), S2LatLng.from_degrees(-16.880241814330226, -179.99085868846697).to_point(), S2LatLng.from_degrees(-16.88376210404762, -179.9951695537554).to_point(), S2LatLng.from_degrees(-16.881949690252107, 179.99948907462112).to_point(), S2LatLng.from_degrees(-16.87661707140543, 179.99845878814452).to_point(), S2LatLng.from_degrees(-16.880137137875717, 179.99414780493106).to_point(), S2LatLng.from_degrees(-16.878324446969305, 179.98880663726433).to_point(), S2LatLng.from_degrees(-16.87299177440956, 179.98777667253748).to_point(), S2LatLng.from_degrees(-16.869471841739493, 179.992087611973).to_point(), S2LatLng.from_degrees(-16.86765909723297, 179.9867467660618).to_point(), S2LatLng.from_degrees(-16.862326415537094, 179.98571691783295).to_point(), S2LatLng.from_degrees(-16.858806527326653, 179.99002765202718).to_point(), S2LatLng.from_degrees(-16.860619186956175, 179.99536827827873).to_point(), S2LatLng.from_degrees(-16.85528654982854, 179.9943382248306).to_point(), S2LatLng.from_degrees(-16.85176648312914, 179.9986486362035).to_point(), S2LatLng.from_degrees(-16.84995390837456, 179.9933082296289).to_point()]) |> matches_r2(17, [(0, R2Point.new(-0.49996263329113605, -0.047572766172033466)), (1, R2Point.new(-0.49997747010658233, -0.04756750577670673)), (2, R2Point.new(-0.49997460746796385, -0.047582985211588179)), (3, R2Point.new(-0.49998658209376506, -0.047593204182170626)), (4, R2Point.new(-0.50000141923716357, -0.047587942942750518)), (5, R2Point.new(-0.50000428114404305, -0.04757246322520061)), (6, R2Point.new(-0.50001625609741374, -0.047582681351557791)), (7, R2Point.new(-0.50003109267426571, -0.047577419408745436)), (8, R2Point.new(-0.50003395368739589, -0.04756193983243346)), (9, R2Point.new(-0.5000219788556306, -0.047551722480999953)), (10, R2Point.new(-0.50003681453871729, -0.047546460679698456)), (11, R2Point.new(-0.50003967522824178, -0.047530981950665976)), (12, R2Point.new(-0.50002770096659122, -0.047520765304871045)), (13, R2Point.new(-0.50001286589367022, -0.047526026613371367)), (14, R2Point.new(-0.50001572715324827, -0.047510548590120334)), (15, R2Point.new(-0.50000375378832351, -0.047500331806633392)), (16, R2Point.new(-0.50001858825103085, -0.047495070990757865))])
# Random-looking pc100m.
expect tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.5696098420815538e-05), [S2LatLng.from_degrees(10.0, 10.0).to_point(), S2LatLng.from_degrees(-60.0, 150.0).to_point(), S2LatLng.from_degrees(30.0, -100.0).to_point()]) |> matches_r2(523, [(0, R2Point.new(10.0, 10.000000000000002)), (47, R2Point.new(30.421470880397109, -35.054991762307885)), (95, R2Point.new(48.058069735065487, -54.321091163364336)), (142, R2Point.new(67.673906580803575, -63.493511861729928)), (190, R2Point.new(93.613695046258059, -67.791808443077116)), (237, R2Point.new(122.92448454086095, -67.009267680108223)), (285, R2Point.new(146.27765692681626, -61.536826652229692)), (332, R2Point.new(167.74586978286027, -58.850971218418763)), (380, R2Point.new(192.55067808848892, -52.148322458021745)), (427, R2Point.new(215.76146861674272, -35.967262381073141)), (475, R2Point.new(235.0667150469082, -9.3638771149556472)), (522, R2Point.new(260.0, 29.999999999999996))])
# UnprojectedNoTessellation.
expect tess_unprojected(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01), [R2Point.new(0.0, 30.0), R2Point.new(0.0, 50.0)]) |> matches_s2(2, [(0, S2Point.new(0.86602540378443871, 0.0, 0.49999999999999994)), (1, S2Point.new(0.64278760968653936, 0.0, 0.76604444311897801))])
# UnprojectedWrapping.
expect tess_unprojected(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01), [R2Point.new(-170.0, 0.0), R2Point.new(170.0, 80.0)]) |> matches_s2(29, [(0, S2Point.new(-0.98480775301220802, -0.17364817766693028, 0.0)), (1, S2Point.new(-0.9846004965259324, -0.15154451077815803, 0.087155742747658166)), (2, S2Point.new(-0.97638258616504225, -0.12854320606946854, 0.17364817766693033)), (3, S2Point.new(-0.96018468987527972, -0.10515732604689247, 0.25881904510252074)), (4, S2Point.new(-0.93611680666285924, -0.081899608319089365, 0.34202014332566871)), (5, S2Point.new(-0.92118746978693766, -0.070477202702814615, 0.38268343236508978)), (6, S2Point.new(-0.90436731249515301, -0.05927536531784304, 0.42261826174069944)), (7, S2Point.new(-0.88569182938862745, -0.04835495351822338, 0.46174861323503391)), (8, S2Point.new(-0.86520113949555377, -0.037775497555895016, 0.49999999999999994)), (9, S2Point.new(-0.84293988347047144, -0.027594994566729217, 0.53729960834682389)), (10, S2Point.new(-0.81895710828501389, -0.017869707671990157, 0.57357643635104605)), (11, S2Point.new(-0.79330613973437336, -0.0086539708231119072, 0.60876142900872066)), (12, S2Point.new(-0.76604444311897801, -9.3813387527027308e-17, 0.64278760968653925)), (13, S2Point.new(-0.73723347249508098, 0.0080422886465118647, 0.67559020761566024)), (14, S2Point.new(-0.70693850892101251, 0.01542545313874317, 0.70710678118654746)), (15, S2Point.new(-0.67522848815765812, 0.022104691956557634, 0.73727733681012408)), (16, S2Point.new(-0.64217581831219051, 0.028038001740555606, 0.76604444311897801)), (17, S2Point.new(-0.60785618794312479, 0.033186325918850873, 0.79335334029123517)), (18, S2Point.new(-0.57234836517229015, 0.037513693790032422, 0.8191520442889918)), (19, S2Point.new(-0.53573398837523933, 0.040987349624112809, 0.84339144581288561)), (20, S2Point.new(-0.49809734904587288, 0.043577871373829104, 0.8660254037844386)), (21, S2Point.new(-0.45952516745357314, 0.045259278620438423, 0.88701083317822171)), (22, S2Point.new(-0.42010636173184152, 0.046009129411079534, 0.90630778703664994)), (23, S2Point.new(-0.37993181105626705, 0.045808605678750731, 0.92387953251128674)), (24, S2Point.new(-0.33909411358656849, 0.044642586970855838, 0.93969262078590832)), (25, S2Point.new(-0.29768733986237739, 0.042499712248031507, 0.95371695074822693)), (26, S2Point.new(-0.25580678235535087, 0.039372429551436217, 0.96592582628906831)), (27, S2Point.new(-0.21354870189105465, 0.035257033373789333, 0.97629600711993336)), (28, S2Point.new(-0.17101007166283441, 0.030153689607045807, 0.98480775301220802))])
# UnprojectedWrappingMultipleCrossings.
expect tess_unprojected(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01), [R2Point.new(179.97, 1.0), R2Point.new(-179.93, 1.0), R2Point.new(179.94, 2.0), R2Point.new(-179.86, 2.0), R2Point.new(179.91, 3.0), R2Point.new(-179.79, 3.0), R2Point.new(179.88, 4.0), R2Point.new(-179.72, 4.0), R2Point.new(179.85, 5.0)]) |> matches_s2(9, [(0, S2Point.new(-0.99984755809943315, 0.00052351900504780545, 0.017452406437283512)), (1, S2Point.new(-0.99984694895747273, -0.0012215440970422692, 0.017452406437283512)), (2, S2Point.new(-0.99939027904180677, 0.0010465594354626315, 0.034899496702500969)), (3, S2Point.new(-0.99938784358840038, -0.0024419700324337427, 0.034899496702500969)), (4, S2Point.new(-0.99862830274502079, 0.0015686429599426591, 0.052335956242943835)), (5, S2Point.new(-0.99862282715313677, -0.0036601602168321256, 0.052335956242943835)), (6, S2Point.new(-0.99756186235783717, 0.0020892917337437286, 0.069756473744125302)), (7, S2Point.new(-0.99755213836835799, -0.0048749982052616559, 0.069756473744125302)), (8, S2Point.new(-0.99619128418828695, 0.0026080286416982688, 0.087155742747658166))])
# UnprojectedAccuracy.
expect tess_unprojected(S2Projection.mercator(180.0), S1Angle.from_degrees(1e-05), [R2Point.new(0.0, 0.0), R2Point.new(89.999999, 179.0)]) |> matches_s2(2250, [(0, S2Point.new(1.0, 0.0, 0.0)), (204, S2Point.new(0.91501306780858138, 0.17690579479748242, 0.36256782194039172)), (409, S2Point.new(0.76653828485925324, 0.26765783310891605, 0.58376223089582802)), (613, S2Point.new(0.67366669052863848, 0.29614637198951888, 0.6771045092374125)), (818, S2Point.new(0.57961319729988037, 0.3112400943462586, 0.75311230582638999)), (1022, S2Point.new(0.48993038754246349, 0.31473847558390528, 0.81296242677605401)), (1227, S2Point.new(0.34649732803565775, 0.29935446214467204, 0.88900309766514529)), (1431, S2Point.new(0.22227622408209796, 0.26293565065456392, 0.93886001290004151)), (1636, S2Point.new(0.13234522616190053, 0.21851785010691652, 0.96681678217581979)), (1840, S2Point.new(0.071371708979722823, 0.17457454148090842, 0.9820538725671033)), (2045, S2Point.new(0.031698479916993698, 0.13485556113981639, 0.99035810896898158)), (2249, S2Point.new(1.5320461818446004e-09, 0.087779780700537255, 0.99613990488292636))])
# UnprojectedAccuracyCrossEquator.
expect tess_unprojected(S2Projection.mercator(180.0), S1Angle.from_degrees(1e-05), [R2Point.new(-10.0, -10.0), R2Point.new(10.0, 10.0)]) |> matches_s2(181, [(0, S2Point.new(0.96999632285828663, -0.17103652290791505, -0.17278206351636374)), (16, S2Point.new(0.976947040122079, -0.15036653117061541, -0.1515400511430072)), (33, S2Point.new(0.98336017159614297, -0.12809797705784878, -0.12881646320285048)), (49, S2Point.new(0.98846349308175807, -0.10689058768031556, -0.10730482333038806)), (65, S2Point.new(0.99376503382367853, -0.078756399771446758, -0.078920764342870653)), (82, S2Point.new(0.99892965255987065, -0.032701570865818541, -0.032713246545153889)), (98, S2Point.new(0.99892965255987065, 0.032701570865818541, 0.032713246545153847)), (115, S2Point.new(0.99376503382367853, 0.078756399771446758, 0.078920764342870667)), (131, S2Point.new(0.98846349308175807, 0.10689058768031556, 0.10730482333038804)), (147, S2Point.new(0.98336017159614297, 0.12809797705784878, 0.12881646320285045)), (164, S2Point.new(0.976947040122079, 0.15036653117061541, 0.1515400511430072)), (180, S2Point.new(0.96999632285828663, 0.17103652290791505, 0.17278206351636377))])
# UnprojectedAccuracyMidpointEquator.
expect tess_unprojected(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.5696098420815538e-07), [R2Point.new(80.0, 50.0), R2Point.new(-80.0, -50.0)]) |> matches_s2(2923, [(0, S2Point.new(0.11161889704894971, 0.63302222155948906, 0.76604444311897801)), (266, S2Point.new(0.25270945283389412, 0.67985570880043034, 0.68842875278409044)), (531, S2Point.new(0.40804913799523868, 0.68608181922645084, 0.60231855218668651)), (797, S2Point.new(0.56654058847549027, 0.64868736774836655, 0.5081697162696146)), (1063, S2Point.new(0.74118065919673159, 0.54813210242718446, 0.38755958086654652)), (1328, S2Point.new(0.94808348036678847, 0.26794551102211611, 0.17129774481496951)), (1594, S2Point.new(0.94808348036678847, -0.26794551102211611, -0.17129774481496951)), (1859, S2Point.new(0.74118065919673159, -0.54813210242718446, -0.38755958086654652)), (2125, S2Point.new(0.56654058847549027, -0.64868736774836655, -0.5081697162696146)), (2391, S2Point.new(0.40804913799523868, -0.68608181922645084, -0.60231855218668651)), (2656, S2Point.new(0.25270945283389412, -0.67985570880043034, -0.68842875278409044)), (2922, S2Point.new(0.11161889704894971, -0.63302222155948906, -0.76604444311897801))])
# UnprojectedAccuracyRandomCheck-like.
expect tess_unprojected(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.001), [R2Point.new(0.0, 45.5), R2Point.new(100.25, -60.75)]) |> matches_s2(207, [(0, S2Point.new(0.7009092642998509, 0.0, 0.71325044915418156)), (19, S2Point.new(0.78546801301061087, 0.10257813501881523, 0.61034230293600367)), (37, S2Point.new(0.83726555295490834, 0.21636412782953468, 0.50216825668661735)), (56, S2Point.new(0.8585231449959414, 0.3456409251642249, 0.37877481484108266)), (75, S2Point.new(0.82524384458851496, 0.53376245923821874, 0.18458123977462032)), (94, S2Point.new(0.59964520702098634, 0.78075620996090211, -0.17562848944361553)), (112, S2Point.new(0.41535047440117356, 0.83086423816035304, -0.37033579513859616)), (131, S2Point.new(0.2847404265586595, 0.82134851004246701, -0.49427675904720836)), (150, S2Point.new(0.16058974675698656, 0.77684537925783159, -0.60886960012984925)), (169, S2Point.new(0.051910140056826606, 0.70031187932565131, -0.71194705493783372)), (187, S2Point.new(-0.029591588912386873, 0.60297974250652409, -0.7972074811442792)), (206, S2Point.new(-0.086946996105798383, 0.48082318736746033, -0.87249600707279706))])
# pc zero length.
expect tess_unprojected(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.5696098420815538e-07), [R2Point.new(5.0, 5.0), R2Point.new(5.0, 5.0)]) |> matches_s2(2, [(0, S2Point.new(0.99240387650610407, 0.086824088833465166, 0.087155742747658166)), (1, S2Point.new(0.99240387650610407, 0.086824088833465166, 0.087155742747658166))])

# Upstream's ProjectedWrapping: the edge from 0:-170 to 0:170 goes the short
# way, so no x coordinate passes -170.
expect {
	a = S2LatLng.from_degrees(0.0, -170.0).to_point()
	b = S2LatLng.from_degrees(0.0, 170.0).to_point()
	vertices = S2EdgeTessellator.new(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01)).append_projected([], a, b)
	vertices.all(|v| v.x() <= -170.0)
}

# Upstream's UnprojectedWrapping: the planar edge from (-170, 0) to (170, 80)
# also goes the short way.
expect {
	vertices = S2EdgeTessellator.new(S2Projection.plate_carree(180.0), S1Angle.from_degrees(0.01)).append_unprojected([], R2Point.new(-170.0, 0.0), R2Point.new(170.0, 80.0))
	vertices.all(|v| S2LatLng.from_point(v).lng_degrees().abs() >= 170.0)
}

# Upstream's ProjectedWrappingMultipleCrossings: the loop crosses the 180
# degree meridian four times, and its x coordinates run from 160 to 640.
expect {
	loop = [
		S2LatLng.from_degrees(0.0, 160.0).to_point(),
		S2LatLng.from_degrees(0.0, -40.0).to_point(),
		S2LatLng.from_degrees(0.0, 120.0).to_point(),
		S2LatLng.from_degrees(0.0, -80.0).to_point(),
		S2LatLng.from_degrees(10.0, 120.0).to_point(),
		S2LatLng.from_degrees(10.0, -40.0).to_point(),
		S2LatLng.from_degrees(0.0, 160.0).to_point(),
	]
	vertices = tess_projected(S2Projection.plate_carree(180.0), S1Angle.from_e7(1), loop)
	xs = vertices.map(|v| v.x())
	vertices.first() == vertices.last()
		and xs.fold(1.0e9, |lowest, x| lowest.min(x)) == 160.0
		and xs.fold(-1.0e9, |highest, x| highest.max(x)) == 640.0
}

# Upstream's InfiniteRecursionBug: with a tolerance of one micrometre, this
# edge has 36 vertices.
expect {
	a = S2LatLng.from_degrees(3.0, 21.0).to_point()
	b = S2LatLng.from_degrees(1.0, -159.0).to_point()
	tess = S2EdgeTessellator.new(S2Projection.plate_carree(180.0), S1Angle.from_radians(1.0e-6 / 6371.0))
	tess.append_projected([], a, b).len() == 36
}

# A tolerance below the minimum is raised to it.
expect S2EdgeTessellator.min_tolerance() == S1Angle.from_radians(1.0e-13)
expect {
	a = S2LatLng.from_degrees(3.0, 21.0).to_point()
	b = S2LatLng.from_degrees(1.0, -159.0).to_point()
	proj = S2Projection.plate_carree(180.0)
	tiny = S2EdgeTessellator.new(proj, S1Angle.from_radians(1.0e-20))
	least = S2EdgeTessellator.new(proj, S2EdgeTessellator.min_tolerance())
	tiny.append_projected([], a, b) == least.append_projected([], a, b)
}

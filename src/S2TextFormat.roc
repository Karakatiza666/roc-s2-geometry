import Internal/S2Format
import R1Interval
import S1Interval
import S2CellId
import S2CellUnion
import S2LatLng
import S2LatLngRect
import S2Loop
import S2Point
import S2Polygon
import S2Polyline

## Reads and writes geometry as short text, for tests, logs and examples.
## Upstream's `s2textformat`.
##
## A position is `lat:lng` in degrees, and a list of them is separated by
## commas. A loop or a polyline is such a list, and a polygon is a list of
## loops separated by semicolons:
##
##     S2TextFormat.make_polygon("0:0, 0:5, 5:0; 1:1, 1:4, 4:1")
##
## The loop `empty` is the empty loop, `full` is the full loop, and a polygon
## written `empty` has no loops. A cell is written as its face, a slash and
## its child positions, like `2/033`.
##
## The `make_` and `parse_` functions give `Err(InvalidArgument(message))`
## for text they cannot read, with the same message as upstream. The
## `..._to_string` functions print every number with at most 15 significant
## digits and without trailing zeros, as upstream does with `"%.15g"`.
##
## Upstream's `make_lax_polygon`, `make_lax_polyline` and `make_index` are
## not here, because they build shapes and a shape index, which this package
## does not have.
S2TextFormat := [].{

	## Reads the points in `text`, a list of `lat:lng` positions separated by
	## commas. Empty parts between commas are skipped.
	parse_lat_lngs : Str -> Try(List(S2LatLng), [InvalidArgument(Str)])
	parse_lat_lngs = |text|
		text.split_on(",").keep_if(|piece| !piece.is_empty()).map_try(parse_lat_lng)

	## Reads the points in `text` as points on the sphere.
	parse_points : Str -> Try(List(S2Point), [InvalidArgument(Str)])
	parse_points = |text| {
		lat_lngs = S2TextFormat.parse_lat_lngs(text)?
		Ok(lat_lngs.map(S2LatLng.to_point))
	}

	## The one point in `text`.
	make_point : Str -> Try(S2Point, [InvalidArgument(Str)])
	make_point = |text| {
		points = S2TextFormat.parse_points(text)?
		match points {
			[point] => Ok(point)
			_ => Err(InvalidArgument("Expected 1 point, got ${points.len().to_str()}"))
		}
	}

	## The one position in `text`.
	make_lat_lng : Str -> Try(S2LatLng, [InvalidArgument(Str)])
	make_lat_lng = |text| {
		lat_lngs = S2TextFormat.parse_lat_lngs(text)?
		match lat_lngs {
			[lat_lng] => Ok(lat_lng)
			_ => Err(InvalidArgument("Expected 1 latlng, got ${lat_lngs.len().to_str()}"))
		}
	}

	## The smallest rectangle that contains every position in `text`. There
	## must be at least one.
	make_lat_lng_rect : Str -> Try(S2LatLngRect, [InvalidArgument(Str)])
	make_lat_lng_rect = |text| {
		lat_lngs = S2TextFormat.parse_lat_lngs(text)?
		match lat_lngs {
			[] => Err(InvalidArgument("No points found to construct S2LatLngRect"))
			[first, .. as rest] =>
				Ok(rest.fold(S2LatLngRect.from_point(first), |rect, lat_lng| rect.add_lat_lng(lat_lng)))
		}
	}

	## The cell that `text` names, such as `1/3` or `4/`.
	make_cell_id : Str -> Try(S2CellId, [InvalidArgument(Str)])
	make_cell_id = |text| parse_cell_id(text)

	## The cell union of the cells in `text`, separated by commas. The cells
	## are normalized.
	make_cell_union : Str -> Try(S2CellUnion, [InvalidArgument(Str)])
	make_cell_union = |text| {
		cells = split_skip_blank(text, ",").map_try(parse_cell_id)?
		Ok(S2CellUnion.from_cell_ids(cells))
	}

	## The loop through the positions in `text`, or the empty loop for the
	## text `empty` and the full loop for `full`.
	make_loop : Str -> Try(S2Loop, [InvalidArgument(Str)])
	make_loop = |text|
		if text == "empty" {
			Ok(S2Loop.empty())
		} else if text == "full" {
			Ok(S2Loop.full())
		} else {
			points = S2TextFormat.parse_points(text)?
			Ok(S2Loop.from_points(points))
		}

	## The polyline through the positions in `text`.
	make_polyline : Str -> Try(S2Polyline, [InvalidArgument(Str)])
	make_polyline = |text| {
		points = S2TextFormat.parse_points(text)?
		Ok(S2Polyline.from_points(points))
	}

	## The polygon of the loops in `text`, separated by semicolons.
	##
	## Each loop is normalized, so that it encloses less than half the
	## sphere, unless it is the full loop. The loops are then nested as
	## `S2Polygon.from_loops` does, so a hole is written in the same
	## direction as its shell. The text `empty` and the empty text give the
	## empty polygon.
	make_polygon : Str -> Try(S2Polygon, [InvalidArgument(Str)])
	make_polygon = |text| polygon_of(text, Bool.True)

	## Like `make_polygon`, but the loops are used as they are written and
	## are not normalized.
	make_verbatim_polygon : Str -> Try(S2Polygon, [InvalidArgument(Str)])
	make_verbatim_polygon = |text| polygon_of(text, Bool.False)

	## The text of a position, like `37.7749:-122.4194`.
	lat_lng_to_string : S2LatLng -> Str
	lat_lng_to_string = |lat_lng|
		"${number(lat_lng.lat_degrees())}:${number(lat_lng.lng_degrees())}"

	## The text of a point, as the position it has. A coordinate of negative
	## zero is written like a positive zero.
	point_to_string : S2Point -> Str
	point_to_string = |point| S2TextFormat.lat_lng_to_string(S2LatLng.from_point(point))

	## The text of some positions, separated by a comma and a space.
	lat_lngs_to_string : List(S2LatLng) -> Str
	lat_lngs_to_string = |lat_lngs| Str.join_with(lat_lngs.map(S2TextFormat.lat_lng_to_string), ", ")

	## The text of some points, separated by a comma and a space.
	points_to_string : List(S2Point) -> Str
	points_to_string = |points| Str.join_with(points.map(S2TextFormat.point_to_string), ", ")

	## The text of a rectangle: its low corner, then its high corner.
	lat_lng_rect_to_string : S2LatLngRect -> Str
	lat_lng_rect_to_string = |rect|
		"${S2TextFormat.lat_lng_to_string(rect.lo())}, ${S2TextFormat.lat_lng_to_string(rect.hi())}"

	## The text of a cell, like `2/033`.
	cell_id_to_string : S2CellId -> Str
	cell_id_to_string = |cell_id| cell_id.to_debug_str()

	## The text of the cells of a cell union, separated by a comma and a space.
	cell_union_to_string : S2CellUnion -> Str
	cell_union_to_string = |cell_union|
		Str.join_with(cell_union.cell_ids().map(S2TextFormat.cell_id_to_string), ", ")

	## The text of a loop: `empty`, `full`, or its vertices.
	loop_to_string : S2Loop -> Str
	loop_to_string = |loop|
		if loop.is_empty() {
			"empty"
		} else if loop.is_full() {
			"full"
		} else {
			S2TextFormat.points_to_string(loop.vertices())
		}

	## The text of a polyline: its vertices.
	polyline_to_string : S2Polyline -> Str
	polyline_to_string = |line| S2TextFormat.points_to_string(line.vertices())

	## The text of a polygon: `empty`, `full`, or its loops with a semicolon
	## and a newline between them. The vertices of each loop are written as
	## the loop stores them.
	polygon_to_string : S2Polygon -> Str
	polygon_to_string = |polygon| S2TextFormat.polygon_to_string_with(polygon, ";\n")

	## Like `polygon_to_string`, with the given text between the loops.
	polygon_to_string_with : S2Polygon, Str -> Str
	polygon_to_string_with = |polygon, loop_separator|
		if polygon.is_empty() {
			"empty"
		} else if polygon.is_full() {
			"full"
		} else {
			Str.join_with(
				(0..<polygon.num_loops()).iter().map(|i| S2TextFormat.points_to_string(polygon.loop_at(i).vertices())).collect(),
				loop_separator,
			)
		}
}

number : F64 -> Str
number = |x| S2Format.general(x, 15)

## The pieces of `text` between `separator`s, without the pieces that are
## blank, and with the whitespace at both ends of each piece removed.
split_skip_blank : Str, Str -> List(Str)
split_skip_blank = |text, separator|
	text.split_on(separator)
		.keep_if(|piece| !S2Format.is_blank(piece))
		.map(S2Format.strip_ascii_whitespace)

## One `lat:lng` part of a list of positions.
parse_lat_lng : Str -> Try(S2LatLng, [InvalidArgument(Str)])
parse_lat_lng = |piece|
	match piece.split_on(":") {
		[lat_text, lng_text] => {
			lat = S2Format.parse_double(lat_text) ? |_| InvalidArgument("Failed to parse latitude: ${lat_text}")
			lng = S2Format.parse_double(lng_text) ? |_| InvalidArgument("Failed to parse longitude: ${lng_text}")
			lat_lng = S2LatLng.from_degrees(lat, lng)
			if lat_lng.is_valid() {
				Ok(lat_lng)
			} else {
				Err(InvalidArgument("Invalid latlng coordinates: ${piece}"))
			}
		}
		_ => Err(InvalidArgument("Invalid latlng format (expected lat:lng): ${piece}"))
	}

## A cell written as its face, a slash and its child positions. Upstream's
## `S2CellId::FromDebugString` is strict about the form: one digit for the
## face, then the slash, then one digit from 0 to 3 for each level.
parse_cell_id : Str -> Try(S2CellId, [InvalidArgument(Str)])
parse_cell_id = |text| {
	bytes = text.to_utf8()
	well_formed =
		match bytes {
			[face, '/', .. as positions] =>
				face >= '0' and face <= '5'
					and positions.len() <= S2CellId.max_level
					and positions.all(|b| b >= '0' and b <= '3')
			_ => Bool.False
		}
	if well_formed {
		S2CellId.from_debug_str(text).map_err(|_| InvalidArgument("Invalid S2CellId: ${text}"))
	} else {
		Err(InvalidArgument("Invalid S2CellId: ${text}"))
	}
}

polygon_of : Str, Bool -> Try(S2Polygon, [InvalidArgument(Str)])
polygon_of = |text, normalize| {
	body = if (text == "empty") "" else text
	loops = split_skip_blank(body, ";").map_try(
		|loop_text| {
			boundary = S2TextFormat.make_loop(loop_text)?
			Ok(if (normalize and !boundary.is_full()) boundary.normalized() else boundary)
		},
	)?
	Ok(S2Polygon.from_loops(loops))
}

# The cases below were read by upstream's s2textformat at v0.14.0 through
# tools/s2_oracle.cc. Several come from s2text_format_test.cc: SafeMakePoint,
# SafeParseLatLngs (the invalid inputs), SafeMakeLatLngRect, SafeMakeCellId,
# SafeMakeCellUnion, SafeMakeLoop, MakeLaxPolygon.Empty and Full.

# tf_parse point.
expect S2TextFormat.make_point("-20:150") == Ok(S2Point.new(-0.8137976813493738, 0.46984631039295416, -0.34202014332566871))
expect S2TextFormat.make_point("-20:150").map_ok(S2TextFormat.point_to_string) == Ok("-20:150")
expect S2TextFormat.make_point("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_point("  -20 : 150 ") == Ok(S2Point.new(-0.8137976813493738, 0.46984631039295416, -0.34202014332566871))
expect S2TextFormat.make_point("  -20 : 150 ").map_ok(S2TextFormat.point_to_string) == Ok("-20:150")
expect S2TextFormat.make_point("1:2, 3:4") == Err(InvalidArgument("Expected 1 point, got 2"))
expect S2TextFormat.make_point("") == Err(InvalidArgument("Expected 1 point, got 0"))
expect S2TextFormat.make_point("0:0") == Ok(S2Point.new(1.0, 0.0, 0.0))
expect S2TextFormat.make_point("0:0").map_ok(S2TextFormat.point_to_string) == Ok("0:0")
expect S2TextFormat.make_point("90:0") == Ok(S2Point.new(6.123233995736766e-17, 0.0, 1.0))
expect S2TextFormat.make_point("90:0").map_ok(S2TextFormat.point_to_string) == Ok("90:0")
expect S2TextFormat.make_point("-90:180") == Ok(S2Point.new(-6.123233995736766e-17, 7.498798913309288e-33, -1.0))
expect S2TextFormat.make_point("-90:180").map_ok(S2TextFormat.point_to_string) == Ok("-90:180")
expect S2TextFormat.make_point("37.7749:-122.4194") == Ok(S2Point.new(-0.42375600249150608, -0.66723313825194108, 0.61256084560709956))
expect S2TextFormat.make_point("37.7749:-122.4194").map_ok(S2TextFormat.point_to_string) == Ok("37.7749:-122.4194")
expect S2TextFormat.make_point("1e-20:1e-30") == Ok(S2Point.new(1.0, 1.7453292519943296e-32, 1.7453292519943296e-22))
expect S2TextFormat.make_point("1e-20:1e-30").map_ok(S2TextFormat.point_to_string) == Ok("1e-20:1e-30")
expect S2TextFormat.make_point("NaN:0") == Err(InvalidArgument("Invalid latlng coordinates: NaN:0"))
expect S2TextFormat.make_point("inf:0") == Err(InvalidArgument("Invalid latlng coordinates: inf:0"))
expect S2TextFormat.make_point("91:0") == Err(InvalidArgument("Invalid latlng coordinates: 91:0"))
expect S2TextFormat.make_point("0:181") == Err(InvalidArgument("Invalid latlng coordinates: 0:181"))
expect S2TextFormat.make_point("0:-180") == Ok(S2Point.new(-1.0, -1.2246467991473532e-16, 0.0))
expect S2TextFormat.make_point("0:-180").map_ok(S2TextFormat.point_to_string) == Ok("0:-180")
expect S2TextFormat.make_point("1:2:3") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): 1:2:3"))
expect S2TextFormat.make_point("1:") == Err(InvalidArgument("Failed to parse longitude: "))
expect S2TextFormat.make_point(":1") == Err(InvalidArgument("Failed to parse latitude: "))
expect S2TextFormat.make_point("10") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): 10"))
expect S2TextFormat.make_point(",,1:1,,") == Ok(S2Point.new(0.99969541350954794, 0.017449748351250485, 0.017452406437283512))
expect S2TextFormat.make_point(",,1:1,,").map_ok(S2TextFormat.point_to_string) == Ok("1:1")
expect S2TextFormat.make_point("1:1, ,") == Err(InvalidArgument("Invalid latlng format (expected lat:lng):  "))

# tf_parse latlng.
expect S2TextFormat.make_lat_lng("-12.3:45.6") == Ok(S2LatLng.from_radians(-0.21467549799530256, 0.79587013890941427))
expect S2TextFormat.make_lat_lng("-12.3:45.6").map_ok(S2TextFormat.lat_lng_to_string) == Ok("-12.3:45.6")
expect S2TextFormat.make_lat_lng("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_lat_lng("1:2, 3:4") == Err(InvalidArgument("Expected 1 latlng, got 2"))
expect S2TextFormat.make_lat_lng("0:180") == Ok(S2LatLng.from_radians(0.0, 3.1415926535897931))
expect S2TextFormat.make_lat_lng("0:180").map_ok(S2TextFormat.lat_lng_to_string) == Ok("0:180")

# tf_parse latlngs.
expect S2TextFormat.parse_lat_lngs("-20:150, -20:151, -19:150") == Ok([S2LatLng.from_radians(-0.3490658503988659, 2.6179938779914944), S2LatLng.from_radians(-0.3490658503988659, 2.6354471705114375), S2LatLng.from_radians(-0.33161255787892263, 2.6179938779914944)])
expect S2TextFormat.parse_lat_lngs("-20:150, -20:151, -19:150").map_ok(S2TextFormat.lat_lngs_to_string) == Ok("-20:150, -20:151, -19:150")
expect S2TextFormat.parse_lat_lngs("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.parse_lat_lngs("NaN:0") == Err(InvalidArgument("Invalid latlng coordinates: NaN:0"))
expect S2TextFormat.parse_lat_lngs("inf:0") == Err(InvalidArgument("Invalid latlng coordinates: inf:0"))
expect S2TextFormat.parse_lat_lngs("infinity:0") == Err(InvalidArgument("Invalid latlng coordinates: infinity:0"))
expect S2TextFormat.parse_lat_lngs("91:0") == Err(InvalidArgument("Invalid latlng coordinates: 91:0"))
expect S2TextFormat.parse_lat_lngs("") == Ok([])
expect S2TextFormat.parse_lat_lngs("").map_ok(S2TextFormat.lat_lngs_to_string) == Ok("")
expect S2TextFormat.parse_lat_lngs("0x10:0x20") == Ok([S2LatLng.from_radians(0.27925268031909273, 0.55850536063818546)])
expect S2TextFormat.parse_lat_lngs("0x10:0x20").map_ok(S2TextFormat.lat_lngs_to_string) == Ok("16:32")
expect S2TextFormat.parse_lat_lngs("1e1:2.5e1") == Ok([S2LatLng.from_radians(0.17453292519943295, 0.43633231299858238)])
expect S2TextFormat.parse_lat_lngs("1e1:2.5e1").map_ok(S2TextFormat.lat_lngs_to_string) == Ok("10:25")

# tf_parse points.
expect S2TextFormat.parse_points("-20:150, -20:151, -19:150") == Ok([S2Point.new(-0.8137976813493738, 0.46984631039295416, -0.34202014332566871), S2Point.new(-0.82187368479282252, 0.45557202263150159, -0.34202014332566871), S2Point.new(-0.81884310621908574, 0.47275928779965837, -0.3255681544571567)])
expect S2TextFormat.parse_points("-20:150, -20:151, -19:150").map_ok(S2TextFormat.points_to_string) == Ok("-20:150, -20:151, -19:150")
expect S2TextFormat.parse_points("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.parse_points("") == Ok([])
expect S2TextFormat.parse_points("").map_ok(S2TextFormat.points_to_string) == Ok("")
expect S2TextFormat.parse_points("45:0, 0:90") == Ok([S2Point.new(0.70710678118654757, 0.0, 0.70710678118654746), S2Point.new(6.123233995736766e-17, 1.0, 0.0)])
expect S2TextFormat.parse_points("45:0, 0:90").map_ok(S2TextFormat.points_to_string) == Ok("45:0, 0:90")

# tf_parse rect.
expect S2TextFormat.make_lat_lng_rect("-10:-10, 10:10") == Ok(S2LatLngRect.new(R1Interval.new(-0.17453292519943295, 0.17453292519943295), S1Interval.new(-0.17453292519943295, 0.17453292519943295)))
expect S2TextFormat.make_lat_lng_rect("-10:-10, 10:10").map_ok(S2TextFormat.lat_lng_rect_to_string) == Ok("-10:-10, 10:10")
expect S2TextFormat.make_lat_lng_rect("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_lat_lng_rect("") == Err(InvalidArgument("No points found to construct S2LatLngRect"))
expect S2TextFormat.make_lat_lng_rect("5:5") == Ok(S2LatLngRect.new(R1Interval.new(0.087266462599716474, 0.087266462599716474), S1Interval.new(0.087266462599716474, 0.087266462599716474)))
expect S2TextFormat.make_lat_lng_rect("5:5").map_ok(S2TextFormat.lat_lng_rect_to_string) == Ok("5:5, 5:5")
expect S2TextFormat.make_lat_lng_rect("10:170, -10:-170") == Ok(S2LatLngRect.new(R1Interval.new(-0.17453292519943295, 0.17453292519943295), S1Interval.new(2.9670597283903604, -2.9670597283903604)))
expect S2TextFormat.make_lat_lng_rect("10:170, -10:-170").map_ok(S2TextFormat.lat_lng_rect_to_string) == Ok("-10:170, 10:-170")
expect S2TextFormat.make_lat_lng_rect("0:0, 0:0, 0:0") == Ok(S2LatLngRect.new(R1Interval.new(0.0, 0.0), S1Interval.new(0.0, 0.0)))
expect S2TextFormat.make_lat_lng_rect("0:0, 0:0, 0:0").map_ok(S2TextFormat.lat_lng_rect_to_string) == Ok("0:0, 0:0")
expect S2TextFormat.make_lat_lng_rect("80:0, 85:1e-3") == Ok(S2LatLngRect.new(R1Interval.new(1.3962634015954636, 1.4835298641951802), S1Interval.new(0.0, 1.7453292519943296e-05)))
expect S2TextFormat.make_lat_lng_rect("80:0, 85:1e-3").map_ok(S2TextFormat.lat_lng_rect_to_string) == Ok("80:0, 85:0.001")

# tf_parse cell.
expect S2TextFormat.make_cell_id("3/") == Ok(S2CellId.from_id(8070450532247928832))
expect S2TextFormat.make_cell_id("3/").map_ok(S2TextFormat.cell_id_to_string) == Ok("3/")
expect S2TextFormat.make_cell_id("blah") == Err(InvalidArgument("Invalid S2CellId: blah"))
expect S2TextFormat.make_cell_id("6/0") == Err(InvalidArgument("Invalid S2CellId: 6/0"))
expect S2TextFormat.make_cell_id("3/04") == Err(InvalidArgument("Invalid S2CellId: 3/04"))
expect S2TextFormat.make_cell_id("2/033") == Ok(S2CellId.from_id(5170132372221329408))
expect S2TextFormat.make_cell_id("2/033").map_ok(S2TextFormat.cell_id_to_string) == Ok("2/033")
expect S2TextFormat.make_cell_id("0/0123012301230123012301230123") == Ok(S2CellId.from_id(244148083328508784))
expect S2TextFormat.make_cell_id("0/0123012301230123012301230123").map_ok(S2TextFormat.cell_id_to_string) == Ok("0/0123012301230123012301230123")
expect S2TextFormat.make_cell_id("0/01230123012301230123012301230") == Ok(S2CellId.from_id(244148083328508772))
expect S2TextFormat.make_cell_id("0/01230123012301230123012301230").map_ok(S2TextFormat.cell_id_to_string) == Ok("0/01230123012301230123012301230")
expect S2TextFormat.make_cell_id("3") == Err(InvalidArgument("Invalid S2CellId: 3"))
expect S2TextFormat.make_cell_id("/") == Err(InvalidArgument("Invalid S2CellId: /"))
expect S2TextFormat.make_cell_id("3/ 0") == Err(InvalidArgument("Invalid S2CellId: 3/ 0"))
expect S2TextFormat.make_cell_id("-1/0") == Err(InvalidArgument("Invalid S2CellId: -1/0"))
expect S2TextFormat.make_cell_id(" 3/") == Err(InvalidArgument("Invalid S2CellId:  3/"))
expect S2TextFormat.make_cell_id("00/") == Err(InvalidArgument("Invalid S2CellId: 00/"))

# tf_parse union.
expect S2TextFormat.make_cell_union("1/3, 4/") == Ok(S2CellUnion.from_ids([4323455642275676160, 10376293541461622784]))
expect S2TextFormat.make_cell_union("1/3, 4/").map_ok(S2TextFormat.cell_union_to_string) == Ok("1/3, 4/")
expect S2TextFormat.make_cell_union("abc") == Err(InvalidArgument("Invalid S2CellId: abc"))
expect S2TextFormat.make_cell_union("3/1 4/1") == Err(InvalidArgument("Invalid S2CellId: 3/1 4/1"))
expect S2TextFormat.make_cell_union("") == Ok(S2CellUnion.from_ids([]))
expect S2TextFormat.make_cell_union("").map_ok(S2TextFormat.cell_union_to_string) == Ok("")
expect S2TextFormat.make_cell_union("1/0, 1/1, 1/2, 1/3") == Ok(S2CellUnion.from_ids([3458764513820540928]))
expect S2TextFormat.make_cell_union("1/0, 1/1, 1/2, 1/3").map_ok(S2TextFormat.cell_union_to_string) == Ok("1/")
expect S2TextFormat.make_cell_union("2/, 2/0") == Ok(S2CellUnion.from_ids([5764607523034234880]))
expect S2TextFormat.make_cell_union("2/, 2/0").map_ok(S2TextFormat.cell_union_to_string) == Ok("2/")
expect S2TextFormat.make_cell_union("1/3,,4/") == Ok(S2CellUnion.from_ids([4323455642275676160, 10376293541461622784]))
expect S2TextFormat.make_cell_union("1/3,,4/").map_ok(S2TextFormat.cell_union_to_string) == Ok("1/3, 4/")
expect S2TextFormat.make_cell_union(" 5/0 , 0/ ") == Ok(S2CellUnion.from_ids([1152921504606846976, 11817445422220181504]))
expect S2TextFormat.make_cell_union(" 5/0 , 0/ ").map_ok(S2TextFormat.cell_union_to_string) == Ok("0/, 5/0")

# tf_parse loop.
expect S2TextFormat.make_loop("-20:150, -20:151, -19:150") == Ok(S2Loop.from_points([S2Point.new(-0.8137976813493738, 0.46984631039295416, -0.34202014332566871), S2Point.new(-0.82187368479282252, 0.45557202263150159, -0.34202014332566871), S2Point.new(-0.81884310621908574, 0.47275928779965837, -0.3255681544571567)]))
expect S2TextFormat.make_loop("-20:150, -20:151, -19:150").map_ok(S2TextFormat.loop_to_string) == Ok("-20:150, -20:151, -19:150")
expect S2TextFormat.make_loop("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_loop("empty") == Ok(S2Loop.from_points([S2Point.new(0.0, 0.0, 1.0)]))
expect S2TextFormat.make_loop("empty").map_ok(S2TextFormat.loop_to_string) == Ok("empty")
expect S2TextFormat.make_loop("full") == Ok(S2Loop.from_points([S2Point.new(0.0, 0.0, -1.0)]))
expect S2TextFormat.make_loop("full").map_ok(S2TextFormat.loop_to_string) == Ok("full")
expect S2TextFormat.make_loop("") == Ok(S2Loop.from_points([]))
expect S2TextFormat.make_loop("").map_ok(S2TextFormat.loop_to_string) == Ok("")
expect S2TextFormat.make_loop("0:0") == Ok(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0)]))
expect S2TextFormat.make_loop("0:0").map_ok(S2TextFormat.loop_to_string) == Ok("empty")
expect S2TextFormat.make_loop("90:0") == Ok(S2Loop.from_points([S2Point.new(6.123233995736766e-17, 0.0, 1.0)]))
expect S2TextFormat.make_loop("90:0").map_ok(S2TextFormat.loop_to_string) == Ok("empty")
expect S2TextFormat.make_loop("-90:0") == Ok(S2Loop.from_points([S2Point.new(6.123233995736766e-17, 0.0, -1.0)]))
expect S2TextFormat.make_loop("-90:0").map_ok(S2TextFormat.loop_to_string) == Ok("full")
expect S2TextFormat.make_loop("0:0, 0:90, 90:0") == Ok(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(6.123233995736766e-17, 1.0, 0.0), S2Point.new(6.123233995736766e-17, 0.0, 1.0)]))
expect S2TextFormat.make_loop("0:0, 0:90, 90:0").map_ok(S2TextFormat.loop_to_string) == Ok("0:0, 0:90, 90:0")
expect S2TextFormat.make_loop("1:1, 1:2, 2:2, 2:1") == Ok(S2Loop.from_points([S2Point.new(0.99969541350954794, 0.017449748351250485, 0.017452406437283512), S2Point.new(0.99923861495548261, 0.03489418134011367, 0.017452406437283512), S2Point.new(0.99878202512991221, 0.034878236872062651, 0.034899496702500969), S2Point.new(0.99923861495548261, 0.017441774902830158, 0.034899496702500969)]))
expect S2TextFormat.make_loop("1:1, 1:2, 2:2, 2:1").map_ok(S2TextFormat.loop_to_string) == Ok("1:1, 1:2, 2:2, 2:1")
expect S2TextFormat.make_loop("Empty") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): Empty"))
expect S2TextFormat.make_loop(" empty") == Err(InvalidArgument("Invalid latlng format (expected lat:lng):  empty"))

# tf_parse line.
expect S2TextFormat.make_polyline("-20:150, -20:151") == Ok(S2Polyline.from_points([S2Point.new(-0.8137976813493738, 0.46984631039295416, -0.34202014332566871), S2Point.new(-0.82187368479282252, 0.45557202263150159, -0.34202014332566871)]))
expect S2TextFormat.make_polyline("-20:150, -20:151").map_ok(S2TextFormat.polyline_to_string) == Ok("-20:150, -20:151")
expect S2TextFormat.make_polyline("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_polyline("") == Ok(S2Polyline.from_points([]))
expect S2TextFormat.make_polyline("").map_ok(S2TextFormat.polyline_to_string) == Ok("")
expect S2TextFormat.make_polyline("0:0") == Ok(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0)]))
expect S2TextFormat.make_polyline("0:0").map_ok(S2TextFormat.polyline_to_string) == Ok("0:0")
expect S2TextFormat.make_polyline("0:0, 0:0") == Ok(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(1.0, 0.0, 0.0)]))
expect S2TextFormat.make_polyline("0:0, 0:0").map_ok(S2TextFormat.polyline_to_string) == Ok("0:0, 0:0")

# tf_parse polygon.
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3)])
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0")
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0; 1:1, 1:4, 4:1").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (1, 3)])
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0; 1:1, 1:4, 4:1").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n1:1, 1:4, 4:1")
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0; 1:1, 4:1, 1:4").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (1, 3)])
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0; 1:1, 4:1, 1:4").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n1:4, 4:1, 1:1")
expect S2TextFormat.make_polygon("empty").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([])
expect S2TextFormat.make_polygon("empty").map_ok(S2TextFormat.polygon_to_string) == Ok("empty")
expect S2TextFormat.make_polygon("full").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 1)])
expect S2TextFormat.make_polygon("full").map_ok(S2TextFormat.polygon_to_string) == Ok("full")
expect S2TextFormat.make_polygon("").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([])
expect S2TextFormat.make_polygon("").map_ok(S2TextFormat.polygon_to_string) == Ok("empty")
expect S2TextFormat.make_polygon("full; 0:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 1)])
expect S2TextFormat.make_polygon("full; 0:0").map_ok(S2TextFormat.polygon_to_string) == Ok("full")
expect S2TextFormat.make_polygon("0:0, 5:0, 0:5").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3)])
expect S2TextFormat.make_polygon("0:0, 5:0, 0:5").map_ok(S2TextFormat.polygon_to_string) == Ok("0:5, 5:0, 0:0")
expect S2TextFormat.make_polygon("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0; blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0;;  ; 1:1, 1:4, 4:1 ;").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (1, 3)])
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0;;  ; 1:1, 1:4, 4:1 ;").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n1:1, 1:4, 4:1")
expect S2TextFormat.make_polygon("1:1, 1:4, 4:1; 0:0, 0:5, 5:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (1, 3)])
expect S2TextFormat.make_polygon("1:1, 1:4, 4:1; 0:0, 0:5, 5:0").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n1:1, 1:4, 4:1")
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0 ; 10:10, 10:15, 15:10").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (0, 3)])
expect S2TextFormat.make_polygon("0:0, 0:5, 5:0 ; 10:10, 10:15, 15:10").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n10:10, 10:15, 15:10")
expect S2TextFormat.make_polygon("empty; 0:0, 0:5, 5:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3)])
expect S2TextFormat.make_polygon("empty; 0:0, 0:5, 5:0").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0")
expect S2TextFormat.make_polygon("90:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([])
expect S2TextFormat.make_polygon("90:0").map_ok(S2TextFormat.polygon_to_string) == Ok("empty")
expect S2TextFormat.make_polygon("-90:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 1)])
expect S2TextFormat.make_polygon("-90:0").map_ok(S2TextFormat.polygon_to_string) == Ok("full")

# tf_parse verbatim.
expect S2TextFormat.make_verbatim_polygon("0:0, 5:0, 0:5").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3)])
expect S2TextFormat.make_verbatim_polygon("0:0, 5:0, 0:5").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 5:0, 0:5")
expect S2TextFormat.make_verbatim_polygon("0:0, 0:5, 5:0; 1:1, 1:4, 4:1").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (1, 3)])
expect S2TextFormat.make_verbatim_polygon("0:0, 0:5, 5:0; 1:1, 1:4, 4:1").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n1:1, 1:4, 4:1")
expect S2TextFormat.make_verbatim_polygon("empty").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([])
expect S2TextFormat.make_verbatim_polygon("empty").map_ok(S2TextFormat.polygon_to_string) == Ok("empty")
expect S2TextFormat.make_verbatim_polygon("full").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 1)])
expect S2TextFormat.make_verbatim_polygon("full").map_ok(S2TextFormat.polygon_to_string) == Ok("full")
expect S2TextFormat.make_verbatim_polygon("").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([])
expect S2TextFormat.make_verbatim_polygon("").map_ok(S2TextFormat.polygon_to_string) == Ok("empty")
expect S2TextFormat.make_verbatim_polygon("blah") == Err(InvalidArgument("Invalid latlng format (expected lat:lng): blah"))
expect S2TextFormat.make_verbatim_polygon("1:1, 1:4, 4:1; 0:0, 0:5, 5:0").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 3), (1, 3)])
expect S2TextFormat.make_verbatim_polygon("1:1, 1:4, 4:1; 0:0, 0:5, 5:0").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0;\n1:1, 1:4, 4:1")
expect S2TextFormat.make_verbatim_polygon("0:0, 0:5, 5:0, 5:5").map_ok(|pg| pg.loops().map(|l| (l.depth, l.boundary.num_vertices()))) == Ok([(0, 4)])
expect S2TextFormat.make_verbatim_polygon("0:0, 0:5, 5:0, 5:5").map_ok(S2TextFormat.polygon_to_string) == Ok("0:0, 0:5, 5:0, 5:5")

# `ToString`, through tools/s2_oracle.cc. The point cases include upstream's
# ToString.NegativeZeros, the cell ones ToString.FaceCellId and Level3CellId,
# and the loop, polyline, point and polygon ones ToString.EmptyLoop, FullLoop,
# UninitializedLoop, EmptyPolyline, EmptyPointVector, EmptyPolygon and
# FullPolygon.
expect S2TextFormat.point_to_string(S2Point.new(1.0, 0.0, 0.0)) == "0:0"
expect S2TextFormat.point_to_string(S2Point.new(0.0, 0.0, 1.0)) == "90:0"
expect S2TextFormat.point_to_string(S2Point.new(1.0, -0.0, 0.0)) == "0:0"
expect S2TextFormat.point_to_string(S2Point.new(1.0, 0.0, -0.0)) == "0:0"
expect S2TextFormat.point_to_string(S2Point.new(1.0, -0.0, -0.0)) == "0:0"
expect S2TextFormat.point_to_string(S2Point.new(-1.0, -0.0, 0.0)) == "0:180"
expect S2TextFormat.point_to_string(S2Point.new(-1.0, 0.0, -0.0)) == "0:180"
expect S2TextFormat.point_to_string(S2Point.new(-1.0, -0.0, -0.0)) == "0:180"
expect S2TextFormat.point_to_string(S2Point.new(-0.0, 0.0, 1.0)) == "90:0"
expect S2TextFormat.point_to_string(S2Point.new(0.0, -0.0, 1.0)) == "90:0"
expect S2TextFormat.point_to_string(S2Point.new(-0.0, -0.0, 1.0)) == "90:0"
expect S2TextFormat.point_to_string(S2Point.new(0.3, -0.4, 0.5)) == "45:-53.130102354156"
expect S2TextFormat.point_to_string(S2Point.new(1.0, 1.0e-15, 1.0e-25)) == "5.72957795130823e-24:5.72957795130823e-14"
expect S2TextFormat.point_to_string(S2Point.new(-1.0, -1.0e-10, -1.0e-300)) == "-5.72957795130823e-299:-179.99999999427"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(0.0, 0.0)) == "0:0"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(0.5, -1.2)) == "28.6478897565412:-68.7549354156988"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(1.0e-05, 3.1)) == "0.000572957795130823:177.616916490555"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(1.5707963267948966, 3.141592653589793)) == "90:180"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(-1.5707963267948966, -3.141592653589793)) == "-90:-180"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(1.5e-20, 2.0e-30)) == "8.59436692696235e-19:1.14591559026165e-28"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(0.6584, -2.1359)) == "37.7235412314134:-122.378055461993"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(0.0123456789012345, 0.9876543210987654)) == "0.707355296264444:56.5884242168179"
expect S2TextFormat.lat_lng_to_string(S2LatLng.from_radians(100.0, 200.0)) == "5729.57795130823:11459.1559026165"
expect S2TextFormat.lat_lng_rect_to_string(S2LatLngRect.new(R1Interval.new(-0.1, 0.2), S1Interval.new(0.3, 0.9))) == "-5.72957795130823:17.1887338539247, 11.4591559026165:51.5662015617741"
expect S2TextFormat.lat_lng_rect_to_string(S2LatLngRect.new(R1Interval.new(1.0, 0.0), S1Interval.new(3.141592653589793, -3.141592653589793))) == "57.2957795130823:180, 0:-180"
expect S2TextFormat.lat_lng_rect_to_string(S2LatLngRect.new(R1Interval.new(-1.5707963267948966, 1.5707963267948966), S1Interval.new(-3.141592653589793, 3.141592653589793))) == "-90:-180, 90:180"
expect S2TextFormat.lat_lng_rect_to_string(S2LatLngRect.new(R1Interval.new(0.1, 0.1), S1Interval.new(3.0, -3.0))) == "5.72957795130823:171.887338539247, 5.72957795130823:-171.887338539247"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(5764607523034234880)) == "2/"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(5170132372221329408)) == "2/033"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(0)) == "Invalid: 0000000000000000"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(1)) == "0/000000000000000000000000000000"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(8070450532247928832)) == "3/"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(244148083328508784)) == "0/0123012301230123012301230123"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(9223372036854775808)) == "Invalid: 8000000000000000"
expect S2TextFormat.cell_id_to_string(S2CellId.from_id(18446744073709551615)) == "Invalid: ffffffffffffffff"
expect S2TextFormat.cell_union_to_string(S2CellUnion.from_verbatim([])) == ""
expect S2TextFormat.cell_union_to_string(S2CellUnion.from_verbatim([S2CellId.from_id(5764607523034234880)])) == "2/"
expect S2TextFormat.cell_union_to_string(S2CellUnion.from_verbatim([S2CellId.from_id(5170132372221329408), S2CellId.from_id(8070450532247928832)])) == "2/033, 3/"
expect S2TextFormat.cell_union_to_string(S2CellUnion.from_verbatim([S2CellId.from_id(3), S2CellId.from_id(5)])) == "0/000000000000000000000000000001, 0/000000000000000000000000000002"
expect S2TextFormat.loop_to_string(S2Loop.from_points([])) == ""
expect S2TextFormat.polyline_to_string(S2Polyline.from_points([])) == ""
expect S2TextFormat.points_to_string([]) == ""
expect S2TextFormat.loop_to_string(S2Loop.from_points([S2Point.new(0.0, 0.0, 1.0)])) == "empty"
expect S2TextFormat.polyline_to_string(S2Polyline.from_points([S2Point.new(0.0, 0.0, 1.0)])) == "90:0"
expect S2TextFormat.points_to_string([S2Point.new(0.0, 0.0, 1.0)]) == "90:0"
expect S2TextFormat.loop_to_string(S2Loop.from_points([S2Point.new(0.0, 0.0, -1.0)])) == "full"
expect S2TextFormat.polyline_to_string(S2Polyline.from_points([S2Point.new(0.0, 0.0, -1.0)])) == "-90:0"
expect S2TextFormat.points_to_string([S2Point.new(0.0, 0.0, -1.0)]) == "-90:0"
expect S2TextFormat.loop_to_string(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])) == "0:0, 0:90, 90:0"
expect S2TextFormat.polyline_to_string(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])) == "0:0, 0:90, 90:0"
expect S2TextFormat.points_to_string([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]) == "0:0, 0:90, 90:0"
expect S2TextFormat.loop_to_string(S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.6, 0.8, 0.0)])) == "0:0, 0:53.130102354156"
expect S2TextFormat.polyline_to_string(S2Polyline.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.6, 0.8, 0.0)])) == "0:0, 0:53.130102354156"
expect S2TextFormat.points_to_string([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.6, 0.8, 0.0)]) == "0:0, 0:53.130102354156"
expect S2TextFormat.polygon_to_string(S2Polygon.from_loops([])) == "empty"
expect S2TextFormat.polygon_to_string_with(S2Polygon.from_loops([]), ";") == "empty"
expect S2TextFormat.polygon_to_string(S2Polygon.from_loops([S2Loop.from_points([S2Point.new(0.0, 0.0, -1.0)])])) == "full"
expect S2TextFormat.polygon_to_string_with(S2Polygon.from_loops([S2Loop.from_points([S2Point.new(0.0, 0.0, -1.0)])]), ";") == "full"
expect S2TextFormat.polygon_to_string(S2Polygon.from_loops([S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])])) == "0:0, 0:90, 90:0"
expect S2TextFormat.polygon_to_string_with(S2Polygon.from_loops([S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)])]), ";") == "0:0, 0:90, 90:0"
expect S2TextFormat.polygon_to_string(S2Polygon.from_loops([S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]), S2Loop.from_points([S2Point.new(0.8, 0.1, 0.1), S2Point.new(0.1, 0.8, 0.1), S2Point.new(0.1, 0.1, 0.8)])])) == "0:0, 0:90, 90:0;\n7.07055511696583:7.1250163489018, 7.07055511696583:82.8749836510982, 79.9750121379243:45"
expect S2TextFormat.polygon_to_string_with(S2Polygon.from_loops([S2Loop.from_points([S2Point.new(1.0, 0.0, 0.0), S2Point.new(0.0, 1.0, 0.0), S2Point.new(0.0, 0.0, 1.0)]), S2Loop.from_points([S2Point.new(0.8, 0.1, 0.1), S2Point.new(0.1, 0.8, 0.1), S2Point.new(0.1, 0.1, 0.8)])]), ";") == "0:0, 0:90, 90:0;7.07055511696583:7.1250163489018, 7.07055511696583:82.8749836510982, 79.9750121379243:45"

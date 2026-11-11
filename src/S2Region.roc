import S2Cap
import S2Cell
import S2CellId
import S2LatLngRect
import S1Angle
import S2LatLng
import S2Polyline
import S2PointRegion
import S2Point

## Any region, with its type forgotten.
##
## Upstream has a base class `S2Region`, so that a list can hold a cap, a
## polygon and a cell union together. Roc has no such class, and the regions
## here are generic through `where` clauses, which cannot name a list of
## different types. `S2Region` closes that gap: `from` wraps one region into a
## value of this type, and a list of such values is what `S2RegionUnion` and
## `S2RegionIntersection` take.
##
##     regions = [S2Region.from(cap), S2Region.from(rect), S2Region.from(polygon)]
##     S2RegionUnion.new(regions)
##
## An `S2Region` has the three methods that `S2RegionCoverer` asks for, so a
## coverer can cover it. It also has `cap_bound`, `rect_bound` and
## `contains_point`, and wrapping the value again with `from` works.
S2Region :: {
	cap_fn : () -> S2Cap,
	rect_fn : () -> S2LatLngRect,
	union_bound_fn : () -> List(S2CellId),
	contains_cell_fn : S2Cell -> Bool,
	may_intersect_cell_fn : S2Cell -> Bool,
	contains_point_fn : S2Point -> Bool,
}.{

	## Wraps a region. The region needs the three methods of a coverer's
	## region and also `cap_bound`, `rect_bound` and `contains_point`;
	## `S2LatLngRect`, `S2CellUnion`, `S2Loop`, `S2Polyline`, `S2Polygon`,
	## `S2PointRegion` and the unions and intersections of regions have them
	## all.
	##
	## An `S2Cap` has no `rect_bound` method and an `S2Cell` has neither bound
	## method. A module cannot import the module that imports it, and the
	## rectangle's module imports the cap and the cell. So the bounds of these
	## two are constructors on the rectangle and the cap, and their wrappers
	## are `from_cap` and `from_cell`.
	from : r -> S2Region
		where [
			r.cap_bound : r -> S2Cap,
			r.rect_bound : r -> S2LatLngRect,
			r.cell_union_bound : r -> List(S2CellId),
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
			r.contains_point : r, S2Point -> Bool,
		]
	from = |region| {
		cap_fn: || region.cap_bound(),
		rect_fn: || region.rect_bound(),
		union_bound_fn: || region.cell_union_bound(),
		contains_cell_fn: |cell| region.contains_cell(cell),
		may_intersect_cell_fn: |cell| region.may_intersect_cell(cell),
		contains_point_fn: |p| region.contains_point(p),
	}

	## Wraps a cap as a region. Its rectangle bound is
	## `S2LatLngRect.from_cap`.
	from_cap : S2Cap -> S2Region
	from_cap = |cap| {
		cap_fn: || cap,
		rect_fn: || S2LatLngRect.from_cap(cap),
		union_bound_fn: || cap.cell_union_bound(),
		contains_cell_fn: |cell| cap.contains_cell(cell),
		may_intersect_cell_fn: |cell| cap.may_intersect_cell(cell),
		contains_point_fn: |p| cap.contains_point(p),
	}

	## Wraps a cell as a region. Its bounds are `S2Cap.from_cell` and
	## `S2LatLngRect.from_cell`.
	from_cell : S2Cell -> S2Region
	from_cell = |cell| {
		cap_fn: || S2Cap.from_cell(cell),
		rect_fn: || S2LatLngRect.from_cell(cell),
		union_bound_fn: || cell.cell_union_bound(),
		contains_cell_fn: |other| cell.contains_cell(other),
		may_intersect_cell_fn: |other| cell.may_intersect_cell(other),
		contains_point_fn: |p| cell.contains_point(p),
	}

	## A cap that contains the region.
	cap_bound : S2Region -> S2Cap
	cap_bound = |region| (region.cap_fn)()

	## A rectangle that contains the region.
	rect_bound : S2Region -> S2LatLngRect
	rect_bound = |region| (region.rect_fn)()

	## A few cells that together cover the region.
	cell_union_bound : S2Region -> List(S2CellId)
	cell_union_bound = |region| (region.union_bound_fn)()

	## True when the region contains the whole cell. A region may answer
	## false for a cell it contains.
	contains_cell : S2Region, S2Cell -> Bool
	contains_cell = |region, cell| (region.contains_cell_fn)(cell)

	## False when the region does not meet the cell. A region may answer true
	## for a cell it does not meet.
	may_intersect_cell : S2Region, S2Cell -> Bool
	may_intersect_cell = |region, cell| (region.may_intersect_cell_fn)(cell)

	## True when the region contains the point.
	contains_point : S2Region, S2Point -> Bool
	contains_point = |region, p| (region.contains_point_fn)(p)
}

# A wrapped region answers as the region does.
expect {
	cap = S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(3.0))
	region = S2Region.from_cap(cap)
	cell = S2Cell.from_cell_id(S2CellId.from_point(cap.center()).parent_at_level(8))
	region.cap_bound() == cap
		and region.rect_bound() == S2LatLngRect.from_cap(cap)
		and region.cell_union_bound() == cap.cell_union_bound()
		and region.contains_cell(cell) == cap.contains_cell(cell)
		and region.may_intersect_cell(cell) == cap.may_intersect_cell(cell)
		and region.contains_point(cap.center())
		and !region.contains_point(S2LatLng.from_degrees(-10.0, 20.0).to_point())
}
expect {
	rect = S2LatLngRect.from_point_pair(S2LatLng.from_degrees(0.0, 0.0), S2LatLng.from_degrees(10.0, 10.0))
	region = S2Region.from(rect)
	region.rect_bound() == rect
		and region.cap_bound() == rect.cap_bound()
		and region.contains_point(S2LatLng.from_degrees(5.0, 5.0).to_point())
		and !region.contains_point(S2LatLng.from_degrees(15.0, 5.0).to_point())
}
expect {
	cell = S2Cell.from_cell_id(S2CellId.from_id(5170132372221329408))
	region = S2Region.from_cell(cell)
	region.cap_bound() == S2Cap.from_cell(cell)
		and region.rect_bound() == S2LatLngRect.from_cell(cell)
		and region.cell_union_bound() == cell.cell_union_bound()
		and region.contains_cell(cell)
		and region.may_intersect_cell(cell)
		and region.contains_point(cell.center())
}
# A region can be wrapped again, whatever it wraps.
expect {
	point = S2LatLng.from_degrees(35.0, 40.0).to_point()
	once = S2Region.from(S2PointRegion.new(point))
	twice = S2Region.from(once)
	twice.contains_point(point) and twice.rect_bound() == once.rect_bound() and twice.cap_bound() == once.cap_bound()
}
# A polyline can be wrapped. It contains no point and no cell.
expect {
	line = S2Polyline.from_points([S2LatLng.from_degrees(0.0, 0.0).to_point(), S2LatLng.from_degrees(0.0, 10.0).to_point()])
	region = S2Region.from(line)
	!region.contains_point(S2LatLng.from_degrees(0.0, 5.0).to_point()) and region.rect_bound() == line.rect_bound()
}

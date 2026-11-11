import S2Cap
import S2Cell
import S2CellId
import S2LatLng
import S2LatLngRect
import S2Point
import S2RegionCoverer
import Internal/S2Coder

## A single point, as a region. Upstream's `S2PointRegion`.
##
## It has the three region methods that `S2RegionCoverer` asks for, so a
## coverer can find the cells around a point, and the bounds of every other
## region.
##
##     S2RegionCoverer.default()
##         .with_max_level(20)
##         .covering(S2PointRegion.new(p))
##
## A point has no area, so the region contains no cell. The point should be
## unit length.
S2PointRegion := { point : S2Point }.{

	## The region holding just the point.
	new : S2Point -> S2PointRegion
	new = |p| { point: p }

	## The point.
	point : S2PointRegion -> S2Point
	point = |region| region.point

	## The cap of zero radius at the point.
	cap_bound : S2PointRegion -> S2Cap
	cap_bound = |region| S2Cap.from_point(region.point)

	## The rectangle of zero size at the point's latitude and longitude.
	rect_bound : S2PointRegion -> S2LatLngRect
	rect_bound = |region| {
		ll = S2LatLng.from_point(region.point)
		S2LatLngRect.from_bounds(ll, ll)
	}

	## A few cells that cover the point: those of its cap bound, as upstream's
	## `S2PointRegion::GetCellUnionBound` gives them.
	cell_union_bound : S2PointRegion -> List(S2CellId)
	cell_union_bound = |region| region.cap_bound().cell_union_bound()

	## Always false: even a leaf cell is larger than a point.
	contains_cell : S2PointRegion, S2Cell -> Bool
	contains_cell = |_region, _cell| Bool.False

	## True when the cell contains the point.
	may_intersect_cell : S2PointRegion, S2Cell -> Bool
	may_intersect_cell = |region, cell| cell.contains_point(region.point)

	## True when `p` is the point itself.
	contains_point : S2PointRegion, S2Point -> Bool
	contains_point = |region, p| region.point == p

	is_eq : S2PointRegion, S2PointRegion -> Bool
	is_eq = |a, b| a.point == b.point

	to_inspect : S2PointRegion -> Str
	to_inspect = |region| "S2PointRegion(${region.point.to_inspect()})"

	## The 25 bytes that upstream's `S2PointRegion::Encode` writes: the version
	## byte 1 and the three coordinates, each as a little-endian IEEE 754
	## double.
	encode : S2PointRegion -> List(U8)
	encode = |region| [1].concat(region.point.encode())

	## The region that `encode` writes. Bytes after the first 25 are ignored.
	##
	## A version byte above 1 is `UnsupportedVersion`. A point that is not
	## unit length is `NotUnitLength`, as upstream refuses it.
	decode : List(U8) -> Try(S2PointRegion, [Truncated, UnsupportedVersion(U8), NotUnitLength])
	decode = |bytes| {
		if !S2Coder.can_read(bytes, 0, 25) {
			return Err(Truncated)
		}
		version = S2Coder.get_u8(bytes, 0)?
		if version > 1 {
			return Err(UnsupportedVersion(version))
		}
		vector = S2Point.decode(bytes.drop_first(1))?
		if (vector.is_unit_length()) Ok({ point: vector }) else Err(NotUnitLength)
	}
}

# Upstream's S2PointRegionTest.Basic.
expect {
	p = S2Point.new(1.0, 0.0, 0.0)
	r0 = S2PointRegion.new(p)
	ll = S2LatLng.from_point(p)
	cell = S2Cell.from_point(p)
	r0.point() == p
		and r0.contains_point(p)
		and !r0.contains_point(S2Point.new(1.0, 0.0, 1.0))
		and r0.cap_bound() == S2Cap.from_point(p)
		and r0.rect_bound() == S2LatLngRect.from_bounds(ll, ll)
		and !r0.contains_cell(cell)
		and r0.may_intersect_cell(cell)
}

# Upstream's GetCellUnionBound, through tools/s2_oracle.cc.
expect S2PointRegion.new(S2Point.new(1.0, 2.0, 3.0).normalize()).cell_union_bound() == [4885382997816251380, 4885382997816251276, 4885382997816251404, 4885382997816251508].map(S2CellId.from_id)
expect S2PointRegion.new(S2LatLng.from_degrees(37.7749, -122.4194).to_point()).cell_union_bound() == [9260949627242122340, 9260949627242122332, 9260949627242122380, 9260949627242122484].map(S2CellId.from_id)
# A coverer reaches the point's cell at its finest level, since the region
# contains no cell and meets only the cells that hold the point.
expect {
	p = S2LatLng.from_degrees(37.7749, -122.4194).to_point()
	S2RegionCoverer.default().with_max_level(20).covering(S2PointRegion.new(p))
		== [S2CellId.from_point(p).parent_at_level(20)]
}

# Only the cells that hold the point meet the region.
expect !S2PointRegion.new(S2Point.new(1.0, 0.0, 0.0)).may_intersect_cell(S2Cell.from_face(3))

# S2PointRegion encoding against upstream's `Encode`, and decoding it back.
expect S2Coder.to_hex(S2PointRegion.new(S2Point.new(1.0, 0.0, 0.0)).encode()) == "01000000000000f03f00000000000000000000000000000000"
expect S2PointRegion.decode(S2Coder.from_hex("01000000000000f03f00000000000000000000000000000000")) == Ok(S2PointRegion.new(S2Point.new(1.0, 0.0, 0.0)))
expect S2Coder.to_hex(S2PointRegion.new(S2Point.new(0.0, 0.0, -1.0)).encode()) == "0100000000000000000000000000000000000000000000f0bf"
expect S2PointRegion.decode(S2Coder.from_hex("0100000000000000000000000000000000000000000000f0bf")) == Ok(S2PointRegion.new(S2Point.new(0.0, 0.0, -1.0)))

expect S2PointRegion.decode(S2Coder.from_hex("01000000000000004000000000000008400000000000001040")) == Err(NotUnitLength)
expect S2PointRegion.decode(S2Coder.from_hex("01000000000000000000000000000000000000000000000000")) == Err(NotUnitLength)
expect S2PointRegion.decode(S2Coder.from_hex("02000000000000f03f00000000000000000000000000000000")) == Err(UnsupportedVersion(2))
expect S2PointRegion.decode(S2Coder.from_hex("00000000000000f03f00000000000000000000000000000000")) == S2PointRegion.decode(S2Coder.from_hex("01000000000000f03f00000000000000000000000000000000"))
expect S2PointRegion.decode(S2Coder.from_hex("01000000000000f03f000000000000000000000000000000")) == Err(Truncated)
expect S2PointRegion.decode([]) == Err(Truncated)

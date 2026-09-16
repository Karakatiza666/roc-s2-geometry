import s2.S2CellId
import s2.S2LatLng
import CellIdCorpus

## Checks `S2CellId` against a corpus generated from s2sphere, an independent
## port of the same library.
##
## Each check walks the whole corpus and counts mismatches, so a failure means
## at least one of the 200 cases disagreed with upstream.
S2CellIdTest := [].{

	## The leaf cell id of the point a case describes.
	leaf_of : CellIdCorpus.Case -> S2CellId
	leaf_of = |case| S2CellId.from_lat_lng(S2LatLng.from_degrees(case.lat, case.lng))

	## Counts the cases a check rejects.
	failures : (CellIdCorpus.Case -> Bool) -> U64
	failures = |check| CellIdCorpus.cases.fold(0, |acc, case| if check(case) acc else acc + 1)
}

# The identity of the leaf cell containing a point.
expect S2CellIdTest.failures(|case| S2CellIdTest.leaf_of(case).id() == case.id) == 0
expect S2CellIdTest.failures(|case| S2CellIdTest.leaf_of(case).level() == 30) == 0
expect S2CellIdTest.failures(|case| S2CellIdTest.leaf_of(case).is_leaf()) == 0
expect S2CellIdTest.failures(|case| S2CellIdTest.leaf_of(case).is_valid()) == 0
expect S2CellIdTest.failures(|case| S2CellIdTest.leaf_of(case).face() == case.face) == 0

# Tokens, in both directions.
expect S2CellIdTest.failures(|case| S2CellIdTest.leaf_of(case).to_token() == case.token) == 0
expect S2CellIdTest.failures(
	|case| S2CellId.from_token(case.token) == Ok(S2CellId.from_id(case.id)),
)
	== 0

# The Hilbert decode: face, position on the face, and curve orientation.
expect S2CellIdTest.failures(
	|case| {
		ij = S2CellId.from_id(case.id).to_face_ij_orientation()
		ij.face == case.face and ij.i == case.i and ij.j == case.j
			and ij.orientation == case.orientation
	},
)
	== 0

# The centre of the leaf cell, back in latitude and longitude.
expect S2CellIdTest.failures(
	|case| {
		center = S2CellId.from_id(case.id).to_lat_lng()
		(center.lat_degrees() - case.center_lat).abs() < 1e-12
			and (center.lng_degrees() - case.center_lng).abs() < 1e-12
	},
)
	== 0

# Ancestors at every level the corpus records.
expect S2CellIdTest.failures(
	|case| {
		cell_id = S2CellId.from_id(case.id)
		CellIdCorpus.parent_levels
			.map2(case.parents, |level, expected| cell_id.parent_at_level(level).id() == expected)
			.all(|ok| ok)
	},
)
	== 0

# Every ancestor contains the leaf, and the leaf's level is recovered.
expect S2CellIdTest.failures(
	|case| {
		cell_id = S2CellId.from_id(case.id)
		CellIdCorpus.parent_levels.all(
			|level| {
				parent = cell_id.parent_at_level(level)
				parent.contains(cell_id) and parent.level() == level and parent.intersects(cell_id)
			},
		)
	},
)
	== 0

# Traversal along the Hilbert curve.
expect S2CellIdTest.failures(|case| S2CellId.from_id(case.id).prev().id() == case.prev_id) == 0
expect S2CellIdTest.failures(|case| S2CellId.from_id(case.id).next().id() == case.next_id) == 0
expect S2CellIdTest.failures(
	|case| S2CellId.from_id(case.id).next().prev().id() == case.id,
)
	== 0
expect S2CellIdTest.failures(
	|case| S2CellId.from_id(case.id).advance(3).id() == S2CellId.from_id(case.next_id).advance(2).id(),
)
	== 0

# Neighbors, of all three kinds.
expect S2CellIdTest.failures(
	|case| S2CellId.from_id(case.id).edge_neighbors().map(S2CellId.id) == case.edge_neighbors,
)
	== 0
expect S2CellIdTest.failures(
	|case|
		S2CellId.from_id(case.id).vertex_neighbors(CellIdCorpus.vertex_neighbor_level).map(S2CellId.id)
			== case.vertex_neighbors,
)
	== 0
expect S2CellIdTest.failures(
	|case|
		S2CellId.from_id(case.id)
			.parent_at_level(CellIdCorpus.all_neighbor_level)
			.all_neighbors(CellIdCorpus.all_neighbor_level)
			.map(S2CellId.id)
			== case.all_neighbors,
)
	== 0

# Properties that hold for every cell, checked over the same corpus.
expect S2CellIdTest.failures(
	|case| {
		cell_id = S2CellId.from_id(case.id)
		cell_id.range_min() == cell_id and cell_id.range_max() == cell_id
	},
)
	== 0
expect S2CellIdTest.failures(
	|case| {
		parent = S2CellId.from_id(case.id).parent_at_level(10)
		children = parent.children()
		children.len() == 4
			and children.all(|child| parent.contains(child) and child.level() == 11)
				and children.get(0) == Ok(parent.child_begin())
					and parent.child_end() == parent.child(3).next()
	},
)
	== 0
expect S2CellIdTest.failures(
	|case| {
		cell_id = S2CellId.from_id(case.id)
		point = cell_id.to_point()
		S2CellId.from_point(point) == cell_id and point.is_unit_length()
	},
)
	== 0
expect S2CellIdTest.failures(
	|case| {
		cell_id = S2CellId.from_id(case.id)
		S2CellId.from_debug_str(cell_id.to_debug_str()) == Ok(cell_id)
	},
)
	== 0
expect S2CellIdTest.failures(
	|case| {
		cell_id = S2CellId.from_id(case.id)
		S2CellId.common_ancestor_level(cell_id, cell_id) == Ok(30)
			and S2CellId.common_ancestor_level(cell_id.parent_at_level(4), cell_id) == Ok(4)
	},
)
	== 0

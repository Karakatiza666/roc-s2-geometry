import R1Interval
import S1Angle
import S1Interval
import S2Cap
import S2Cell
import S2CellId
import S2CellUnion
import S2LatLng
import S2LatLngRect
import S2Loop
import S2Point
import S2RegionCoverer

## Turns regions into index terms for a text search system. Upstream's
## `S2RegionTermIndexer`.
##
## A search engine finds the documents that hold a word by looking the word
## up in an inverted index. To use one for places, give each region a few
## words, the index terms, and give each query region the words it would
## match. A document is near the query when they share a word.
##
##     indexer = S2RegionTermIndexer.default().with_max_cells(10)
##     index_words = indexer.get_index_terms(cap, "")
##     query_words = indexer.get_query_terms(rect, "")
##
## Each term is the token of a cell, with the marker character in front of
## it for a covering term, and the prefix in front of that. The terms are
## lower case letters, digits, the marker character and the prefix, and the
## prefix tells them apart from the other terms of the same index.
##
## The indexer and the queries must use the same `min_level`, `max_level` and
## `level_mod`, and may use different values of `max_cells`.
##
## The strategy is the one at the top of upstream's source. A region is
## covered by cells. For each cell of the covering the index holds a
## covering term, and an ancestor term for the cell and for each of its
## ancestors. A query region asks for the ancestor terms of its own cells,
## which find the documents that are smaller than the query, and for the
## covering terms of the ancestors of its cells, which find the documents
## that are larger.
S2RegionTermIndexer := {
	coverer : S2RegionCoverer,
	points_only : Bool,
	for_space : Bool,
	marker : U8,
}.{

	## An indexer that uses at most 8 cells for a region, at levels 4 to 16,
	## which suit regions from about 100 metres to 3000 kilometres across.
	## It indexes regions, and favours speed over space.
	default : () -> S2RegionTermIndexer
	default = || {
		coverer: S2RegionCoverer.default().with_min_level(4).with_max_level(16),
		points_only: Bool.False,
		for_space: Bool.False,
		marker: '$',
	}

	## The most cells to use for one region. A larger value makes the terms
	## more exact and more numerous. It may differ between indexing and
	## querying.
	with_max_cells : S2RegionTermIndexer, U64 -> S2RegionTermIndexer
	with_max_cells = |indexer, max_cells| { ..indexer, coverer: indexer.coverer.with_max_cells(max_cells) }

	## The coarsest level of a cell. It must be the same for indexing and
	## querying.
	with_min_level : S2RegionTermIndexer, U64 -> S2RegionTermIndexer
	with_min_level = |indexer, min_level| { ..indexer, coverer: indexer.coverer.with_min_level(min_level) }

	## The finest level of a cell. It must be the same for indexing and
	## querying.
	with_max_level : S2RegionTermIndexer, U64 -> S2RegionTermIndexer
	with_max_level = |indexer, max_level| { ..indexer, coverer: indexer.coverer.with_max_level(max_level) }

	## The step between the levels of a cell, 1, 2 or 3. A larger step gives
	## fewer terms and a coarser covering. It must be the same for indexing
	## and querying.
	with_level_mod : S2RegionTermIndexer, U64 -> S2RegionTermIndexer
	with_level_mod = |indexer, level_mod| { ..indexer, coverer: indexer.coverer.with_level_mod(level_mod) }

	## Whether the index holds only points. If it does, queries need about
	## half as many terms. Then use `get_index_terms_for_point` to index,
	## because a region cannot be indexed.
	with_index_contains_points_only : S2RegionTermIndexer, Bool -> S2RegionTermIndexer
	with_index_contains_points_only = |indexer, points_only| { ..indexer, points_only: points_only }

	## Whether to make the index small rather than the query short. This
	## uses fewer index terms and more query terms, by a factor of about
	## 1.3. It has no effect when the index holds only points.
	with_optimize_for_space : S2RegionTermIndexer, Bool -> S2RegionTermIndexer
	with_optimize_for_space = |indexer, for_space| { ..indexer, for_space: for_space }

	## The byte that marks a covering term, in front of its token. It must
	## not be a letter or a digit. The default is `$`.
	with_marker_character : S2RegionTermIndexer, U8 -> S2RegionTermIndexer
	with_marker_character = |indexer, marker| { ..indexer, marker: marker }

	## The most cells to use for one region.
	max_cells : S2RegionTermIndexer -> U64
	max_cells = |indexer| indexer.coverer.max_cells()

	## The coarsest level of a cell.
	min_level : S2RegionTermIndexer -> U64
	min_level = |indexer| indexer.coverer.min_level()

	## The finest level of a cell.
	max_level : S2RegionTermIndexer -> U64
	max_level = |indexer| indexer.coverer.max_level()

	## The step between the levels of a cell.
	level_mod : S2RegionTermIndexer -> U64
	level_mod = |indexer| indexer.coverer.level_mod()

	## Whether the index holds only points.
	index_contains_points_only : S2RegionTermIndexer -> Bool
	index_contains_points_only = |indexer| indexer.points_only

	## Whether the index is made small rather than the query short.
	optimize_for_space : S2RegionTermIndexer -> Bool
	optimize_for_space = |indexer| indexer.for_space

	## The byte that marks a covering term.
	marker_character : S2RegionTermIndexer -> U8
	marker_character = |indexer| indexer.marker

	## The terms to add to the index for a region, with `prefix` in front of
	## each. The region must be of a type that `S2RegionCoverer` can cover.
	## The index must not be set to hold only points.
	get_index_terms : S2RegionTermIndexer, r, Str -> List(Str)
		where [
			r.cell_union_bound : r -> List(S2CellId),
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	get_index_terms = |indexer, region, prefix|
		indexer.get_index_terms_for_canonical_covering(
			S2CellUnion.from_normalized_cell_ids(indexer.coverer.covering(region)),
			prefix,
		)

	## The terms to look up for a query region. The union of the documents
	## of these terms holds every document whose region meets the query
	## region, and some that come close. `prefix` is the one of indexing.
	get_query_terms : S2RegionTermIndexer, r, Str -> List(Str)
		where [
			r.cell_union_bound : r -> List(S2CellId),
			r.contains_cell : r, S2Cell -> Bool,
			r.may_intersect_cell : r, S2Cell -> Bool,
		]
	get_query_terms = |indexer, region, prefix|
		indexer.get_query_terms_for_canonical_covering(
			S2CellUnion.from_normalized_cell_ids(indexer.coverer.covering(region)),
			prefix,
		)

	## The terms to add to the index for a point. This is faster than the
	## terms of a region, and it works when the index holds only points.
	get_index_terms_for_point : S2RegionTermIndexer, S2Point, Str -> List(Str)
	get_index_terms_for_point = |indexer, point, prefix| {
		id = S2CellId.from_point(point)
		min = indexer.coverer.min_level()
		max = indexer.coverer.max_level()
		step = indexer.coverer.level_mod()
		# The cell at the finest level is the covering of the point. It is an
		# ancestor term only, because no query region has a smaller cell.
		var $terms = []
		var $level = min
		while $level <= max {
			$terms = $terms.append(term(indexer, Ancestor, id.parent_at_level($level), prefix))
			$level = $level + step
		}
		$terms
	}

	## The terms to look up for a query point. This is faster than the terms
	## of a region.
	get_query_terms_for_point : S2RegionTermIndexer, S2Point, Str -> List(Str)
	get_query_terms_for_point = |indexer, point, prefix| {
		id = S2CellId.from_point(point)
		finest = indexer.coverer.true_max_level()
		first = term(indexer, Ancestor, id.parent_at_level(finest), prefix)
		if indexer.points_only {
			return [first]
		}
		# The covering terms of the cell at the finest level and of all its
		# ancestors.
		var $terms = [first]
		var $level = finest
		var $more = finest >= indexer.coverer.min_level()
		while $more {
			$terms = $terms.append(term(indexer, Covering, id.parent_at_level($level), prefix))
			if $level < indexer.coverer.level_mod() + indexer.coverer.min_level() {
				$more = Bool.False
			} else {
				$level = $level - indexer.coverer.level_mod()
			}
		}
		$terms
	}

	## The terms to add to the index for a covering, which a coverer with this
	## indexer's levels gave. The covering is canonical: its cells are at the
	## levels that `min_level`, `max_level` and `level_mod` allow, and it has
	## no cell next to cells that could be joined. The index must not be set
	## to hold only points.
	##
	## Cells of the covering are covering terms, and unless the index is made
	## small they are ancestor terms too. The cells at the finest level are
	## ancestor terms only. Then the ancestors of each cell are ancestor
	## terms, without repeating the ones that the cell before gave.
	get_index_terms_for_canonical_covering : S2RegionTermIndexer, S2CellUnion, Str -> List(Str)
	get_index_terms_for_canonical_covering = |indexer, covering, prefix| {
		finest = indexer.coverer.true_max_level()
		var $terms = []
		var $previous = S2CellId.none()
		for id in covering.cell_ids() {
			level = id.level()
			if level < finest {
				$terms = $terms.append(term(indexer, Covering, id, prefix))
			}
			if level == finest or !indexer.for_space {
				$terms = $terms.append(term(indexer, Ancestor, id, prefix))
			}
			$terms = $terms.concat(ancestor_terms(indexer, id, $previous, Ancestor, prefix))
			$previous = id
		}
		$terms
	}

	## The terms to look up for a covering of the query region, which a
	## coverer with this indexer's levels gave. The covering is canonical, as
	## for `get_index_terms_for_canonical_covering`.
	get_query_terms_for_canonical_covering : S2RegionTermIndexer, S2CellUnion, Str -> List(Str)
	get_query_terms_for_canonical_covering = |indexer, covering, prefix| {
		finest = indexer.coverer.true_max_level()
		var $terms = []
		var $previous = S2CellId.none()
		for id in covering.cell_ids() {
			level = id.level()
			# A cell of the covering is always asked for as an ancestor term.
			$terms = $terms.append(term(indexer, Ancestor, id, prefix))
			# An index of points has no covering terms.
			if !indexer.points_only {
				if indexer.for_space and level < finest {
					$terms = $terms.append(term(indexer, Covering, id, prefix))
				}
				$terms = $terms.concat(ancestor_terms(indexer, id, $previous, Covering, prefix))
				$previous = id
			}
		}
		$terms
	}
}

TermKind : [Ancestor, Covering]

## The text of a term: the prefix, then for a covering term the marker, then
## the token of the cell. There are more ancestor terms than covering
## terms, so the covering terms carry the marker.
term : S2RegionTermIndexer, TermKind, S2CellId, Str -> Str
term = |indexer, kind, id, prefix|
	match kind {
		Ancestor => "${prefix}${id.to_token()}"
		Covering => "${prefix}${Str.from_utf8_lossy([indexer.marker])}${id.to_token()}"
	}

## The terms of the ancestors of `id` at the levels the indexer allows, from
## the finest to the coarsest. It stops at an ancestor that the cell
## `previous` has already given.
ancestor_terms : S2RegionTermIndexer, S2CellId, S2CellId, TermKind, Str -> List(Str)
ancestor_terms = |indexer, id, previous, kind, prefix| {
	min = indexer.coverer.min_level()
	step = indexer.coverer.level_mod()
	var $terms = []
	var $level = id.level()
	var $more = Bool.True
	while $more {
		if $level < step + min {
			$more = Bool.False
		} else {
			$level = $level - step
			ancestor = id.parent_at_level($level)
			already =
				previous != S2CellId.none()
					and previous.level() > $level
					and previous.parent_at_level($level) == ancestor
			if already {
				$more = Bool.False
			} else {
				$terms = $terms.append(term(indexer, kind, ancestor, prefix))
			}
		}
	}
	$terms
}

## True when the terms are the expected ones. A long list is compared by its
## length and by its first and last eight terms.
terms_match : List(Str), U64, List(Str), List(Str) -> Bool
terms_match = |terms, n, first, last|
	terms.len() == n and terms.take_first(first.len()) == first and terms.drop_first(n - last.len()) == last

# Upstream's cases, through tools/s2_oracle.cc. The configurations are those
# of s2region_term_indexer_test.cc (IndexRegionsQueryRegionsOptimizeTime and
# its level_mod, space and points variants, MarkerCharacter and
# MaxLevelSetLoosely) applied to a few points, caps, a rectangle, a loop and a
# cell union.
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["9", "84", "81", "80c", "809", "8084", "8085", "8085c", "80859", "808584", "808581", "808580c", "8085809", "8085809c", "8085809f", "8085809ec", "8085809e9"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e9", "$8085809e9", "$8085809ec", "$8085809f", "$8085809c", "$8085809", "$808580c", "$808581", "$808584", "$80859", "$8085c", "$8085", "$8084", "$809", "$80c", "$81", "$84", "$9"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["5", "44", "43", "43c", "43d", "43cc", "43cd", "43cc4", "43cc5", "43cc5c", "43cc5d", "43cc5dc", "43cc5df", "43cc5df4", "43cc5df3", "43cc5df3c", "43cc5df3f"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3f", "$43cc5df3f", "$43cc5df3c", "$43cc5df3", "$43cc5df4", "$43cc5df", "$43cc5dc", "$43cc5d", "$43cc5c", "$43cc5", "$43cc4", "$43cd", "$43cc", "$43d", "$43c", "$43", "$44", "$5"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["5", "54", "51", "504", "501", "5004", "5001", "50004", "50001", "500004", "500001", "5000004", "5000001", "50000004", "50000001", "500000004", "500000001"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["500000001", "$500000001", "$500000004", "$50000001", "$50000004", "$5000001", "$5000004", "$500001", "$500004", "$50001", "$50004", "$5001", "$5004", "$501", "$504", "$51", "$54", "$5"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), ""), 77, ["$4b3e5c2c", "4b3e5c2c", "4b3e5c3", "4b3e5c4", "4b3e5d", "4b3e5c", "4b3e5", "4b3e4"], ["4b3ef5", "4b3ef4", "4b3ef", "$4b3ef54", "4b3ef54", "$4b3ef59", "4b3ef59", "4b3ef5c"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), ""), 58, ["4b3e5c2c", "$4b3e5c3", "$4b3e5c4", "$4b3e5d", "$4b3e5c", "$4b3e5", "$4b3e4", "$4b3f"], ["$4b3e8ed", "4b3ef4c", "$4b3ef5", "$4b3ef4", "$4b3ef", "4b3ef54", "4b3ef59", "$4b3ef5c"])
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["112820871", "112820874", "11282087", "11282084", "1128209", "112820c", "112821", "112824", "11283", "11284", "1129", "112c", "113", "114", "11", "14", "1"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["112820871", "$112820874", "$11282087", "$11282084", "$1128209", "$112820c", "$112821", "$112824", "$11283", "$11284", "$1129", "$112c", "$113", "$114", "$11", "$14", "$1"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), ""), 49, ["$25", "25", "24", "3", "$27", "27", "$2c", "2c"], ["b4", "$b32ab", "b32ab", "b32ac", "b32b", "b32c", "b33", "b34"])
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["25", "$24", "$3", "27", "2c", "304", "$31", "$34", "31c", "324", "$33", "3ac", "$3b", "$3c", "3b2c", "$3b3", "$3b4", "aad", "$aac", "$ab", "$ac", "$b", "ab4", "acc", "$ad", "ad4", "b2c", "$b3", "$b4", "b32ab", "$b32ac", "$b32b", "$b32c", "$b33", "$b34"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), "") == ["$1", "1", "$3", "3", "$5", "5", "$7", "7", "$9", "9", "$b", "b"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), "") == ["1", "3", "5", "7", "9", "b"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), ""), 59, ["$10cb54", "10cb54", "10cb5", "10cb4", "10cb", "10cc", "10d", "10c"], ["17334", "$17349c", "17349c", "17349", "1734c", "1735", "$1734b", "1734b"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), ""), 42, ["10cb54", "$10cb5", "$10cb4", "$10cb", "$10cc", "$10d", "$10c", "$11"], ["$1732f", "1732ec", "17334", "17349c", "$17349", "$1734c", "$1735", "1734b"])
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["$5", "5", "$7", "7"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["5", "7"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085", "808584", "8085809"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809", "$8085809", "$808584", "$8085"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cd", "43cc5c", "43cc5df"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df", "$43cc5df", "$43cc5c", "$43cd"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["5001", "500004", "5000001"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["5000001", "$5000001", "$500004", "$5001"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["$4b3e5c", "4b3e5c", "4b3f", "$4b3e64", "4b3e64", "$4b3e8c", "4b3e8c", "$4b3ef4", "4b3ef4"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5c", "$4b3f", "4b3e64", "4b3e8c", "4b3ef4"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["1128209", "112824", "1129"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["1128209", "$112824", "$1129"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["$10cb", "10cb", "$10cd", "10cd", "$1733", "1733", "$17349c", "17349c", "1735", "$1734a4", "1734a4", "$1734ac", "1734ac"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cb", "10cd", "1733", "17349c", "$1735", "1734a4", "1734ac"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["809", "8084", "8085", "8085c", "80859", "808584", "808581", "808580c", "8085809", "8085809c", "8085809f", "8085809ec", "8085809e9", "8085809e8c", "8085809e8f", "8085809e8ec", "8085809e8e9", "8085809e8e8c", "8085809e8e8d", "8085809e8e8dc", "8085809e8e8d9", "8085809e8e8d8c", "8085809e8e8d8d", "8085809e8e8d8c4", "8085809e8e8d8c7", "8085809e8e8d8c64", "8085809e8e8d8c61"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e8e8d8c61", "$8085809e8e8d8c61", "$8085809e8e8d8c64", "$8085809e8e8d8c7", "$8085809e8e8d8c4", "$8085809e8e8d8d", "$8085809e8e8d8c", "$8085809e8e8d9", "$8085809e8e8dc", "$8085809e8e8d", "$8085809e8e8c", "$8085809e8e9", "$8085809e8ec", "$8085809e8f", "$8085809e8c", "$8085809e9", "$8085809ec", "$8085809f", "$8085809c", "$8085809", "$808580c", "$808581", "$808584", "$80859", "$8085c", "$8085", "$8084", "$809"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43d", "43cc", "43cd", "43cc4", "43cc5", "43cc5c", "43cc5d", "43cc5dc", "43cc5df", "43cc5df4", "43cc5df3", "43cc5df3c", "43cc5df3f", "43cc5df3e4", "43cc5df3e1", "43cc5df3e0c", "43cc5df3e09", "43cc5df3e094", "43cc5df3e093", "43cc5df3e0924", "43cc5df3e0921", "43cc5df3e09214", "43cc5df3e09213", "43cc5df3e09213c", "43cc5df3e09213f", "43cc5df3e09213f4", "43cc5df3e09213f5"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3e09213f5", "$43cc5df3e09213f5", "$43cc5df3e09213f4", "$43cc5df3e09213f", "$43cc5df3e09213c", "$43cc5df3e09213", "$43cc5df3e09214", "$43cc5df3e0921", "$43cc5df3e0924", "$43cc5df3e093", "$43cc5df3e094", "$43cc5df3e09", "$43cc5df3e0c", "$43cc5df3e1", "$43cc5df3e4", "$43cc5df3f", "$43cc5df3c", "$43cc5df3", "$43cc5df4", "$43cc5df", "$43cc5dc", "$43cc5d", "$43cc5c", "$43cc5", "$43cc4", "$43cd", "$43cc", "$43d"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["501", "5004", "5001", "50004", "50001", "500004", "500001", "5000004", "5000001", "50000004", "50000001", "500000004", "500000001", "5000000004", "5000000001", "50000000004", "50000000001", "500000000004", "500000000001", "5000000000004", "5000000000001", "50000000000004", "50000000000001", "500000000000004", "500000000000001", "5000000000000004", "5000000000000001"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["5000000000000001", "$5000000000000001", "$5000000000000004", "$500000000000001", "$500000000000004", "$50000000000001", "$50000000000004", "$5000000000001", "$5000000000004", "$500000000001", "$500000000004", "$50000000001", "$50000000004", "$5000000001", "$5000000004", "$500000001", "$500000004", "$50000001", "$50000004", "$5000001", "$5000004", "$500001", "$500004", "$50001", "$50004", "$5001", "$5004", "$501"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["$4b3e5d", "4b3e5c", "4b3e5", "4b3e4", "4b3f", "4b3c", "4b3", "$4b3e5f", "$4b3e64", "4b3e7", "$4b3e89", "4b3e8c", "4b3e9", "4b3ec", "$4b3e8b", "$4b3e8d", "$4b3e8ec", "4b3e8f", "$4b3ef5", "4b3ef4", "4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5d", "$4b3e5d", "$4b3e5c", "$4b3e5", "$4b3e4", "$4b3f", "$4b3c", "$4b3", "4b3e5f", "$4b3e5f", "4b3e64", "$4b3e64", "$4b3e7", "4b3e89", "$4b3e89", "$4b3e8c", "$4b3e9", "$4b3ec", "4b3e8b", "$4b3e8b", "4b3e8d", "$4b3e8d", "4b3e8ec", "$4b3e8ec", "$4b3e8f", "4b3ef5", "$4b3ef5", "$4b3ef4", "$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["$10cb5", "10cb4", "10cb", "10cc", "10d", "$10cb7", "$10cb9", "10cbc", "$10cd", "$1732c", "1733", "1734", "173", "$17334", "$17349c", "17349", "1734c", "1735", "$1734b"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cb5", "$10cb5", "$10cb4", "$10cb", "$10cc", "$10d", "10cb7", "$10cb7", "10cb9", "$10cb9", "$10cbc", "10cd", "$10cd", "1732c", "$1732c", "$1733", "$1734", "$173", "17334", "$17334", "17349c", "$17349c", "$17349", "$1734c", "$1735", "1734b", "$1734b"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["9", "81", "809", "8085", "80859", "808581", "8085809", "8085809f", "8085809e9", "8085809e8f", "8085809e8e9", "8085809e8e8d", "8085809e8e8d9", "8085809e8e8d8d", "8085809e8e8d8c7", "8085809e8e8d8c61"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e8e8d8c61"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["5", "43", "43d", "43cd", "43cc5", "43cc5d", "43cc5df", "43cc5df3", "43cc5df3f", "43cc5df3e1", "43cc5df3e09", "43cc5df3e093", "43cc5df3e0921", "43cc5df3e09213", "43cc5df3e09213f", "43cc5df3e09213f5"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3e09213f5"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["5", "51", "501", "5001", "50001", "500001", "5000001", "50000001", "500000001", "5000000001", "50000000001", "500000000001", "5000000000001", "50000000000001", "500000000000001", "5000000000000001"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["5000000000000001"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5c3", "4b3e5d9", "4b3e5dbff", "4b3e5dd", "4b3e5df", "4b3e5f", "4b3e61", "4b3e63", "4b3e640001", "4b3e67", "4b3e89", "4b3e8b", "4b3e8c1", "4b3e8c7", "4b3e8c81", "4b3e8c8201", "4b3e8eb", "4b3e8ecb", "4b3ef5"]
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(30).with_level_mod(2).with_max_cells(20).with_index_contains_points_only(Bool.True).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cb5", "10cb7", "10cb9", "10cd", "173295", "1732b5", "1732b7", "1732b9", "1732bf", "1732d", "1732f", "17331", "17333", "17335", "17337", "173499", "17349f", "1734b"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["809", "8084", "8085", "8085c", "80859", "808584", "808581", "808580c", "8085809", "8085809c", "8085809f", "8085809ec", "8085809e9"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e9"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43d", "43cc", "43cd", "43cc4", "43cc5", "43cc5c", "43cc5d", "43cc5dc", "43cc5df", "43cc5df4", "43cc5df3", "43cc5df3c", "43cc5df3f"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3f"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["501", "5004", "5001", "50004", "50001", "500004", "500001", "5000004", "5000001", "50000004", "50000001", "500000004", "500000001"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["500000001"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5d", "4b3e5f", "4b3e64", "4b3e89", "4b3e8b", "4b3e8d", "4b3e8ec", "4b3ef5"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["112820871"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cb5", "10cb7", "10cb9", "10cd", "1732c", "17334", "17349c", "1734b"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["809", "8084", "8085", "8085c", "80859", "808584", "808581", "808580c", "8085809", "8085809c", "8085809f", "8085809ec", "8085809e9"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e9", "$8085809e9", "$8085809ec", "$8085809f", "$8085809c", "$8085809", "$808580c", "$808581", "$808584", "$80859", "$8085c", "$8085", "$8084", "$809"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43d", "43cc", "43cd", "43cc4", "43cc5", "43cc5c", "43cc5d", "43cc5dc", "43cc5df", "43cc5df4", "43cc5df3", "43cc5df3c", "43cc5df3f"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3f", "$43cc5df3f", "$43cc5df3c", "$43cc5df3", "$43cc5df4", "$43cc5df", "$43cc5dc", "$43cc5d", "$43cc5c", "$43cc5", "$43cc4", "$43cd", "$43cc", "$43d"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["501", "5004", "5001", "50004", "50001", "500004", "500001", "5000004", "5000001", "50000004", "50000001", "500000004", "500000001"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["500000001", "$500000001", "$500000004", "$50000001", "$50000004", "$5000001", "$5000004", "$500001", "$500004", "$50001", "$50004", "$5001", "$5004", "$501"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["$4b3e5d", "4b3e5d", "4b3e5c", "4b3e5", "4b3e4", "4b3f", "4b3c", "4b3", "$4b3e5f", "4b3e5f", "$4b3e64", "4b3e64", "4b3e7", "$4b3e89", "4b3e89", "4b3e8c", "4b3e9", "4b3ec", "$4b3e8b", "4b3e8b", "$4b3e8d", "4b3e8d", "$4b3e8ec", "4b3e8ec", "4b3e8f", "$4b3ef5", "4b3ef5", "4b3ef4", "4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5d", "$4b3e5c", "$4b3e5", "$4b3e4", "$4b3f", "$4b3c", "$4b3", "4b3e5f", "4b3e64", "$4b3e7", "4b3e89", "$4b3e8c", "$4b3e9", "$4b3ec", "4b3e8b", "4b3e8d", "4b3e8ec", "$4b3e8f", "4b3ef5", "$4b3ef4", "$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["112820871", "112820874", "11282087", "11282084", "1128209", "112820c", "112821", "112824", "11283", "11284", "1129", "112c", "113"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["112820871", "$112820874", "$11282087", "$11282084", "$1128209", "$112820c", "$112821", "$112824", "$11283", "$11284", "$1129", "$112c", "$113"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["$10cb5", "10cb5", "10cb4", "10cb", "10cc", "10d", "$10cb7", "10cb7", "$10cb9", "10cb9", "10cbc", "$10cd", "10cd", "$1732c", "1732c", "1733", "1734", "173", "$17334", "17334", "$17349c", "17349c", "17349", "1734c", "1735", "$1734b", "1734b"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cb5", "$10cb4", "$10cb", "$10cc", "$10d", "10cb7", "10cb9", "$10cbc", "10cd", "1732c", "$1733", "$1734", "$173", "17334", "17349c", "$17349", "$1734c", "$1735", "1734b"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e8e9"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e8e9", "$8085809e8e9"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3e09"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3e09", "$43cc5df3e09"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["50000000001"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["50000000001", "$50000000001"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["84", "80c", "8084", "8085c", "808584", "808580c", "8085809c", "8085809ec", "8085809e8c", "8085809e8ec"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e8ec", "$8085809e8ec", "$8085809e8c", "$8085809ec", "$8085809c", "$808580c", "$808584", "$8085c", "$8084", "$80c", "$84"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["44", "43c", "43cc", "43cc4", "43cc5c", "43cc5dc", "43cc5df4", "43cc5df3c", "43cc5df3e4", "43cc5df3e0c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3e0c", "$43cc5df3e0c", "$43cc5df3e4", "$43cc5df3c", "$43cc5df4", "$43cc5dc", "$43cc5c", "$43cc4", "$43cc", "$43c", "$44"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["54", "504", "5004", "50004", "500004", "5000004", "50000004", "500000004", "5000000004", "50000000004"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["50000000004", "$50000000004", "$5000000004", "$500000004", "$50000004", "$5000004", "$500004", "$50004", "$5004", "$504", "$54"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["$4b3e5c", "4b3e5c", "4b3e4", "4b3c", "4b4", "4c", "$4b3e64", "4b3e64", "$4b3e8c", "4b3e8c", "4b3ec", "$4b3ef4c", "4b3ef4c", "4b3ef4", "$4b3ef54", "4b3ef54", "$4b3ef584", "4b3ef584", "4b3ef5c", "$4b3ef59c", "4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5c", "$4b3e4", "$4b3c", "$4b4", "$4c", "4b3e64", "4b3e8c", "$4b3ec", "4b3ef4c", "$4b3ef4", "4b3ef54", "4b3ef584", "$4b3ef5c", "4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["1128208703c", "1128208704", "112820874", "11282084", "112820c", "112824", "11284", "112c", "114", "14"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["1128208703c", "$1128208704", "$112820874", "$11282084", "$112820c", "$112824", "$11284", "$112c", "$114", "$14"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["$24", "24", "$2c", "2c", "$34", "34", "$3ac", "3ac", "3c", "$3b2c", "3b2c", "3b4", "$ac", "ac", "$b2c", "b2c", "b4", "$b32ac", "b32ac", "b32c", "b34"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["24", "2c", "34", "3ac", "$3c", "3b2c", "$3b4", "ac", "b2c", "$b4", "b32ac", "$b32c", "$b34"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), ""), 48, ["$04", "04", "$0c", "0c", "$14", "14", "$1c", "1c"], ["$a4", "a4", "$ac", "ac", "$b4", "b4", "$bc", "bc"])
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), "") == ["04", "0c", "14", "1c", "24", "2c", "34", "3c", "44", "4c", "54", "5c", "64", "6c", "74", "7c", "84", "8c", "94", "9c", "a4", "ac", "b4", "bc"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["$10cc", "10cc", "10c", "14", "$1732c", "1732c", "1734", "174", "$17334", "17334", "$17349c", "17349c", "1734c", "$1734a4", "1734a4", "$1734ac", "1734ac"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cc", "$10c", "$14", "1732c", "$1734", "$174", "17334", "17349c", "$1734c", "1734a4", "1734ac"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["$44", "44", "$4c", "4c", "$54", "54", "$5c", "5c", "$64", "64", "$6c", "6c", "$74", "74", "$7c", "7c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["44", "4c", "54", "5c", "64", "6c", "74", "7c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["84", "80c", "8084", "8085c", "808584", "808580c", "8085809c", "8085809ec", "8085809e8c", "8085809e8ec"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["8085809e8ec", "$8085809e8ec", "$8085809e8c", "$8085809ec", "$8085809c", "$808580c", "$808584", "$8085c", "$8084", "$80c", "$84"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["44", "43c", "43cc", "43cc4", "43cc5c", "43cc5dc", "43cc5df4", "43cc5df3c", "43cc5df3e4", "43cc5df3e0c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5df3e0c", "$43cc5df3e0c", "$43cc5df3e4", "$43cc5df3c", "$43cc5df4", "$43cc5dc", "$43cc5c", "$43cc4", "$43cc", "$43c", "$44"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["54", "504", "5004", "50004", "500004", "5000004", "50000004", "500000004", "5000000004", "50000000004"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["50000000004", "$50000000004", "$5000000004", "$500000004", "$50000004", "$5000004", "$500004", "$50004", "$5004", "$504", "$54"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["$4b3e5c", "4b3e5c", "4b3e4", "4b3c", "4b4", "4c", "$4b3e64", "4b3e64", "$4b3e8c", "4b3e8c", "4b3ec", "$4b3ef4c", "4b3ef4c", "4b3ef4", "$4b3ef54", "4b3ef54", "$4b3ef584", "4b3ef584", "4b3ef5c", "$4b3ef59c", "4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3e5c", "$4b3e4", "$4b3c", "$4b4", "$4c", "4b3e64", "4b3e8c", "$4b3ec", "4b3ef4c", "$4b3ef4", "4b3ef54", "4b3ef584", "$4b3ef5c", "4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["1128208703c", "1128208704", "112820874", "11282084", "112820c", "112824", "11284", "112c", "114", "14"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["1128208703c", "$1128208704", "$112820874", "$11282084", "$112820c", "$112824", "$11284", "$112c", "$114", "$14"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["$24", "24", "$2c", "2c", "$34", "34", "$3ac", "3ac", "3c", "$3b2c", "3b2c", "3b4", "$ac", "ac", "$b2c", "b2c", "b4", "$b32ac", "b32ac", "b32c", "b34"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["24", "2c", "34", "3ac", "$3c", "3b2c", "$3b4", "ac", "b2c", "$b4", "b32ac", "$b32c", "$b34"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), ""), 48, ["$04", "04", "$0c", "0c", "$14", "14", "$1c", "1c"], ["$a4", "a4", "$ac", "ac", "$b4", "b4", "$bc", "bc"])
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), "") == ["04", "0c", "14", "1c", "24", "2c", "34", "3c", "44", "4c", "54", "5c", "64", "6c", "74", "7c", "84", "8c", "94", "9c", "a4", "ac", "b4", "bc"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["$10cc", "10cc", "10c", "14", "$1732c", "1732c", "1734", "174", "$17334", "17334", "$17349c", "17349c", "1734c", "$1734a4", "1734a4", "$1734ac", "1734ac"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cc", "$10c", "$14", "1732c", "$1734", "$174", "17334", "17349c", "$1734c", "1734a4", "1734ac"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_index_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["$44", "44", "$4c", "4c", "$54", "54", "$5c", "5c", "$64", "64", "$6c", "6c", "$74", "74", "$7c", "7c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(20).with_level_mod(2).with_max_cells(8).get_query_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["44", "4c", "54", "5c", "64", "6c", "74", "7c"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["81", "8084", "80859"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "") == ["80859", "$80859", "$8084", "$81"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43", "43cc", "43cc5"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2Point.new(1.0, 2.0, 3.0).normalize(), "") == ["43cc5", "$43cc5", "$43cc", "$43"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["51", "5004", "50001"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_point(S2LatLng.from_degrees(90.0, 0.0).to_point(), "") == ["50001", "$50001", "$5004", "$51"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["$4b3c", "4b"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "") == ["4b3c", "$4b3c", "$4b"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["11283", "112c", "11"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(10.0, 20.0).to_point(), S1Angle.from_degrees(1.0e-05)), "") == ["11283", "$112c", "$11"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["$25", "$27", "$29", "$2b", "$2d", "$2f", "$31", "$33", "$3b", "$ab", "$ad", "$b3"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(-20.0, 100.0).to_point(), S1Angle.from_degrees(30.0)), "") == ["25", "$25", "27", "$27", "29", "$29", "2b", "$2b", "2d", "$2d", "2f", "$2f", "31", "$31", "33", "$33", "3b", "$3b", "ab", "$ab", "ad", "$ad", "b3", "$b3"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), ""), 96, ["$01", "$03", "$05", "$07", "$09", "$0b", "$0d", "$0f"], ["$b1", "$b3", "$b5", "$b7", "$b9", "$bb", "$bd", "$bf"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(0.0, 0.0).to_point(), S1Angle.from_degrees(180.0)), ""), 192, ["01", "$01", "03", "$03", "05", "$05", "07", "$07"], ["b9", "$b9", "bb", "$bb", "bd", "$bd", "bf", "$bf"])
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["$10cc", "11", "$1734", "17"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms(S2LatLngRect.new(R1Interval.new(0.1011, 0.1205), S1Interval.new(0.3779, 0.4031)), "") == ["10cc", "$10cc", "$11", "1734", "$1734", "$17"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), "") == ["$41", "$43", "$45", "$47", "$49", "$4b", "$4d", "$4f", "$51", "$53", "$55", "$57", "$59", "$5b", "$5d", "$5f", "$61", "$63", "$65", "$67", "$69", "$6b", "$6d", "$6f", "$71", "$73", "$75", "$77", "$79", "$7b", "$7d", "$7f"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms(S2CellUnion.from_ids([5764607523034234880, 5170132372221329408, 8070450532247928832]), ""), 64, ["41", "$41", "43", "$43", "45", "$45", "47", "$47"], ["79", "$79", "7b", "$7b", "7d", "$7d", "7f", "$7f"])
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "geo_") == ["geo_809", "geo_8084", "geo_8085", "geo_8085c", "geo_80859", "geo_808584", "geo_808581", "geo_808580c", "geo_8085809", "geo_8085809c", "geo_8085809f", "geo_8085809ec", "geo_8085809e9"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms_for_point(S2LatLng.from_degrees(37.7749, -122.4194).to_point(), "geo_") == ["geo_8085809e9", "geo_$8085809e9", "geo_$8085809ec", "geo_$8085809f", "geo_$8085809c", "geo_$8085809", "geo_$808580c", "geo_$808581", "geo_$808584", "geo_$80859", "geo_$8085c", "geo_$8085", "geo_$8084", "geo_$809"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "geo_") == ["geo_$4b3e5d", "geo_4b3e5d", "geo_4b3e5c", "geo_4b3e5", "geo_4b3e4", "geo_4b3f", "geo_4b3c", "geo_4b3", "geo_$4b3e5f", "geo_4b3e5f", "geo_$4b3e64", "geo_4b3e64", "geo_4b3e7", "geo_$4b3e89", "geo_4b3e89", "geo_4b3e8c", "geo_4b3e9", "geo_4b3ec", "geo_$4b3e8b", "geo_4b3e8b", "geo_$4b3e8d", "geo_4b3e8d", "geo_$4b3e8ec", "geo_4b3e8ec", "geo_4b3e8f", "geo_$4b3ef5", "geo_4b3ef5", "geo_4b3ef4", "geo_4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms(S2Cap.from_center_angle(S2LatLng.from_degrees(44.1, -56.235).to_point(), S1Angle.from_degrees(0.09)), "geo_") == ["geo_4b3e5d", "geo_$4b3e5c", "geo_$4b3e5", "geo_$4b3e4", "geo_$4b3f", "geo_$4b3c", "geo_$4b3", "geo_4b3e5f", "geo_4b3e64", "geo_$4b3e7", "geo_4b3e89", "geo_$4b3e8c", "geo_$4b3e9", "geo_$4b3ec", "geo_4b3e8b", "geo_4b3e8d", "geo_4b3e8ec", "geo_$4b3e8f", "geo_4b3ef5", "geo_$4b3ef4", "geo_$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).with_marker_character(58).get_index_terms_for_point(S2LatLng.from_degrees(10.0, 20.0).to_point(), "") == ["11282087039"]
expect S2RegionTermIndexer.default().with_min_level(20).with_max_level(20).with_level_mod(1).with_max_cells(8).with_marker_character(58).get_query_terms_for_point(S2LatLng.from_degrees(10.0, 20.0).to_point(), "") == ["11282087039", ":11282087039"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).with_marker_character(33).get_index_terms_for_point(S2LatLng.from_degrees(10.0, 20.0).to_point(), "x") == ["x113", "x112c", "x1129", "x11284", "x11283", "x112824", "x112821", "x112820c", "x1128209", "x11282084", "x11282087", "x112820874", "x112820871"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).with_marker_character(33).get_query_terms_for_point(S2LatLng.from_degrees(10.0, 20.0).to_point(), "x") == ["x112820871"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872345448972288), S2CellId.from_id(5421874080615759872), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421877654028550144), S2CellId.from_id(5421879028418084864), S2CellId.from_id(5421879578173898752), S2CellId.from_id(5421880677685526528), S2CellId.from_id(5421880952831868928), S2CellId.from_id(5421883976220409856), S2CellId.from_id(5421884525976223744), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421925001748021248), S2CellId.from_id(5421925414064881664), S2CellId.from_id(5421925499964227584), S2CellId.from_id(5421927887966044160), S2CellId.from_id(5421928003930161152), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422041000224751616)]), ""), 77, ["$4b3e5c2c", "4b3e5c2c", "4b3e5c3", "4b3e5c4", "4b3e5d", "4b3e5c", "4b3e5", "4b3e4"], ["4b3ef5", "4b3ef4", "4b3ef", "$4b3ef54", "4b3ef54", "$4b3ef59", "4b3ef59", "4b3ef5c"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872345448972288), S2CellId.from_id(5421874080615759872), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421877654028550144), S2CellId.from_id(5421879028418084864), S2CellId.from_id(5421879578173898752), S2CellId.from_id(5421880677685526528), S2CellId.from_id(5421880952831868928), S2CellId.from_id(5421883976220409856), S2CellId.from_id(5421884525976223744), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421925001748021248), S2CellId.from_id(5421925414064881664), S2CellId.from_id(5421925499964227584), S2CellId.from_id(5421927887966044160), S2CellId.from_id(5421928003930161152), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422041000224751616)]), ""), 58, ["4b3e5c2c", "$4b3e5c3", "$4b3e5c4", "$4b3e5d", "$4b3e5c", "$4b3e5", "$4b3e4", "$4b3f"], ["$4b3e8ed", "4b3ef4c", "$4b3ef5", "$4b3ef4", "$4b3ef", "4b3ef54", "4b3ef59", "$4b3ef5c"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872345448972288), S2CellId.from_id(5421874080615759872), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421877654028550144), S2CellId.from_id(5421879028418084864), S2CellId.from_id(5421879578173898752), S2CellId.from_id(5421880677685526528), S2CellId.from_id(5421880952831868928), S2CellId.from_id(5421883976220409856), S2CellId.from_id(5421884525976223744), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421925001748021248), S2CellId.from_id(5421925414064881664), S2CellId.from_id(5421925499964227584), S2CellId.from_id(5421927887966044160), S2CellId.from_id(5421928003930161152), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422041000224751616)]), "p:"), 77, ["p:$4b3e5c2c", "p:4b3e5c2c", "p:4b3e5c3", "p:4b3e5c4", "p:4b3e5d", "p:4b3e5c", "p:4b3e5", "p:4b3e4"], ["p:4b3ef5", "p:4b3ef4", "p:4b3ef", "p:$4b3ef54", "p:4b3ef54", "p:$4b3ef59", "p:4b3ef59", "p:4b3ef5c"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872345448972288), S2CellId.from_id(5421874080615759872), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421877654028550144), S2CellId.from_id(5421879028418084864), S2CellId.from_id(5421879578173898752), S2CellId.from_id(5421880677685526528), S2CellId.from_id(5421880952831868928), S2CellId.from_id(5421883976220409856), S2CellId.from_id(5421884525976223744), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421925001748021248), S2CellId.from_id(5421925414064881664), S2CellId.from_id(5421925499964227584), S2CellId.from_id(5421927887966044160), S2CellId.from_id(5421928003930161152), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422041000224751616)]), "p:"), 58, ["p:4b3e5c2c", "p:$4b3e5c3", "p:$4b3e5c4", "p:$4b3e5d", "p:$4b3e5c", "p:$4b3e5", "p:$4b3e4", "p:$4b3f"], ["p:$4b3e8ed", "p:4b3ef4c", "p:$4b3ef5", "p:$4b3ef4", "p:$4b3ef", "p:4b3ef54", "p:4b3ef59", "p:$4b3ef5c"])
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3476778912330022912), S2CellId.from_id(3584865303386914816), S2CellId.from_id(3620894100405878784), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12308337781603565568), S2CellId.from_id(12339862978995159040), S2CellId.from_id(12447949370052050944), S2CellId.from_id(12483978167071014912), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910324795857436672)]), ""), 49, ["$25", "25", "24", "3", "$27", "27", "$2c", "2c"], ["b4", "$b32ab", "b32ab", "b32ac", "b32b", "b32c", "b33", "b34"])
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3476778912330022912), S2CellId.from_id(3584865303386914816), S2CellId.from_id(3620894100405878784), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12308337781603565568), S2CellId.from_id(12339862978995159040), S2CellId.from_id(12447949370052050944), S2CellId.from_id(12483978167071014912), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910324795857436672)]), "") == ["25", "$24", "$3", "27", "2c", "304", "$31", "$34", "31c", "324", "$33", "3ac", "$3b", "$3c", "3b2c", "$3b3", "$3b4", "aad", "$aac", "$ab", "$ac", "$b", "ab4", "acc", "$ad", "ad4", "b2c", "$b3", "$b4", "b32ab", "$b32ac", "$b32b", "$b32c", "$b33", "$b34"]
expect terms_match(S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3476778912330022912), S2CellId.from_id(3584865303386914816), S2CellId.from_id(3620894100405878784), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12308337781603565568), S2CellId.from_id(12339862978995159040), S2CellId.from_id(12447949370052050944), S2CellId.from_id(12483978167071014912), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910324795857436672)]), "p:"), 49, ["p:$25", "p:25", "p:24", "p:3", "p:$27", "p:27", "p:$2c", "p:2c"], ["p:b4", "p:$b32ab", "p:b32ab", "p:b32ac", "p:b32b", "p:b32c", "p:b33", "p:b34"])
expect S2RegionTermIndexer.default().with_min_level(0).with_max_level(16).with_level_mod(1).with_max_cells(20).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3476778912330022912), S2CellId.from_id(3584865303386914816), S2CellId.from_id(3620894100405878784), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12308337781603565568), S2CellId.from_id(12339862978995159040), S2CellId.from_id(12447949370052050944), S2CellId.from_id(12483978167071014912), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910324795857436672)]), "p:") == ["p:25", "p:$24", "p:$3", "p:27", "p:2c", "p:304", "p:$31", "p:$34", "p:31c", "p:324", "p:$33", "p:3ac", "p:$3b", "p:$3c", "p:3b2c", "p:$3b3", "p:$3b4", "p:aad", "p:$aac", "p:$ab", "p:$ac", "p:$b", "p:ab4", "p:acc", "p:$ad", "p:ad4", "p:b2c", "p:$b3", "p:$b4", "p:b32ab", "p:$b32ac", "p:$b32b", "p:$b32c", "p:$b33", "p:$b34"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422039282237833216)]), "") == ["$4b3e5c", "4b3e5c", "4b3f", "$4b3e64", "4b3e64", "$4b3e8c", "4b3e8c", "$4b3ef4", "4b3ef4"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422039282237833216)]), "") == ["4b3e5c", "$4b3f", "4b3e64", "4b3e8c", "4b3ef4"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422039282237833216)]), "p:") == ["p:$4b3e5c", "p:4b3e5c", "p:4b3f", "p:$4b3e64", "p:4b3e64", "p:$4b3e8c", "p:4b3e8c", "p:$4b3ef4", "p:4b3ef4"]
expect S2RegionTermIndexer.default().with_min_level(6).with_max_level(12).with_level_mod(3).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422039282237833216)]), "p:") == ["p:4b3e5c", "p:$4b3f", "p:4b3e64", "p:4b3e8c", "p:4b3ef4"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "") == ["$4b3e5d", "4b3e5c", "4b3e5", "4b3e4", "4b3f", "4b3c", "4b3", "$4b3e5f", "$4b3e64", "4b3e7", "$4b3e89", "4b3e8c", "4b3e9", "4b3ec", "$4b3e8b", "$4b3e8d", "$4b3e8ec", "4b3e8f", "$4b3ef5", "4b3ef4", "4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "") == ["4b3e5d", "$4b3e5d", "$4b3e5c", "$4b3e5", "$4b3e4", "$4b3f", "$4b3c", "$4b3", "4b3e5f", "$4b3e5f", "4b3e64", "$4b3e64", "$4b3e7", "4b3e89", "$4b3e89", "$4b3e8c", "$4b3e9", "$4b3ec", "4b3e8b", "$4b3e8b", "4b3e8d", "$4b3e8d", "4b3e8ec", "$4b3e8ec", "$4b3e8f", "4b3ef5", "$4b3ef5", "$4b3ef4", "$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "p:") == ["p:$4b3e5d", "p:4b3e5c", "p:4b3e5", "p:4b3e4", "p:4b3f", "p:4b3c", "p:4b3", "p:$4b3e5f", "p:$4b3e64", "p:4b3e7", "p:$4b3e89", "p:4b3e8c", "p:4b3e9", "p:4b3ec", "p:$4b3e8b", "p:$4b3e8d", "p:$4b3e8ec", "p:4b3e8f", "p:$4b3ef5", "p:4b3ef4", "p:4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(30).with_level_mod(1).with_max_cells(8).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "p:") == ["p:4b3e5d", "p:$4b3e5d", "p:$4b3e5c", "p:$4b3e5", "p:$4b3e4", "p:$4b3f", "p:$4b3c", "p:$4b3", "p:4b3e5f", "p:$4b3e5f", "p:4b3e64", "p:$4b3e64", "p:$4b3e7", "p:4b3e89", "p:$4b3e89", "p:$4b3e8c", "p:$4b3e9", "p:$4b3ec", "p:4b3e8b", "p:$4b3e8b", "p:4b3e8d", "p:$4b3e8d", "p:4b3e8ec", "p:$4b3e8ec", "p:$4b3e8f", "p:4b3ef5", "p:$4b3ef5", "p:$4b3ef4", "p:$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "") == ["4b3e5d", "4b3e5f", "4b3e64", "4b3e89", "4b3e8b", "4b3e8d", "4b3e8ec", "4b3ef5"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).with_index_contains_points_only(Bool.True).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "p:") == ["p:4b3e5d", "p:4b3e5f", "p:4b3e64", "p:4b3e89", "p:4b3e8b", "p:4b3e8d", "p:4b3e8ec", "p:4b3ef5"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "") == ["$4b3e5d", "4b3e5d", "4b3e5c", "4b3e5", "4b3e4", "4b3f", "4b3c", "4b3", "$4b3e5f", "4b3e5f", "$4b3e64", "4b3e64", "4b3e7", "$4b3e89", "4b3e89", "4b3e8c", "4b3e9", "4b3ec", "$4b3e8b", "4b3e8b", "$4b3e8d", "4b3e8d", "$4b3e8ec", "4b3e8ec", "4b3e8f", "$4b3ef5", "4b3ef5", "4b3ef4", "4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "") == ["4b3e5d", "$4b3e5c", "$4b3e5", "$4b3e4", "$4b3f", "$4b3c", "$4b3", "4b3e5f", "4b3e64", "$4b3e7", "4b3e89", "$4b3e8c", "$4b3e9", "$4b3ec", "4b3e8b", "4b3e8d", "4b3e8ec", "$4b3e8f", "4b3ef5", "$4b3ef4", "$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "p:") == ["p:$4b3e5d", "p:4b3e5d", "p:4b3e5c", "p:4b3e5", "p:4b3e4", "p:4b3f", "p:4b3c", "p:4b3", "p:$4b3e5f", "p:4b3e5f", "p:$4b3e64", "p:4b3e64", "p:4b3e7", "p:$4b3e89", "p:4b3e89", "p:4b3e8c", "p:4b3e9", "p:4b3ec", "p:$4b3e8b", "p:4b3e8b", "p:$4b3e8d", "p:4b3e8d", "p:$4b3e8ec", "p:4b3e8ec", "p:4b3e8f", "p:$4b3ef5", "p:4b3ef5", "p:4b3ef4", "p:4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(4).with_max_level(16).with_level_mod(1).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421873255982039040), S2CellId.from_id(5421875455005294592), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421921634493661184), S2CellId.from_id(5421923833516916736), S2CellId.from_id(5421926032540172288), S2CellId.from_id(5421927956685520896), S2CellId.from_id(5422040381749460992)]), "p:") == ["p:4b3e5d", "p:$4b3e5c", "p:$4b3e5", "p:$4b3e4", "p:$4b3f", "p:$4b3c", "p:$4b3", "p:4b3e5f", "p:4b3e64", "p:$4b3e7", "p:4b3e89", "p:$4b3e8c", "p:$4b3e9", "p:$4b3ec", "p:4b3e8b", "p:4b3e8d", "p:4b3e8ec", "p:$4b3e8f", "p:4b3ef5", "p:$4b3ef4", "p:$4b3ef"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422040948685144064), S2CellId.from_id(5422041051764359168)]), "") == ["$4b3e5c", "4b3e5c", "4b3e4", "4b3c", "4b4", "4c", "$4b3e64", "4b3e64", "$4b3e8c", "4b3e8c", "4b3ec", "$4b3ef4c", "4b3ef4c", "4b3ef4", "$4b3ef54", "4b3ef54", "$4b3ef584", "4b3ef584", "4b3ef5c", "$4b3ef59c", "4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422040948685144064), S2CellId.from_id(5422041051764359168)]), "") == ["4b3e5c", "$4b3e4", "$4b3c", "$4b4", "$4c", "4b3e64", "4b3e8c", "$4b3ec", "4b3ef4c", "$4b3ef4", "4b3ef54", "4b3ef584", "$4b3ef5c", "4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422040948685144064), S2CellId.from_id(5422041051764359168)]), "p:") == ["p:$4b3e5c", "p:4b3e5c", "p:4b3e4", "p:4b3c", "p:4b4", "p:4c", "p:$4b3e64", "p:4b3e64", "p:$4b3e8c", "p:4b3e8c", "p:4b3ec", "p:$4b3ef4c", "p:4b3ef4c", "p:4b3ef4", "p:$4b3ef54", "p:4b3ef54", "p:$4b3ef584", "p:4b3ef584", "p:4b3ef5c", "p:$4b3ef59c", "p:4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421872156470411264), S2CellId.from_id(5421880952563433472), S2CellId.from_id(5421924933028544512), S2CellId.from_id(5422040106871554048), S2CellId.from_id(5422040656627367936), S2CellId.from_id(5422040948685144064), S2CellId.from_id(5422041051764359168)]), "p:") == ["p:4b3e5c", "p:$4b3e4", "p:$4b3c", "p:$4b4", "p:$4c", "p:4b3e64", "p:4b3e8c", "p:$4b3ec", "p:4b3ef4c", "p:$4b3ef4", "p:4b3ef54", "p:4b3ef584", "p:$4b3ef5c", "p:4b3ef59c"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2594073385365405696), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3746994889972252672), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12393906174523604992), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910342388043481088)]), "") == ["$24", "24", "$2c", "2c", "$34", "34", "$3ac", "3ac", "3c", "$3b2c", "3b2c", "3b4", "$ac", "ac", "$b2c", "b2c", "b4", "$b32ac", "b32ac", "b32c", "b34"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2594073385365405696), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3746994889972252672), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12393906174523604992), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910342388043481088)]), "") == ["24", "2c", "34", "3ac", "$3c", "3b2c", "$3b4", "ac", "b2c", "$b4", "b32ac", "$b32c", "$b34"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2594073385365405696), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3746994889972252672), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12393906174523604992), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910342388043481088)]), "p:") == ["p:$24", "p:24", "p:$2c", "p:2c", "p:$34", "p:34", "p:$3ac", "p:3ac", "p:3c", "p:$3b2c", "p:3b2c", "p:3b4", "p:$ac", "p:ac", "p:$b2c", "p:b2c", "p:b4", "p:$b32ac", "p:b32ac", "p:b32c", "p:b34"]
expect S2RegionTermIndexer.default().with_min_level(1).with_max_level(19).with_level_mod(2).with_max_cells(8).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2594073385365405696), S2CellId.from_id(3170534137668829184), S2CellId.from_id(3746994889972252672), S2CellId.from_id(4233383649728266240), S2CellId.from_id(4263782947213017088), S2CellId.from_id(12393906174523604992), S2CellId.from_id(12880294934279618560), S2CellId.from_id(12910342388043481088)]), "p:") == ["p:24", "p:2c", "p:34", "p:3ac", "p:$3c", "p:3b2c", "p:$3b4", "p:ac", "p:b2c", "p:$b4", "p:b32ac", "p:$b32c", "p:$b34"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421208051447234560)]), "") == ["$4b3c", "4b"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421208051447234560)]), "") == ["4b3c", "$4b3c", "$4b"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421208051447234560)]), "p:") == ["p:$4b3c", "p:4b"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(5421208051447234560)]), "p:") == ["p:4b3c", "p:$4b3c", "p:$4b"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(2954361355555045376), S2CellId.from_id(3098476543630901248), S2CellId.from_id(3242591731706757120), S2CellId.from_id(3386706919782612992), S2CellId.from_id(3530822107858468864), S2CellId.from_id(3674937295934324736), S2CellId.from_id(4251398048237748224), S2CellId.from_id(12321848580485677056), S2CellId.from_id(12465963768561532928), S2CellId.from_id(12898309332789100544)]), "") == ["$25", "$27", "$29", "$2b", "$2d", "$2f", "$31", "$33", "$3b", "$ab", "$ad", "$b3"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(2954361355555045376), S2CellId.from_id(3098476543630901248), S2CellId.from_id(3242591731706757120), S2CellId.from_id(3386706919782612992), S2CellId.from_id(3530822107858468864), S2CellId.from_id(3674937295934324736), S2CellId.from_id(4251398048237748224), S2CellId.from_id(12321848580485677056), S2CellId.from_id(12465963768561532928), S2CellId.from_id(12898309332789100544)]), "") == ["25", "$25", "27", "$27", "29", "$29", "2b", "$2b", "2d", "$2d", "2f", "$2f", "31", "$31", "33", "$33", "3b", "$3b", "ab", "$ab", "ad", "$ad", "b3", "$b3"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_index_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(2954361355555045376), S2CellId.from_id(3098476543630901248), S2CellId.from_id(3242591731706757120), S2CellId.from_id(3386706919782612992), S2CellId.from_id(3530822107858468864), S2CellId.from_id(3674937295934324736), S2CellId.from_id(4251398048237748224), S2CellId.from_id(12321848580485677056), S2CellId.from_id(12465963768561532928), S2CellId.from_id(12898309332789100544)]), "p:") == ["p:$25", "p:$27", "p:$29", "p:$2b", "p:$2d", "p:$2f", "p:$31", "p:$33", "p:$3b", "p:$ab", "p:$ad", "p:$b3"]
expect S2RegionTermIndexer.default().with_min_level(2).with_max_level(10).with_level_mod(3).with_max_cells(3).with_optimize_for_space(Bool.True).get_query_terms_for_canonical_covering(S2CellUnion.from_verbatim([S2CellId.from_id(2666130979403333632), S2CellId.from_id(2810246167479189504), S2CellId.from_id(2954361355555045376), S2CellId.from_id(3098476543630901248), S2CellId.from_id(3242591731706757120), S2CellId.from_id(3386706919782612992), S2CellId.from_id(3530822107858468864), S2CellId.from_id(3674937295934324736), S2CellId.from_id(4251398048237748224), S2CellId.from_id(12321848580485677056), S2CellId.from_id(12465963768561532928), S2CellId.from_id(12898309332789100544)]), "p:") == ["p:25", "p:$25", "p:27", "p:$27", "p:29", "p:$29", "p:2b", "p:$2b", "p:2d", "p:$2d", "p:2f", "p:$2f", "p:31", "p:$31", "p:33", "p:$33", "p:3b", "p:$3b", "p:ab", "p:$ab", "p:ad", "p:$ad", "p:b3", "p:$b3"]

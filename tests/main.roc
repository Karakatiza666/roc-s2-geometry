## The test entry point.
##
## The corpora here are hundreds of kilobytes and belong to nobody but this
## repository, so they live outside `src/`, which is what `roc bundle` ships.
## This package reaches the library the way a consumer does, through `s2`, and
## `roc test tests/main.roc` runs the `expect`s of both: the ones beside the
## code in `src/` and the corpus checks imported below.
package
	[]
	{
		s2: "../src/main.roc",
	}

import S2CellIdTest
import S2CellTest
import S2CellUnionTest
import S2ExactTest
import S2LoopRelationTest
import S2PolygonTest
import S2RegionCovererTest
import S2RegionTest
import S2ShapeTest

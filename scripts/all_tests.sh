#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2005 Google Inc. and subsequent S2 Geometry authors, 2026 George Bulakh
# SPDX-License-Identifier: Apache-2.0

# The local and CI checks. Usage: ROC=/path/to/roc scripts/all_tests.sh
#
# `roc test` runs the `expect`s of a path dependency only in the modules its
# importers reach, so `src/main.roc` runs every inline test and
# `tests/main.roc` adds the corpus checks. `--no-cache` makes the result come
# from the sources, not from a cache.
set -euo pipefail
ROC="${ROC:-roc}"
cd "$(dirname "$0")/.."

"$ROC" version
"$ROC" fmt --check src tests examples
"$ROC" check --no-cache src/main.roc
"$ROC" check --no-cache tests/main.roc
"$ROC" test --no-cache src/main.roc
"$ROC" test --no-cache tests/main.roc
for f in examples/*.roc; do
	"$ROC" check --no-cache "$f"
	"$ROC" "$f"
done
"$ROC" docs src/main.roc
# `roc docs` names the site after the directory of main.roc.
find generated-docs -name '*.html' -exec perl -pi -e 's|<title>src Docs</title>|<title>roc-s2-geometry Docs</title>|' {} +

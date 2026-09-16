#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2005 Google Inc. and subsequent S2 Geometry authors, 2026 George Bulakh
# SPDX-License-Identifier: Apache-2.0

# Writes dist/<hash>.tar.zst and lists its files.
set -euo pipefail
ROC="${ROC:-roc}"
cd "$(dirname "$0")/.."

rm -rf dist
mkdir dist
"$ROC" bundle src/main.roc --output-dir dist
zstd -dc dist/*.tar.zst | tar -t

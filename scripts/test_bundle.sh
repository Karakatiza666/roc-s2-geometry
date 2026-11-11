#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Heorhii Bulakh
# SPDX-License-Identifier: UPL-1.0

# Runs the examples against a bundle: a .tar.zst file (default dist/*.tar.zst)
# served on localhost, or a release URL. A path is from the repo root.
set -euo pipefail
ROC="${ROC:-roc}"
cd "$(dirname "$0")/.."
target="${1:-$(echo dist/*.tar.zst)}"

if [[ $target == https://* ]]; then
	url="$target"
else
	port="${PORT:-8765}"
	url="http://127.0.0.1:$port/$(basename "$target")"
	python3 -m http.server "$port" --bind 127.0.0.1 --directory "$(dirname "$target")" >/dev/null 2>&1 &
	server=$!
	trap 'kill "$server"' EXIT
	for _ in $(seq 50); do
		(: >"/dev/tcp/127.0.0.1/$port") 2>/dev/null && break
		sleep 0.1
	done
fi
for f in examples/*.roc; do
	"$ROC" check "$f" --replace-dep ./src/main.roc "$url"
	"$ROC" "$f" --replace-dep ./src/main.roc "$url"
done

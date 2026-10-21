#!/usr/bin/env bash
# Build and render the blueprint (as verso-blueprint's project_template/scripts/ci-pages.sh).
# Run from blueprint/ after the main library is built (`lake build` at the repository root).
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json

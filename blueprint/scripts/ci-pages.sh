#!/usr/bin/env bash
# Build and render the blueprint (as verso-blueprint's project_template/scripts/ci-pages.sh).
# Run from blueprint/ after the main library is built (`lake build` at the repository root).
set -euo pipefail
cd "$(dirname "$0")/.."

# materialize the dependencies, then patch VersoBlueprint's exponential closure walk
lake env true
python3 scripts/patch_versoblueprint.py

lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json

# the rendered dependency graph must be the DAG of digest/00-overview.md §2.1
python3 scripts/check_dag.py

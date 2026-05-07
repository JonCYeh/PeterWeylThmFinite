#!/usr/bin/env bash
# Build the blueprint web pages and patch the rendered HTML so links to
# Lean declarations resolve:
#   - Mathlib decls → mathlib4_docs/find/#doc/X
#   - local decls   → GitHub source with a line anchor
#
# This mirrors what .github/workflows/blueprint.yml does in CI.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

leanblueprint web
python3 scripts/fix_blueprint_links.py

echo
echo "Done. Serve with:  leanblueprint serve   →  http://localhost:8000/"

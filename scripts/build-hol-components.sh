#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

for dir in \
  src/sapic \
  src/translate_to_sapic \
  src/composition/dy_library \
  src/composition/deduction \
  src/composition/general_deduction \
  src/composition/concrete \
  src/composition/plain \
  src/composition/combined_deduction \
  src/refinement \
  src/pretty_print \
  src/tree
do
  (cd "$root/$dir" && Holmake)
done

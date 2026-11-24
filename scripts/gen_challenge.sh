#!/usr/bin/env bash
# Regenerate SignatureVolatilityComparator/Challenge.lean and comparator.json theorem_names
# from the compared targets listed in scripts/ComparatorClosure.lean.in.
# Requires a built SignatureVolatility library.
#
# ComparatorClosure.lean.in is a non-module Lean meta script (it needs the full, non-exported
# view of imported declarations: theorem kinds, declaration ranges, module indices). It is kept
# with a `.in` suffix so the repository's tracked `.lean` files all use the module system
# (Palomar CONTRIBUTING); it is copied to a temporary `.lean` file and run here.
set -euo pipefail
cd "$(dirname "$0")/.."
tmpd="$(mktemp -d)"
trap 'rm -rf "$tmpd"' EXIT
cp scripts/ComparatorClosure.lean.in "$tmpd/ComparatorClosure.lean"
lake env lean "$tmpd/ComparatorClosure.lean" > "$tmpd/closure.tsv"
rm -rf SignatureVolatilityComparator/ChallengeParts
python3 scripts/gen_challenge.py "$tmpd/closure.tsv" SignatureVolatilityComparator/Challenge.lean comparator.json

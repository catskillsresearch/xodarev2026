#!/usr/bin/env bash
# Regenerate SignatureVolatilityComparator/Challenge.lean, ChallengeParts/** and
# comparator.json theorem_names from the compared targets listed in
# scripts/ComparatorClosure.lean. Requires a built SignatureVolatility library.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
lake env lean scripts/ComparatorClosure.lean > "$tmp"
rm -rf SignatureVolatilityComparator/ChallengeParts
python3 scripts/gen_challenge.py "$tmp" SignatureVolatilityComparator/Challenge.lean comparator.json

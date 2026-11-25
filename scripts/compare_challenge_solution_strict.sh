#!/usr/bin/env bash
# Strict local stand-in for Palomar Comparator's `Compare.loop`: fingerprints every constant
# reachable from comparator.json theorem_names in Challenge and in Solution (all namespaces,
# `._proof_N` included; targets by type only) and diffs the two lists. Requires built
# Challenge and Solution modules.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
targets="$(python3 -c 'import json; print(", ".join("`"+n for n in json.load(open("comparator.json"))["theorem_names"]))')"
for role in challenge solution; do
  module="$(python3 -c "import json; print(json.load(open('comparator.json'))['${role}_module'])")"
  sed -e "s|@@MODULE@@|${module}|" -e "s|@@TARGETS@@|${targets}|" scripts/StrictCompare.lean.in \
    >"${tmp}/Strict_${role}.lean"
  lake env lean "${tmp}/Strict_${role}.lean" >"${tmp}/${role}.raw" 2>&1 || { cat "${tmp}/${role}.raw"; exit 1; }
  grep -P '\t' "${tmp}/${role}.raw" >"${tmp}/${role}.txt"
done
n="$(wc -l <"${tmp}/challenge.txt")"
if diff "${tmp}/challenge.txt" "${tmp}/solution.txt" >"${tmp}/diff.txt"; then
  echo "OK: strict closure match (${n} constants, all namespaces, _proof_N included)."
else
  echo "FAIL: strict closure mismatch:"
  head -n 60 "${tmp}/diff.txt"
  exit 1
fi

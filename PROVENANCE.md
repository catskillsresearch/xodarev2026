# Provenance

This repository is a standalone Lean 4 / Mathlib formalization of Akmal
Xodarev, *On the Structural Foundations of Signature Volatility Models*,
arXiv:2605.17142. It is not a thin wrapper and not a reimplementation of an
independent formalization.

**Akmal Xodarev did not participate in, review, or endorse this
formalization.** There are no other human collaborators. The Lean
development was produced by Lars Warren Ericson with AI-agent assistance
under his direction and review. The source paper is cited as literature
only and is not licensed under this repository's Apache-2.0 terms (see
`NOTICE`).

## Framing

Primary story: **rigorous reconstruction / verification** of Xodarev’s
Theorems A–D (existence/uniqueness of the signature SDE; NFLVR and Riccati
duality; price-filtration completeness depth; GKW hedging-error
decomposition with weight-tail bounds).

## Comparator

Compared declarations are `SignatureVolatility.theorem_A` …
`SignatureVolatility.theorem_D`, stated Mathlib-only in
`SignatureVolatilityComparator/Challenge.lean` and proved in the
`SignatureVolatility/` library imported by
`SignatureVolatilityComparator/Solution.lean`. Configuration:
`comparator.json`. Supporting scaffolding appears as type-only holes in
`definition_names`.

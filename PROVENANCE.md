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

Compared declarations are the 11 unwrapped theorems named in
`comparator.json` (Theorems A–D, their refutations, and the two NFLVR
definition-sharpness refutations `not_literal_nflvr_unwrapped` and
`not_terminal_bdd_nflvr_unwrapped`). They are stated Mathlib-only in
`SignatureVolatilityComparator/Challenge.lean` and proved in the
`SignatureVolatility/` library imported by
`SignatureVolatilityComparator/Solution.lean`. The unwrapped statements
live in `SignatureVolatility/Unwrapped.lean`. Configuration:
`comparator.json`. The field `definition_names` is empty: supporting
lemmas in the Challenge are fully proved, not compared holes.

The unwrapped predicate `IsSignaturePrice` requires almost surely continuous
paths on `[0, T]` and almost sure equality, at each time, to the Doléans
exponential of the signature volatility. The packaged `SignaturePriceSolution`
remains a pointwise Doléans representation. The NFLVR conjunct of
`theorem_B_mp_unwrapped` is Delbaen–Schachermayer NFLVR (`SatisfiesNFLVR_DS`)
for the cone `BoundedBelowGains` of that process `S`. The two definition-sharpness
refutations concern the paper's literal cone (no wealth bound) and the
terminal-only bound; they do not refute the uniformly bounded-below statement,
which is proved.


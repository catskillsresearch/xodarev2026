# Abstract

This is a Lean 4 / Mathlib formalization of Akmal Xodarev, *On the Structural Foundations of Signature Volatility Models* [@xodarev2026] (arXiv:2605.17142v1). It proves the paper claims that hold, at the exact strength of the corresponding Lean theorems, and refutes the claims that do not, by Lean negations of those claims and nothing stronger.

The library contains 212 first-party `.lean` files. The holes board lists 209 modules done, with 0 open, 0 blocked, and no `sorry`. The comparator checks 9 theorems (Theorems A–D and their refutations, in unwrapped form): none is open. Palomar registration: TBD. The official Palomar abstract is the `project.description` field of `formalization.yaml`; it is reproduced verbatim in the section "Palomar registration and main results", together with a table that maps each headline claim to its Lean theorem and exact strength.

Source paper: Xodarev [@xodarev2026]. AI assistance is acknowledged at the end with model cards for Google Gemini Carbon, Cursor Composer, Cursor Grok, Claude Fable 2, and Cursor Auto.

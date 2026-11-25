# Why Theorem C (paper Thm 56 / PDF Thm 5.3) fails

**Lean:** `not_theorem_C`, `theorem_C_refuted`, `blackScholes_isCompleteWithCalls`
(`TheoremCCounterExample.lean`, `TheoremC.lean`), with `theorem_C_depth_infinite` and
`theorem_C_blackScholes_depth_infinite`. All are compared.

**Claim.** The market of `S` plus finitely many calls is complete on `ℱ^S_T` iff `N^*_S < ∞`.

**Counterexample.** Take the Black–Scholes market (`d = 1`, `σ ≡ σ₀ ≠ 0`, any `T > 0`, `s₀ > 0`)
and any finite strike set. Lean shows two things:

- The market is complete. The price filtration equals the Brownian filtration, and every
  `X ∈ L²(ℱ^S_T)` is `E X` plus an Itô integral by Brownian martingale representation, so no calls
  are needed.
- Its completeness depth is `N^*_S = ∞`. Depth `N` would require `L²(ℱ^S_T)` to be the closed span
  of the finitely many signature coordinates of level `≤ N`, a finite-dimensional space. But
  `L²(ℱ^S_T)` is infinite-dimensional (see `prop58.md`).

So the left side of the iff holds and the right side fails. More generally,
`theorem_C_depth_infinite` gives `N^*_S = ∞` for every model with infinite-dimensional `L²(ℱ^S_T)`.

**Source material.** No verbatim Carbon text for this refutation was found in the repository
or `.carbon/`. See `README.md`.

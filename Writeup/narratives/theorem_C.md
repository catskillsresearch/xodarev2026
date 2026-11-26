# Why Theorem C (paper Thm 56 / PDF Thm 5.3) fails

**Lean:** compared: `not_theorem_C_unwrapped` (`Unwrapped`), where "complete" means every
`X ∈ L²(ℱ^S_T)` is a.s. `c + Σ_k a_k (S_T − k)^+ + G` with `G` in the `L²`-closed span of the
elementary Brownian integrals `Σ_p h_p (W_{p.2} − W_{p.1})` on `[0, T]` (`h_p` bounded and
`σ(W_u : u ≤ p.1)`-measurable). Proved in the library, not compared: `not_theorem_C`,
`theorem_C_refuted`, `blackScholes_isCompleteWithCalls` (`TheoremCCounterExample`,
`TheoremC`; gains are MathFin Itô integrals), `bsMarket_isCompleteWithCallsUnwrapped`,
`theorem_C_depth_infinite` and `theorem_C_blackScholes_depth_infinite`.

**Claim.** The market of `S` plus finitely many calls is complete on `ℱ^S_T` iff `N^*_S < ∞`.

**Counterexample.** Take the Black–Scholes market (`d = 1`, `σ ≡ σ₀ ≠ 0`, any `T > 0`, `s₀ > 0`)
and any finite strike set. Lean shows two things:

- The market is complete. The price filtration equals the Brownian filtration, and every
  `X ∈ L²(ℱ^S_T)` is `E X` plus an Itô integral by Brownian martingale representation, so no calls
  are needed. Each Itô integral lies in the closed span of elementary integrals, because simple
  integrands are dense and the Itô integral is an isometry.
- Its completeness depth is `N^*_S = ∞`. Depth `N` would require `L²(ℱ^S_T)` to be the closed span
  of the finitely many signature coordinates of level `≤ N`, a finite-dimensional space. But
  `L²(ℱ^S_T)` is infinite-dimensional.

So the left side of the iff holds and the right side fails. More generally,
`theorem_C_depth_infinite` gives `N^*_S = ∞` for every model with infinite-dimensional `L²(ℱ^S_T)`.

**Source material.** No verbatim Carbon text for this refutation was

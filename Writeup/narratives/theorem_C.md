# Why the unconditional completeness equivalence fails

**Lean:** compared: `not_theorem_C_unwrapped`, where "complete" means every
`X ∈ L²(ℱ^S_T)` is a.s. `c + Σ_k a_k (S_T − k)^+ + G` with `G` in the `L²`-closed span of the
elementary Brownian integrals `Σ_p h_p (W_{p.2} − W_{p.1})` on `[0, T]` (`h_p` bounded and
`σ(W_u : u ≤ p.1)`-measurable). Proved in the library, not compared: `not_theorem_C`,
`theorem_C_refuted`, `blackScholes_isCompleteWithCalls` (gains are MathFin Itô integrals),
`bsMarket_isCompleteWithCallsUnwrapped`, `theorem_C_depth_infinite` and
`theorem_C_blackScholes_depth_infinite`.

**Claim.** The *unconditional* form of the completeness-depth equivalence: for an arbitrary
finite set of call strikes, the market of `S` plus those calls is complete on `ℱ^S_T` if and
only if `N^*_S < ∞`. This is not the statement of the paper's Theorem 56, which restricts the
equivalence to the finite-polynomial subcase `K(N^*_S) < ∞` and to a strike set rich enough
to span polynomials in `S_T` of degree at most `K(N^*_S)`. Separately, the paper claims that
Black–Scholes has completeness depth `N^*_S = 0` (Proposition 58).

**What is shown.** Take the Black–Scholes market (`d = 1`, `σ ≡ σ₀ ≠ 0`, any `T > 0`, `s₀ > 0`)
and any finite strike set. Lean shows two things:

- The market is complete. The price filtration equals the Brownian filtration, and every
  `X ∈ L²(ℱ^S_T)` is `E X` plus an Itô integral by Brownian martingale representation, so no calls
  are needed. Each Itô integral lies in the closed span of elementary integrals, because simple
  integrands are dense and the Itô integral is an isometry.
- Under Definition 55, the completeness depth is `N^*_S = ∞`. Depth `N` would require
  `L²(ℱ^S_T)` to be the closed span of the finitely many signature coordinates of level `≤ N`,
  a finite-dimensional space. But `L²(ℱ^S_T)` is infinite-dimensional.

So the left side of the unconditional iff holds and the right side fails, and the paper's
Black–Scholes depth claim is also false. This is not a counterexample inside Theorem 56's
finite-polynomial, rich-strike hypotheses: those require `K(N^*_S) < ∞`, which the Black–Scholes
witness does not satisfy, because Definition 55 already gives `N^*_S = ∞`. More generally,
`theorem_C_depth_infinite` gives `N^*_S = ∞` for every model with infinite-dimensional `L²(ℱ^S_T)`.

**Source material.** No verbatim Carbon text for this refutation was available; the narrative
is taken from the Lean proofs.

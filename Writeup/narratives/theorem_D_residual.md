# Theorem D (paper Thm 66): the residual-expansion hypothesis fails for Black–Scholes

**Lean:** `theorem_D_residual_hypothesis_fails` (`TheoremDCounterExample`), compared as
`theorem_D_residual_hypothesis_fails_unwrapped` (`Unwrapped`). The GKW projection part
`theorem_D` is proved and compared as `theorem_D_unwrapped`.

**What is shown.** Theorem 66's residual expansion assumes `N^*_S < ∞`. For Black–Scholes, Lean
proves `¬ (N^*_S < ∞)`, because `N^*_S = ∞`. So the clause is vacuous for the
paper's own basic example.

This shows that the residual expansion's hypothesis fails. It does **not** show that the
expansion is false when its hypothesis holds. Under Definition 55, `N^*_S < ∞` forces
`L²(ℱ^S_T)` to be finite-dimensional.


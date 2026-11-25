# Why Proposition 58 (PDF Prop. 5.5) fails

**Lean:** `not_prop58_blackScholes_depth_zero`, `blackScholes_completenessDepth_eq_top`
(`Prop58BlackScholesDepthFalse.lean`). Both are compared.

**Claim.** Black–Scholes has `(N^*_S, K) = (0, 1)`.

**Counterexample.** Under Definition 55, `N^*_S = 0` means `L²(ℱ^S_T)` is the closed span of
`⟨e_∅, Ŵ_T⟩ = 1`, that is, only constants. In Black–Scholes,
`S_T = s₀ exp(σ₀ W_T − σ₀² T/2)`, so `W_T` is `ℱ^S_T`-measurable. The events
`{W_T ∈ (k, k+1]}`, `k ∈ ℕ`, are disjoint, lie in `ℱ^S_T` and have positive probability. So
`L²(ℱ^S_T)` is infinite-dimensional.

No finite-level span is dense, so Lean proves `N^*_S = ∞`, in particular `≠ 0`. The Lean statement
is `completenessDepth ≠ 0` (with `= ⊤` alongside) for every `T > 0`, `s₀ > 0`, `σ₀ ≠ 0` and every
driver `B`.

**Source material.** No verbatim Carbon text for this refutation was found in the repository
or `.carbon/`. See `README.md`.

module

public import SignatureVolatility.GKWDecompositionSetup.OfPFS

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace SignatureVolatility

/-!
# Theorem D (paper Theorem 66): the hedging-error decomposition

* **GKW projection part (proved).** `theorem_D` is `MarketData.gkw_decomposition`. For every
  `X ∈ L²(ℱ^S_T, ℚ)` there is a unique decomposition `X = E[X] + G + ε`, where `G` lies in the
  closed span `H0` of constants and stochastic integrals against `S` and has mean zero, and
  `ε ⊥ H0` (in particular `ε` is orthogonal to every stochastic integral against `S`). The
  Pythagorean variance identity also holds.
  Identifying `G` as a single integral `∫ H^X dS` needs the gains space to be closed
  (Kunita–Watanabe). That step is not formalised.
* **Residual expansion part.** The expansion of `ε` is stated "if `N^*_S < ∞`". Under the
  paper's Definition 55 that hypothesis fails in every non-degenerate market (see `TheoremC`),
  so this part is vacuous there. For Black–Scholes this is `theorem_D_residual_hypothesis_fails` in
  `TheoremDCounterExample` (board label `CounterExample_TheoremD`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem D / Theorem 66 (GKW part).** -/
theorem theorem_D (mkt : MarketData Ω P) (X : Lp ℝ 2 P) (hX : X ∈ mkt.L2S) :
    ∃ G ε : Lp ℝ 2 P,
      G ∈ mkt.H0 ∧ ⟪G, MarketData.oneLp P⟫ = 0 ∧ ε ∈ mkt.L2S ∧ ε ∈ mkt.H0ᗮ ∧
      (∀ Z ∈ mkt.gainsSet, ⟪ε, Z⟫ = 0) ∧
      X = (∫ ω, X ω ∂P) • MarketData.oneLp P + G + ε ∧
      ‖X‖ ^ 2 = ‖(∫ ω, X ω ∂P) • MarketData.oneLp P + G‖ ^ 2 + ‖ε‖ ^ 2 ∧
      ∀ (c : ℝ) (G' ε' : Lp ℝ 2 P), G' ∈ mkt.H0 → ⟪G', MarketData.oneLp P⟫ = 0 →
        ε' ∈ mkt.H0ᗮ → X = c • MarketData.oneLp P + G' + ε' →
          c = ∫ ω, X ω ∂P ∧ G' = G ∧ ε' = ε :=
  mkt.gkw_decomposition X hX

end SignatureVolatility

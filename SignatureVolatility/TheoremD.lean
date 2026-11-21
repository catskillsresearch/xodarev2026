module

public import SignatureVolatility.GKWDecompositionSetup.OfPFS
public import SignatureVolatility.TheoremDOfMarketKit
public import SignatureVolatility.Weight


@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace SignatureVolatility

/-- **Paper Theorem D.** GKW hedging-error decomposition over a market. -/
theorem theorem_D
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (mkt : MarketData Ω P) (w : Weight) :
    (∀ X : ℝ, ∃ ε_T : ℝ,
      X = (gkwDecompositionSetup_of_pfs mkt w).expectationPart X +
        (gkwDecompositionSetup_of_pfs mkt w).stochasticIntegralPart X + ε_T ∧
      (∀ Z ∈ (gkwDecompositionSetup_of_pfs mkt w).replicableSubspace, ⟪ε_T, Z⟫ = 0) ∧
      ‖X‖ ^ 2 =
        ‖(gkwDecompositionSetup_of_pfs mkt w).expectationPart X +
            (gkwDecompositionSetup_of_pfs mkt w).stochasticIntegralPart X‖ ^ 2 +
          ‖ε_T‖ ^ 2) ∧
    (∀ (w' : Weight) (b : ExtTensorAlgebra (mkt.M.d + 1)) (_hb : MemTw w' b)
        (N : ℕ) (ρ_N : ℝ) (_hρ : 0 ≤ ρ_N),
      (∀ n : ℕ, N < n → w n / w' n ≤ ρ_N) →
      ∃ Z ∈ (gkwDecompositionSetup_of_pfs mkt w).replicableSubspace ⊔
          (priceFiltrationSignatureSpace_of_market mkt).V_subspace N,
        ‖(gkwDecompositionSetup_of_pfs mkt w).evalSig b - Z‖ ≤
          (gkwDecompositionSetup_of_pfs mkt w).C_sig * ρ_N * normW w' b) ∧
    ((priceFiltrationSignatureSpace_of_market mkt).V_infty = ⊤ →
      ∀ N : ℕ,
        (priceFiltrationSignatureSpace_of_market mkt).completenessDepth ≤ (N : ℕ∞) →
          ∀ X : ℝ,
            X ∈ (gkwDecompositionSetup_of_pfs mkt w).replicableSubspace ⊔
              (priceFiltrationSignatureSpace_of_market mkt).V_subspace N) :=
  theorem_D_of_Market_Kit (gkwDecompositionSetup_of_pfs mkt w)

end SignatureVolatility

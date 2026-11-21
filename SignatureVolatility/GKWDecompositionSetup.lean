import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.MemL2wInv
import SignatureVolatility.Norm2wInv
import SignatureVolatility.PriceFiltrationSignatureSpace
import SignatureVolatility.PriceFiltrationSignatureSpace.VSubspace
import SignatureVolatility.ProjLe
import SignatureVolatility.Weight

noncomputable section

namespace SignatureVolatility

def replicableStarProjection {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    (K : Submodule ℝ H_S) [hK : K.HasOrthogonalProjection] (X : H_S) : H_S :=
  K.starProjection X

/-- From closedness in a complete inner product space (Mathlib `ofCompleteSpace`). -/
lemma replicable_hasOrthProj_of_closed {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] (K : Submodule ℝ H_S) (hK_closed : IsClosed (K : Set H_S)) :
    K.HasOrthogonalProjection := by
  haveI : CompleteSpace ↥K := hK_closed.completeSpace_coe
  exact inferInstance

structure GKWDecompositionSetup (H_S : Type*) [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S] (d : ℕ) (w : Weight)
    (PFS : PriceFiltrationSignatureSpace H_S d) where
  /-- Closed dynamic-replicable subspace `ℋ_0 := span{1} ⊔ dynamicGainSubspace` (assumed closed by
  Itô/martingale isometry of `L^2(S)`). -/
  replicableSubspace : Submodule ℝ H_S
  replicable_closed : IsClosed (replicableSubspace : Set H_S)
  replicable_hasOrthProj : Submodule.HasOrthogonalProjection replicableSubspace
  /-- Expectation functional `E_ℚ[X]` as an orthogonal projection onto constants. -/
  expectationPart : H_S →L[ℝ] H_S
  /-- Dynamic stochastic integral component `∫_0^T H^X_s dS_s` inside `replicableSubspace`. -/
  stochasticIntegralPart : H_S →L[ℝ] H_S
  /-- Every element in the orthogonal projection onto `replicableSubspace` splits into
  `expectationPart X + stochasticIntegralPart X`. -/
  orthProj_split : ∀ X : H_S,
    @replicableStarProjection H_S _ _ replicableSubspace replicable_hasOrthProj X =
      expectationPart X + stochasticIntegralPart X
  /-- Evaluation map sending a formal series `b ∈ T_{w'}` to the payoff `⟨b, Ŵ_T⟩` projected onto
  `H_S = L^2(ℱ^S_T, ℚ)`, satisfying `‖evalSig b‖_{L^2} ≤ C_sig ‖b‖_{2, w^{-1}}`. -/
  C_sig : ℝ
  hC_sig_nonneg : 0 ≤ C_sig
  evalSig : ExtTensorAlgebra (d + 1) → H_S
  evalSig_add : ∀ a b, evalSig (a + b) = evalSig a + evalSig b
  evalSig_le_in_V : ∀ N : ℕ, ∀ b : ExtTensorAlgebra (d + 1),
    evalSig (projLe N b) ∈ PFS.V_subspace N
  evalSig_l2_bound : ∀ b : ExtTensorAlgebra (d + 1), MemL2wInv w b →
    ‖evalSig b‖ ≤ C_sig * norm2wInv w b

end SignatureVolatility
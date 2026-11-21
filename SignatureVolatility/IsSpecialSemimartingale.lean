import SignatureVolatility.IndexedFiltration


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

structure IsSpecialSemimartingale {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) (ℱ : IndexedFiltration Ω) (T : ℝ) (X : ℝ → Ω → ℝ) where
  M_part : ℝ → Ω → ℝ
  A_part : ℝ → Ω → ℝ
  decomp : ∀ t ∈ Icc 0 T, ∀ ω, X t ω = X 0 ω + M_part t ω + A_part t ω
  M_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    Integrable (M_part t) ℙ ∧ ℙ[M_part t | ℱ.σAlg s] =ᵐ[ℙ] M_part s
  M_l2_bdd : Integrable (fun ω => (M_part T ω) ^ 2) ℙ
  A_integrable_var : ∃ V : Ω → ℝ, Integrable V ℙ ∧ ∀ t ∈ Icc 0 T, ∀ ω, |A_part t ω| ≤ V ω

end SignatureVolatility

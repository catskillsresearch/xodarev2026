module

public import SignatureVolatility.IndexedFiltration

@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Special semimartingale on `[0, T]`** (paper Lemma 43): `X = X₀ + M + A` with `M₀ = A₀ = 0`,
`M` an a.s. continuous square-integrable true martingale and `A` an a.s. continuous adapted
finite-variation part of integrable total variation on `[0, T]`. -/
structure IsSpecialSemimartingale {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) (ℱ : IndexedFiltration Ω) (T : ℝ) (X : ℝ → Ω → ℝ) where
  M_part : ℝ → Ω → ℝ
  A_part : ℝ → Ω → ℝ
  decomp : ∀ t ∈ Icc 0 T, ∀ ω, X t ω = X 0 ω + M_part t ω + A_part t ω
  M_zero : ∀ ω, M_part 0 ω = 0
  A_zero : ∀ ω, A_part 0 ω = 0
  M_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    Integrable (M_part t) ℙ ∧ ℙ[M_part t | ℱ.σAlg s] =ᵐ[ℙ] M_part s
  M_l2_bdd : Integrable (fun ω => (M_part T ω) ^ 2) ℙ
  M_cont : ∀ᵐ ω ∂ℙ, ContinuousOn (fun t => M_part t ω) (Icc 0 T)
  A_cont : ∀ᵐ ω ∂ℙ, ContinuousOn (fun t => A_part t ω) (Icc 0 T)
  A_adapted : ∀ t ∈ Icc 0 T, Measurable[ℱ.σAlg t] (A_part t)
  A_integrable_var : ∃ V : Ω → ℝ, Integrable V ℙ ∧
    ∀ᵐ ω ∂ℙ, eVariationOn (fun t => A_part t ω) (Icc 0 T) ≤ ENNReal.ofReal (V ω)

end SignatureVolatility

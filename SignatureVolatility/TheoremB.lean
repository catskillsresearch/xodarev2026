import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.SignatureRiccatiKit
import SignatureVolatility.SatisfiesNFLVR
import SignatureVolatility.IsSpecialSemimartingale
import SignatureVolatility.ProlongedBrownianSetup


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

theorem theorem_B {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup)
    (ricKit : SignatureRiccatiKit Ω ℙ M setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      -- (1) `S` is a true `(ℱ^{\widehat{W}}_t, ℙ)`-martingale on `[0, T]`:
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) ℙ ∧
        ℙ[sol.S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] sol.S s) ∧
      -- (2) NFLVR holds on `[0, T]`:
      SatisfiesNFLVR ℙ (AdmissibleGainsUnderP ℙ) ∧
      -- (3) Every finite signature coordinate is a special semimartingale:
      (∀ I : Word (M.d + 1),
        IsSpecialSemimartingale ℙ setup.signatureFiltration M.T
          (fun t ω => (setup.W_hat t ω).coeff I)) ∧
      -- (4) Exponential-affine conditional transform iff global Riccati solution on `[0, T]`:
      (∀ u₀ : FreeTensorAlgebra (M.d + 1),
        Nonempty (ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1) →
        ∃ rSol : ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
            ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
              setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (setup.W_hat t ω))) := by
  obtain ⟨sol, _⟩ := theorem_A M setup ito
  refine ⟨sol, sol.is_martingale, nflvr_of_martingale_measure ℙ,
    ricKit.coord_special_semimartingale, fun u₀ hne => ?_⟩
  exact (ricKit.affine_riccati_duality u₀).mpr hne

/-! ## Section 5: Option-Span Completeness Criterion and Price-Filtration Depth (Theorem C) -/

end SignatureVolatility

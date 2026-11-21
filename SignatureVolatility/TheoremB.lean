import SignatureVolatility.AdmissibleGainsUnderP
import SignatureVolatility.ClassicalRiccatiSolution
import SignatureVolatility.DualPairing
import SignatureVolatility.ExtTensorAlgebra.FreeTensorAlgebra
import SignatureVolatility.IsSpecialSemimartingale
import SignatureVolatility.ItoCalculusKit
import SignatureVolatility.NflvrOfMartingaleMeasure
import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
import SignatureVolatility.ProlongedBrownianSetup.WHat
import SignatureVolatility.SatisfiesNFLVR
import SignatureVolatility.SignaturePriceSolution
import SignatureVolatility.SignatureRiccatiKit
import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.TheoremA
import SignatureVolatility.Word

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

theorem theorem_B {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup)
    (ricKit : SignatureRiccatiKit Ω ℙ M setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) ℙ ∧
        ℙ[sol.S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] sol.S s) ∧
      SatisfiesNFLVR ℙ (AdmissibleGainsUnderP ℙ) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale ℙ setup.signatureFiltration M.T
          (fun t ω => (setup.W_hat t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        Nonempty (ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1) →
        ∃ rSol : ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
            ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
              setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (setup.W_hat t ω))) := by
  obtain ⟨sol, _⟩ := theorem_A M setup ito
  refine ⟨sol, sol.is_martingale, nflvr_of_martingale_measure ℙ,
    fun I => ⟨ricKit.coord_special_semimartingale I⟩, fun u₀ hne => ?_⟩
  exact (ricKit.affine_riccati_duality u₀).mpr hne

end SignatureVolatility
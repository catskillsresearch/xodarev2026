module

public import SignatureVolatility.AdmissibleGainsUnderP
public import SignatureVolatility.ClassicalRiccatiSolution
public import SignatureVolatility.DualPairing
public import SignatureVolatility.ExtTensorAlgebra.FreeTensorAlgebra
public import SignatureVolatility.IsSpecialSemimartingale
public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.NflvrOfMartingaleMeasure
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.SatisfiesNFLVR
public import SignatureVolatility.SignaturePriceSolution
public import SignatureVolatility.SignatureRiccatiKit
public import SignatureVolatility.SignatureVolatilityModel
public import SignatureVolatility.TheoremAOfBrownianSetupItoKit
public import SignatureVolatility.Word


@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

/-- Kit-level Theorem B: NFLVR + Riccati transform duality, *assuming* a `SignatureRiccatiKit`.
This is an implication from an abstract kit whose `affine_riccati_duality` field is the paper
iff. The paper operator `riccatiOp` does not inhabit such a kit
(`not_affine_riccati_duality`); there is no `signatureRiccatiKit_of_setup`. -/
theorem theorem_B_of_Setup_Ito_Riccati_Kit {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup)
    (h3 : HypH3 ℙ M.T (SignatureVolatilityModel.sigma M setup))
    (hcont : ∀ᵐ ω ∂ℙ,
      ContinuousOn (fun s => SignatureVolatilityModel.sigma M setup s ω) (Icc 0 M.T))
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
        SignatureTransformFinite ℙ setup u₀.1 →
        Nonempty (ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1) →
        ∃ rSol : ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
            ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
              setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (setup.W_hat t ω))) := by
  obtain ⟨sol, _⟩ := theorem_A_of_Brownian_Setup_Ito_Kit M setup ito h3 hcont
  refine ⟨sol, sol.is_martingale, nflvr_of_martingale_measure ℙ,
    fun I => ⟨ricKit.coord_special_semimartingale I⟩, fun u₀ hfin hne => ?_⟩
  exact (ricKit.affine_riccati_duality u₀ hfin).mpr hne

end SignatureVolatility

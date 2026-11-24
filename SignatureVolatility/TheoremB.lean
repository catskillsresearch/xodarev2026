module

public import SignatureVolatility.AdmissibleGainsUnderP
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.SatisfiesNFLVR
public import SignatureVolatility.SignatureRiccatiKit.OfSetup
public import SignatureVolatility.TheoremBOfSetupItoRiccatiKit


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem B.** NFLVR + Riccati transform non-explosion over Brownian motion. -/
theorem theorem_B (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ (sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT)),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) P ∧
        P[sol.S t | (paperSetup B M.hT).signatureFiltration.σAlg s] =ᵐ[P] sol.S s) ∧
      SatisfiesNFLVR P (AdmissibleGainsUnderP P) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale P
          (paperSetup B M.hT).signatureFiltration M.T
          (fun t ω => ((paperSetup B M.hT).W_hat t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
        Nonempty (ClassicalRiccatiSolution M.w M.T
          (signatureRiccatiKit_of_setup M B).R_op u₀.1) →
        ∃ rSol : ClassicalRiccatiSolution M.w M.T
            (signatureRiccatiKit_of_setup M B).R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1
              ((paperSetup B M.hT).W_hat M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1
                ((paperSetup B M.hT).W_hat M.T ω)) |
              (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t))
                ((paperSetup B M.hT).W_hat t ω))) :=
  theorem_B_of_Setup_Ito_Riccati_Kit M (paperSetup B M.hT)
    (itoCalculusKit_of_mathfin B M.hT) h3
    (ae_continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1)
    (signatureRiccatiKit_of_setup M B)


/-- **Paper Theorem B, proved part** (no dependence on the open `affine_riccati_duality`): the
Theorem A price is a martingale on the signature filtration, NFLVR holds, and every signature
coordinate is a special semimartingale (Lemma 43). The Riccati clause of `theorem_B` is still
open (`signatureRiccatiKit_of_setup.affine_riccati_duality`). -/
theorem theorem_B_proved (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ (sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT)),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) P ∧
        P[sol.S t | (paperSetup B M.hT).signatureFiltration.σAlg s] =ᵐ[P] sol.S s) ∧
      SatisfiesNFLVR P (AdmissibleGainsUnderP P) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale P
          (paperSetup B M.hT).signatureFiltration M.T
          (fun t ω => ((paperSetup B M.hT).W_hat t ω).coeff I))) := by
  obtain ⟨sol, _⟩ := theorem_A_of_Brownian_Setup_Ito_Kit M (paperSetup B M.hT)
    (itoCalculusKit_of_mathfin B M.hT) h3
    (ae_continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1)
  exact ⟨sol, sol.is_martingale, nflvr_of_martingale_measure P,
    fun I => ⟨isSpecialSemimartingale_paperSig2_coeff B I M.hT⟩⟩

end SignatureVolatility

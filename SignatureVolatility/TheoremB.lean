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
    (ae_of_all P fun ω => continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1 ω)
    (signatureRiccatiKit_of_setup M B)

end SignatureVolatility

module

public import SignatureVolatility.TheoremBOfSetupItoRiccatiKit
public import SignatureVolatility.SignatureRiccatiKit.CoordSemimartingale


@[expose] public section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem B, proved part** (no dependence on the open `affine_riccati_duality`): the
Theorem A price is a martingale on the signature filtration, NFLVR holds, and every signature
coordinate is a special semimartingale (Lemma 43). The full `theorem_B`, whose Riccati clause
rests on the open `affine_riccati_duality_mpr`, is in the non-submitted `OpenProblems` library
(`OpenProblems/TheoremB.lean`). -/
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

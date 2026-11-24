module

public import SignatureVolatility.TheoremBOfSetupItoRiccatiKit
public import SignatureVolatility.SignatureRiccatiKit.CoordSemimartingale
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMp


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper Theorem B, `→` part (proved)

Paper Theorem B: under H1–H3 the Theorem A price is a martingale on the signature filtration,
NFLVR holds, every signature coordinate is a special semimartingale, and (part (ii)) the
conditional transform of every finitely supported `u₀` with finite signature transform is
exponential-affine iff the Riccati equation `∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, has a global classical
solution.

`theorem_B_mp` proves everything except the `←` direction of (ii): the martingale, NFLVR and
special-semimartingale conclusions, and the `→` direction of the Riccati equivalence
(`affine_riccati_duality_mp`). The `←` direction is `theorem_B_mpr`, and the full statement
`theorem_B` (assembled from both), in `SignatureVolatility/TheoremBMpr.lean`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem B, `→` part (proved).** Martingale property on the signature filtration,
NFLVR, special-semimartingale signature coordinates (Lemma 43), and the `→` direction of the
Riccati transform equivalence (Theorem 4.2(ii)): an exponential-affine conditional transform
through a classical Riccati solution yields a global classical Riccati solution. -/
theorem theorem_B_mp (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
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
        (∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1
              ((paperSetup B M.hT).W_hat M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1
                ((paperSetup B M.hT).W_hat M.T ω)) |
              (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t))
                ((paperSetup B M.hT).W_hat t ω))) →
        Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) := by
  obtain ⟨sol, _⟩ := theorem_A_of_Brownian_Setup_Ito_Kit M (paperSetup B M.hT)
    (itoCalculusKit_of_mathfin B M.hT) h3
    (ae_continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1)
  exact ⟨sol, sol.is_martingale, nflvr_of_martingale_measure P,
    fun I => ⟨isSpecialSemimartingale_paperSig2_coeff B I M.hT⟩,
    fun u₀ hf h => affine_riccati_duality_mp M B u₀ hf h⟩

end SignatureVolatility

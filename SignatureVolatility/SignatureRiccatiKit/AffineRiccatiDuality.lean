module

public import SignatureVolatility.SignatureRiccatiKit.CoordSemimartingale
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMp
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMpr


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Affine / Riccati duality (paper Theorem 4.2(ii)) and the paper-strength kit

Assembles the paper's equivalence `affine_riccati_duality` from the proved `→` direction
(`affine_riccati_duality_mp`) and the open `←` direction (`affine_riccati_duality_mpr`), and
builds the paper-strength Riccati kit `signatureRiccatiKit_of_setup` from it.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Affine / Riccati duality** (paper Theorem 4.2(ii)), the paper's equivalence: `→` is
`affine_riccati_duality_mp` (proved), `←` is the open `affine_riccati_duality_mpr`. -/
theorem affine_riccati_duality (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)) :
    SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
    ((∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω))) P ∧
        P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) ((paperSetup B M.hT).W_hat t ω))) ↔
    Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) :=
  fun h => ⟨affine_riccati_duality_mp M B u₀ h, affine_riccati_duality_mpr M B u₀ h⟩

/-- **Paper goal.** Riccati kit over the paper-strength Brownian prolonged setup. -/
noncomputable def signatureRiccatiKit_of_setup (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    SignatureRiccatiKit Ω P M (paperSetup B M.hT) where
  coord_special_semimartingale := fun I => isSpecialSemimartingale_paperSig2_coeff B I M.hT
  R_op := riccatiOp
  affine_riccati_duality := affine_riccati_duality M B

end SignatureVolatility

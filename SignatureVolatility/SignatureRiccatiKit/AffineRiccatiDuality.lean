module

public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# The paper's affine / Riccati iff is false

Paper Theorem 4.2(ii) claimed, for every finitely supported `u₀` with finite signature
transform, that the exponential-affine conditional transform identity holds if and only if a
global classical Riccati solution exists. The `→` direction is true (`affine_riccati_duality_mp`).
The `←` direction is false as a universal statement: `not_affine_riccati_duality_mpr`. This file
records the corresponding negation of the iff.

The constructor `signatureRiccatiKit_of_setup`, which filled a `SignatureRiccatiKit` with this
iff for the paper operator `riccatiOp`, has been dropped: that kit field is an abstract
hypothesis, and the paper operator does not satisfy it.

No `sorry` is introduced here. The proof follows from `not_affine_riccati_duality_mpr`, which is
proved sorry-free in `AffineRiccatiDualityMprCounterexample` (see
`Writeup/narratives/affine_riccati_duality_mpr.md`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The paper's affine / Riccati iff (Theorem 4.2(ii)) is false as a statement over all
finitely supported `u₀` with finite signature transform. This follows from
`not_affine_riccati_duality_mpr` (the `←` direction already fails), with no added assumptions. -/
theorem not_affine_riccati_duality (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ¬ ∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
      SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
      ((∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1
                ((paperSetup B M.hT).W_hat M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1
                ((paperSetup B M.hT).W_hat M.T ω)) |
              (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (sol.ψ (M.T - t))
                ((paperSetup B M.hT).W_hat t ω))) ↔
        Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) := by
  intro h
  exact not_affine_riccati_duality_mpr M B fun u₀ hfin hne => (h u₀ hfin).mpr hne

end SignatureVolatility

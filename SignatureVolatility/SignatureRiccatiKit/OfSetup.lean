module

public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.SignatureRiccatiKit
public import SignatureVolatility.SignatureRiccatiKit.RiccatiOp


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper-strength `SignatureRiccatiKit` (Phase 3)

**Status: HOLE.** Kit inhabitant only. Paper Theorem B lives in `TheoremB`.

`R_op` is pinned to the paper's operator `riccatiOp` (Definition 18; agrees with
`riccatiOpBounded N` on `𝒟_fin`, see `riccatiOp_eq_bounded`). The kit field itself is
unconstrained, so a degenerate `R_op` with no classical solutions would make
`affine_riccati_duality` vacuous; we deliberately do not take that route.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper goal.** Riccati kit over the paper-strength Brownian prolonged setup. -/
noncomputable def signatureRiccatiKit_of_setup (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    SignatureRiccatiKit Ω P M (paperSetup B M.hT) where
  coord_special_semimartingale := sorry
  R_op := riccatiOp
  affine_riccati_duality := sorry

end SignatureVolatility

module

public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.SignatureRiccatiKit


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper-strength `SignatureRiccatiKit` (Phase 3)

**Status: HOLE.** Kit inhabitant only. Paper Theorem B lives in `TheoremB`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper goal.** Riccati kit over the paper-strength Brownian prolonged setup. -/
noncomputable def signatureRiccatiKit_of_setup (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    SignatureRiccatiKit Ω P M (paperSetup B M.hT) := by
  sorry

end SignatureVolatility

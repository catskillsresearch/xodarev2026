module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1


/-!
# B1. Positivity and the unit upper bound for `v₁`

`0 < v₁ x ≤ 1` for every real `x`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B1.** `0 < v₁ x ≤ 1` for all `x`. -/
lemma counterexampleV1_pos_le (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (x : ℝ) :
    0 < counterexampleV1AtHalf M B x ∧ counterexampleV1AtHalf M B x ≤ 1 := by
  sorry

end SignatureVolatility

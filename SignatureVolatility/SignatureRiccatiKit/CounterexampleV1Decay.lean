module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1


/-!
# B4. Decay of `v₁` to `0` as `x → +∞`

This is the clause that makes the Doléans exponential a strict local martingale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B4.** `Tendsto v₁ atTop (𝓝 0)`. -/
lemma counterexampleV1_tendsto_zero (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    Tendsto (counterexampleV1AtHalf M B) atTop (𝓝 0) := by
  sorry

end SignatureVolatility

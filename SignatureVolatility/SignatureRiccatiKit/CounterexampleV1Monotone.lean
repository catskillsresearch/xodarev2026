module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1


/-!
# B3. Monotonicity of `v₁` on `(-∞, 0]`
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B3.** Uniform positive lower bound on `(-∞, 0]`: `x ≤ 0 → v₁ 0 ≤ v₁ x`. -/
lemma counterexampleV1_monotone_nonpos (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∀ x : ℝ, x ≤ 0 →
      counterexampleV1AtHalf M B 0 ≤ counterexampleV1AtHalf M B x := by
  sorry

end SignatureVolatility

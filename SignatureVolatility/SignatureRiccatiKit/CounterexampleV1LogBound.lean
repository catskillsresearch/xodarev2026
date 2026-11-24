module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1


/-!
# B2. Quartic lower bound on `log v₁`
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B2.** Polynomial lower bound on `log v₁`:
`∃ C ≥ 0, ∀ x, -C (1 + |x|^4) ≤ log (v₁ x)`. -/
lemma counterexampleV1_log_bound (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      -C * (1 + |x| ^ 4) ≤ Real.log (counterexampleV1AtHalf M B x) := by
  sorry

end SignatureVolatility

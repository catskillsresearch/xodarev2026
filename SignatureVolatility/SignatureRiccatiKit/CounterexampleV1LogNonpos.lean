module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.CameronMartinC2Shift
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1PosLe

/-!
# B3. Logarithmic lower bound on `log v₁` for `x ≤ 0`, via deterministic Cameron–Martin
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B3.** For all `x ≤ 0`,
`log (v₁ x) ≥ -(s₀³/2) - 2 log(1 + s₀ |x|)` at `s₀ = T/2`.
Replaces the earlier (false-as-needed) comparison `v₁ 0 ≤ v₁ x`. -/
lemma counterexampleV1_log_nonpos (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∀ x : ℝ, x ≤ 0 →
      -((M.T / 2) ^ 3 / 2) - 2 * Real.log (1 + (M.T / 2) * |x|) ≤
        Real.log (counterexampleV1AtHalf M B x) := by
  sorry

end SignatureVolatility

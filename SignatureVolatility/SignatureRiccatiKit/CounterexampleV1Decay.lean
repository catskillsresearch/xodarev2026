module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1PosLe
public import SignatureVolatility.SignatureRiccatiKit.IntegralExpBarrier


/-!
# B4. Decay of `v₁` to `0` as `x → +∞`

This is the clause that makes the Doléans exponential a strict local martingale.
The bound `v₁ x ≤ exp(u(0,x))` from `integral_exp_shiftedExponent_le_exp_barrierU`,
together with `barrierU_initial_le`, gives an explicit exponential tail.
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
  set s₀ := M.T / 2
  have hs₀ : 0 < s₀ := half_pos M.hT
  rw [Metric.tendsto_atTop]
  intro ε hε
  set β : ℝ := max 1 ((8 / s₀ ^ 3) * Real.log (2 / ε))
  have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set A : ℝ := max 2 (max (2 * Real.sqrt (s₀ ^ 3)) (2 * Real.sqrt β * s₀ ^ 3))
  have hA2 : 2 ≤ A := le_max_left _ _
  have hAs : 2 * Real.sqrt (s₀ ^ 3) ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAβ : 2 * Real.sqrt β * s₀ ^ 3 ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 < A := by linarith
  refine ⟨2 * A / s₀, fun x hx => ?_⟩
  have hpos : 0 < counterexampleV1AtHalf M B x := (counterexampleV1_pos_le M B x).1
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  have h1 : counterexampleV1AtHalf M B x ≤ Real.exp (barrierU s₀ β A 0 x) := by
    simpa only [counterexampleV1AtHalf, counterexampleV1, s₀] using
      integral_exp_shiftedExponent_le_exp_barrierU B M.hd hs₀ hβ hA2 hAs hAβ hx
  have h2 := barrierU_initial_le hs₀ hβ hA hx
  have hβ_log : (8 / s₀ ^ 3) * Real.log (2 / ε) ≤ β := le_max_right _ _
  have hexp : Real.exp (-β * (s₀ ^ 3 / 8)) ≤ ε / 2 := by
    have hle : -β * (s₀ ^ 3 / 8) ≤ -Real.log (2 / ε) := by
      have := mul_le_mul_of_nonneg_right hβ_log (by positivity : 0 ≤ s₀ ^ 3 / 8)
      have hc : (8 / s₀ ^ 3) * Real.log (2 / ε) * (s₀ ^ 3 / 8) = Real.log (2 / ε) := by field_simp
      linarith
    calc Real.exp (-β * (s₀ ^ 3 / 8)) ≤ Real.exp (-Real.log (2 / ε)) := Real.exp_le_exp.mpr hle
      _ = (Real.exp (Real.log (2 / ε)))⁻¹ := Real.exp_neg _
      _ = (2 / ε)⁻¹ := by rw [Real.exp_log (by positivity)]
      _ = ε / 2 := by field_simp
  exact (h1.trans ((Real.exp_le_exp.mpr h2).trans hexp)).trans_lt (half_lt_self hε)

end SignatureVolatility

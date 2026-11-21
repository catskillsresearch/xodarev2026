/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.FiskStratonovich.Basic
public import StochLean.Probability.Process.Semimartingale.Ito.ContinuousCovariation

/-! # Protter II.34: the Fisk--Stratonovich change-of-variables formula

The C3 assumption makes the derivative transform a semimartingale in the
source integral's domain. The actual first-order jump correction is retained.
This does not claim the later Chapter V extension to C2 functions.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.ito_fiskStratonovich
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 3 f) :
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (fun t ω ↦ hX.fiskStratonovichIntegral (hX.contDiff_comp hF hf.deriv') hF t ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω)) P := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hd : ContDiff ℝ 2 (deriv f) := hf.deriv'
  filter_upwards [hX.ito_continuous_bracket hF hf₂,
    hX.continuousQuadraticCovariation_contDiff_comp_self hF hd] with ω hi hc t
  simp only [fiskStratonovichIntegral, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc t]
  exact hi t

theorem IsSemimartingale.ito_fiskStratonovich_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 3 f)
    (hc : HasContinuousPaths X P) :
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (hX.fiskStratonovichIntegral (hX.contDiff_comp hF hf.deriv') hF) P := by
  filter_upwards [hX.ito_fiskStratonovich hF hf, hc] with ω hi hx t
  have hz : (∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
      deriv f (leftLimitProcess X s ω) * jumpProcess X s ω)) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hx.leftLimitProcess_eq (ne_of_gt s.2.1),
          hx.jumpProcess_eq_zero (ne_of_gt s.2.1), sub_self, mul_zero, sub_self]
      _ = 0 := tsum_zero
  simpa only [hz, add_zero] using hi t

end ProbabilityTheory

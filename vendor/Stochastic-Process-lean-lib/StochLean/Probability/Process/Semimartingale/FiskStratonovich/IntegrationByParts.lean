/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.FiskStratonovich.Basic

/-! # Fisk--Stratonovich integration by parts, with the jump correction

The correction vanishes if either path is continuous, giving the corollary
to Protter II.34. It cannot be discarded for arbitrary cadlag inputs.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.fiskStratonovich_integrationByParts_with_jumps
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (fun t ω ↦ X t ω * Y t ω - X 0 ω * Y 0 ω)
      (fun t ω ↦ hX.fiskStratonovichIntegral hY hF t ω +
        hY.fiskStratonovichIntegral hX hF t ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P := by
  filter_upwards [hX.integrationByParts hY hF,
    hX.quadraticCovariation_continuous_jump_decomposition hY hF,
    hY.continuousQuadraticCovariation_comm hX hF] with ω hi hd hc t
  have h := hi t
  simp only [Pi.add_apply, Pi.mul_apply, (hd t).2] at h
  simp only [fiskStratonovichIntegral, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc t]
  linarith only [h]

theorem IsSemimartingale.fiskStratonovich_integrationByParts_of_continuous_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    Indistinguishable (fun t ω ↦ X t ω * Y t ω - X 0 ω * Y 0 ω)
      (hX.fiskStratonovichIntegral hY hF + hY.fiskStratonovichIntegral hX hF) P := by
  filter_upwards [hX.fiskStratonovich_integrationByParts_with_jumps hY hF, hc]
    with ω hi hx t
  have hz : (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hx.jumpProcess_eq_zero (ne_of_gt s.2.1), zero_mul]
      _ = 0 := tsum_zero
  simpa only [hz, add_zero, Pi.add_apply] using hi t

theorem IsSemimartingale.fiskStratonovich_integrationByParts_of_continuous_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths Y P) :
    Indistinguishable (fun t ω ↦ X t ω * Y t ω - X 0 ω * Y 0 ω)
      (hX.fiskStratonovichIntegral hY hF + hY.fiskStratonovichIntegral hX hF) P := by
  filter_upwards [hX.fiskStratonovich_integrationByParts_with_jumps hY hF, hc]
    with ω hi hy t
  have hz : (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hy.jumpProcess_eq_zero (ne_of_gt s.2.1), mul_zero]
      _ = 0 := tsum_zero
  simpa only [hz, add_zero, Pi.add_apply] using hi t

end ProbabilityTheory

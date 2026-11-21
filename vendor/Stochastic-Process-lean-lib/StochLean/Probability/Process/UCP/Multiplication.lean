/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.LeftContinuousDeviation
public import StochLean.Probability.Process.UCP.UniformConvergence
public import StochLean.Probability.Process.Path.CagladBounded
public import StochLean.Probability.Process.Path.Multiplication

/-! # UCP multiplication by a fixed caglad process

The multiplier need only be pathwise bounded on compact intervals, not bounded
uniformly in the sample point or integrable. Countable dense deviations provide
the needed measurability, including an independent initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y H : ℝ≥0 → Ω → ℝ}

theorem compactDeviation_mul_right_le {T : ℝ≥0} {ω : Ω} {C : ℝ}
    (hC : ∀ t ≤ T, ‖H t ω‖ ≤ C) :
    compactDeviation (X * H) (Y * H) T ω ≤
      compactDeviation X Y T ω * ENNReal.ofReal C := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  change ENNReal.ofReal ‖X t ω * H t ω - Y t ω * H t ω‖ ≤ _
  rw [← sub_mul, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul' (enorm_sub_le_compactDeviation ht ω) (ENNReal.ofReal_le_ofReal (hC t ht))

theorem tendsto_compactDeviation_mul_right {ι : Type*} {l : Filter ι}
    {Z : ι → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hu : Tendsto (fun n ↦ compactDeviation (Z n) Y T ω) l (𝓝 0))
    (hH : ∃ C : ℝ, ∀ t ≤ T, ‖H t ω‖ ≤ C) :
    Tendsto (fun n ↦ compactDeviation (Z n * H) (Y * H) T ω) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := hH
  have hb := ENNReal.Tendsto.mul_const hu (Or.inr (ENNReal.ofReal_ne_top :
    ENNReal.ofReal C ≠ ∞))
  rw [zero_mul] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ ↦ bot_le) (fun _ ↦ compactDeviation_mul_right_le hC)

theorem TendstoUCP.mul_right_of_caglad [IsFiniteMeasure P]
    {Z : ℕ → ℝ≥0 → Ω → ℝ} (hu : TendstoUCP P Z atTop Y)
    (hmZ : ∀ n t, Measurable (Z n t)) (hmY : ∀ t, Measurable (Y t))
    (hmH : ∀ t, Measurable (H t))
    (hrZ : ∀ n, HasCagladPaths (Z n) P) (hrY : HasCagladPaths Y P)
    (hrH : HasCagladPaths H P) :
    TendstoUCP P (fun n ↦ Z n * H) atTop (Y * H) := by
  apply tendstoUCP_of_subseq_ae_compactDeviation_of_aemeasurable
    (fun n T ↦ aemeasurable_compactDeviation_of_leftContinuous
      (fun t ↦ (hmZ n t).mul (hmH t)) (fun t ↦ (hmY t).mul (hmH t))
      ((hrZ n).mul hrH).hasLeftContinuousPaths (hrY.mul hrH).hasLeftContinuousPaths T)
  intro ns hns
  obtain ⟨k, _, hk⟩ := (hu.comp hns).exists_seq_ae_locallyUniform
  refine ⟨k, ?_⟩
  filter_upwards [hk, hrH] with ω hω hHω
  intro T
  apply tendsto_compactDeviation_mul_right (hω T)
  obtain ⟨C, _, hC⟩ := hHω.exists_norm_bound_Icc T
  exact ⟨C, fun t ht ↦ hC t ⟨bot_le, ht⟩⟩

theorem TendstoUCP.mul_left_of_caglad [IsFiniteMeasure P]
    {Z : ℕ → ℝ≥0 → Ω → ℝ} (hu : TendstoUCP P Z atTop Y)
    (hmZ : ∀ n t, Measurable (Z n t)) (hmY : ∀ t, Measurable (Y t))
    (hmH : ∀ t, Measurable (H t))
    (hrZ : ∀ n, HasCagladPaths (Z n) P) (hrY : HasCagladPaths Y P)
    (hrH : HasCagladPaths H P) :
    TendstoUCP P (fun n ↦ H * Z n) atTop (H * Y) := by
  simpa only [mul_comm] using hu.mul_right_of_caglad hmZ hmY hmH hrZ hrY hrH

end ProbabilityTheory

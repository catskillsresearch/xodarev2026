/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedIntegrability
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Process.Stopping.CadlagExitLocalization
public import StochLean.Probability.Process.ClassD.Basic

/-! # Capped norm exits give actual Class D stopped supermartingales

Before the capped exit the path's norm is at most the exit level. At and after
the exit, the stopped path equals the actual exit sample, including an exit at
time zero. The exit is bounded by a deterministic finite integer, so one-sided
bounded optional sampling proves that this actual sample is integrable.

The resulting common random envelope dominates every finite stopping sample
of the stopped process. Uniform integrability of that single integrable
envelope proves Class D. Neither Class D of the source nor a jump bound or zero
initial value is assumed. No terminal value at infinity is used: the existing
capped exit is everywhere finite by its deterministic cap.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace ProbabilityTheory

/-- The exit level and the actual exit sample bound every coordinate of the
stopped path. This order argument does not require path regularity. -/
theorem norm_stoppedProcess_cappedNormExitSequence_le_sample
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    ‖stoppedProcess X (cappedNormExitSequence X n) t ω‖ ≤ ((n + 1 : ℕ) : ℝ) +
      ‖stoppedValue X (cappedNormExitSequence X n) ω‖ := by
  by_cases ht : cappedNormExitSequence X n ω ≤ (t : WithTop ℝ≥0)
  · rw [stoppedProcess_eq_of_ge ht]
    change ‖stoppedValue X (cappedNormExitSequence X n) ω‖ ≤ _
    exact le_add_of_nonneg_left (by positivity)
  · have hlt : (t : WithTop ℝ≥0) < cappedNormExitSequence X n ω := lt_of_not_ge ht
    rw [stoppedProcess_eq_of_le hlt.le]
    exact (norm_le_of_lt_cappedNormExitSequence hlt).trans
      (le_add_of_nonneg_right (norm_nonneg _))

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Each actual capped norm-exit stopped supermartingale is Class D, even when
the original cadlag supermartingale is not assumed to be Class D. -/
theorem Supermartingale.isClassD_stoppedProcess_cappedNormExitSequence
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (n : ℕ) :
    IsClassD (stoppedProcess X (cappedNormExitSequence X n)) F P := by
  let τ := cappedNormExitSequence X n
  have hτ : IsStoppingTime F τ :=
    hX.stronglyAdapted.adapted.isStoppingTime_cappedNormExitSequence hF hc n
  have hi : Integrable (stoppedValue X τ) P :=
    hX.integrable_stoppedValue_of_bounded hτ (cappedNormExitSequence_le X n)
      hc.hasRightContinuousPaths
  let G : Ω → ℝ := fun ω ↦ ((n + 1 : ℕ) : ℝ) + ‖stoppedValue X τ ω‖
  have hiG : Integrable G P := (integrable_const (((n + 1 : ℕ) : ℝ))).add hi.norm
  have ha := hX.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hτ
  have hr := hc.hasRightContinuousPaths.stoppedProcess τ
  apply (isClassD_const (F := F) hiG).mono_norm
  · intro σ
    exact ((ha.measurable_stoppedValue_of_usual hF hr σ.isStoppingTime).mono
      σ.measurableSpace_le le_rfl).stronglyMeasurable.aestronglyMeasurable
  · intro σ
    filter_upwards with ω
    change ‖stoppedProcess X τ (σ ω) ω‖ ≤ ‖G ω‖
    have hG : 0 ≤ G ω := by dsimp only [G]; positivity
    rw [Real.norm_of_nonneg hG]
    exact norm_stoppedProcess_cappedNormExitSequence_le_sample X n (σ ω) ω

end MeasureTheory

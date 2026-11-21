/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IncrementBound
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Stopping
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Stopping

/-! # Stopping just one argument of the canonical covariation

The increment bound makes covariation constant whenever its first square
bracket is constant. Applied after a stopping time, this and the previously
proved simultaneous-stopping identity give both one-sided identities.
No false single-cell mixed-sum identity is used.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_stopped_left_eq_self_stopped
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable ((hX.stoppedProcess hF hτ).quadraticCovariation hY hF)
      (MeasureTheory.stoppedProcess
        ((hX.stoppedProcess hF hτ).quadraticCovariation hY hF) τ) P := by
  filter_upwards [(hX.stoppedProcess hF hτ).quadraticCovariation_eq_of_quadraticVariation_eq
    hY hF, hX.quadraticVariation_stoppedProcess hF hτ] with ω hflat hsq t
  cases htau : τ ω with
  | top =>
    simp only [MeasureTheory.stoppedProcess, htau, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe]
  | coe a =>
    have heq (u : ℝ≥0) :
        (hX.stoppedProcess hF hτ).quadraticVariation hF u ω =
          hX.quadraticVariation hF (min u a) ω := by
      simpa only [MeasureTheory.stoppedProcess, htau, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using hsq u
    simp only [MeasureTheory.stoppedProcess, htau, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe]
    apply hflat (min t a) t (min_le_left _ _)
    rw [heq t, heq (min t a), min_assoc, min_self]

theorem IsSemimartingale.quadraticCovariation_stoppedProcess_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable ((hX.stoppedProcess hF hτ).quadraticCovariation hY hF)
      (MeasureTheory.stoppedProcess (hX.quadraticCovariation hY hF) τ) P := by
  have hid : Indistinguishable
      (MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess X τ) τ)
      (MeasureTheory.stoppedProcess X τ) P := by
    simp only [MeasureTheory.stoppedProcess_stoppedProcess, inf_idem]
    exact ae_of_all _ fun _ _ ↦ rfl
  have heq := ((hX.stoppedProcess hF hτ).stoppedProcess hF hτ).quadraticCovariation_congr
    (hY.stoppedProcess hF hτ) (hX.stoppedProcess hF hτ) (hY.stoppedProcess hF hτ) hF hid
    (ae_of_all _ fun _ _ ↦ rfl)
  exact (hX.quadraticCovariation_stopped_left_eq_self_stopped hY hF hτ).trans
    (((hX.stoppedProcess hF hτ).quadraticCovariation_stoppedProcess_both hY hF hτ).symm.trans
      (heq.trans (hX.quadraticCovariation_stoppedProcess_both hY hF hτ)))

theorem IsSemimartingale.quadraticCovariation_stoppedProcess_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable (hX.quadraticCovariation (hY.stoppedProcess hF hτ) hF)
      (MeasureTheory.stoppedProcess (hX.quadraticCovariation hY hF) τ) P :=
  (hX.quadraticCovariation_comm (hY.stoppedProcess hF hτ) hF).trans
    ((hY.quadraticCovariation_stoppedProcess_left hX hF hτ).trans
      ((hY.quadraticCovariation_comm hX hF).stoppedProcess τ))

end ProbabilityTheory

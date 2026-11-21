/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra

/-! # Raw and continuous covariation with a continuous argument

One continuous argument kills every positive-time mixed jump. The initial
product is kept separate; no zero-starting convention is silently imposed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.continuousQuadraticCovariation_eq_of_left_continuous
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF)
      (fun t ω ↦ hX.quadraticCovariation hY hF t ω - X 0 ω * Y 0 ω) P := by
  filter_upwards [hX.quadraticCovariation_continuous_jump_decomposition hY hF, hc]
    with ω hd hcω t
  have hj : (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hcω.jumpProcess_eq_zero (ne_of_gt s.2.1), zero_mul]
      _ = 0 := tsum_zero
  have h := (hd t).2
  rw [hj, add_zero] at h
  linarith

end ProbabilityTheory

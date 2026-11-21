/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra

/-! # Raw quadratic variation controls every jump, including the initial jump

These bounds are on one event for all ordered times. They are used to control
cadlag stopping overshoots without asserting that a discontinuous path reaches
a norm-exit level exactly.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.sq_jump_le_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s T : ℝ≥0, s ≤ T →
      jumpProcess X s ω ^ 2 ≤ hX.quadraticVariation hF T ω := by
  filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF,
    hX.initial_sq_le_quadraticVariation hF] with ω hd h0 s T hst
  by_cases hs : s = 0
  · simpa only [hs, jumpProcess_zero] using h0 T
  · have hp : 0 < s := pos_iff_ne_zero.mpr hs
    have hle := (hd T).1.le_tsum (⟨s, hp, hst⟩ : Ioc 0 T) (fun _ _ ↦ sq_nonneg _)
    have hc := hX.continuousQuadraticVariation_nonneg hF T ω
    have hi := sq_nonneg (X 0 ω)
    have he := (hd T).2
    change jumpProcess X s ω ^ 2 ≤ ∑' r : Ioc 0 T, jumpProcess X r ω ^ 2 at hle
    linarith

theorem IsSemimartingale.norm_jump_le_sqrt_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s T : ℝ≥0, s ≤ T →
      ‖jumpProcess X s ω‖ ≤ Real.sqrt (hX.quadraticVariation hF T ω) := by
  filter_upwards [hX.sq_jump_le_quadraticVariation hF] with ω hω s T hst
  apply Real.le_sqrt_of_sq_le
  simpa only [Real.norm_eq_abs, sq_abs] using hω s T hst

end ProbabilityTheory

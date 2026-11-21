/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPart

/-! # Version invariance and continuous-path specialization of the continuous bracket -/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticVariation_congr
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hXY : Indistinguishable X Y P) :
    Indistinguishable (hX.continuousQuadraticVariation hF)
      (hY.continuousQuadraticVariation hF) P := by
  filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF,
    hY.quadraticVariation_continuous_jump_decomposition hF,
    hX.quadraticVariation_congr hY hF hXY, hXY, hXY.jumpProcess]
    with ω hx hy hq hxy hj t
  have hsum : (∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2) =
      ∑' s : Ioc 0 t, (jumpProcess Y s ω) ^ 2 := by
    apply tsum_congr
    intro s
    rw [hj s]
  have h := (hx t).2
  rw [hq t, hxy 0, hsum] at h
  linarith [(hy t).2]

theorem IsSemimartingale.continuousQuadraticVariation_eq_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    Indistinguishable (hX.continuousQuadraticVariation hF)
      (fun t ω ↦ hX.quadraticVariation hF t ω - (X 0 ω) ^ 2) P := by
  filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF, hc]
    with ω h hcω t
  have hsum : (∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hcω.jumpProcess_eq_zero (ne_of_gt s.2.1), zero_pow (by decide : 2 ≠ 0)]
      _ = 0 := tsum_zero
  have hd := (h t).2
  rw [hsum, add_zero] at hd
  linarith

theorem IsSemimartingale.continuousQuadraticVariation_nonneg
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (t : ℝ≥0) (ω : Ω) :
    0 ≤ hX.continuousQuadraticVariation hF t ω := by
  rw [← hX.continuousQuadraticVariation_zero hF ω]
  exact hX.monotone_continuousQuadraticVariation hF ω (show (0 : ℝ≥0) ≤ t from bot_le)

theorem IsSemimartingale.sq_jump_sum_le_quadraticVariation_sub_initial
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2) ≤ hX.quadraticVariation hF t ω - (X 0 ω) ^ 2 := by
  filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF] with ω h t
  linarith [(h t).2, hX.continuousQuadraticVariation_nonneg hF t ω]

end ProbabilityTheory

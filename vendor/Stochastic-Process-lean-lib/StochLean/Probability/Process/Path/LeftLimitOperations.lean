/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.Probability.Process.Path.Subtraction

/-! # Algebra of source left limits and jumps

Continuous scalar transformations must preserve zero to commute with the
source left limit at every time, including the special time-zero value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.leftLimitProcess_continuous_comp (hX : IsCadlagPath (X · ω))
    {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) (t : ℝ≥0) :
    leftLimitProcess (fun s v ↦ f (X s v)) t ω = f (leftLimitProcess X t ω) := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, h0]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto (hf.continuousAt.tendsto.comp (hX.tendsto_leftLimitProcess ht))

theorem IsCadlagPath.leftLimitProcess_sub (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    leftLimitProcess (X - Y) t ω = leftLimitProcess X t ω - leftLimitProcess Y t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, sub_self]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto
      ((hX.tendsto_leftLimitProcess ht).sub (hY.tendsto_leftLimitProcess ht))

theorem IsCadlagPath.jumpProcess_sub (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    jumpProcess (X - Y) t ω = jumpProcess X t ω - jumpProcess Y t ω := by
  simp only [jumpProcess, Pi.sub_apply, hX.leftLimitProcess_sub hY t]
  ring

theorem IsCadlagPath.jumpProcess_const_mul (hX : IsCadlagPath (X · ω))
    (c : ℝ) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ c * X s v) t ω = c * jumpProcess X t ω := by
  simp only [jumpProcess, Pi.sub_apply,
    hX.leftLimitProcess_continuous_comp (f := fun x ↦ c * x)
      (continuous_const.mul continuous_id) (mul_zero c) t]
  ring

theorem IsCadlagPath.jumpProcess_sq (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ (X s v) ^ 2) t ω =
      (X t ω) ^ 2 - (leftLimitProcess X t ω) ^ 2 := by
  simp only [jumpProcess, Pi.sub_apply,
    hX.leftLimitProcess_continuous_comp (f := fun x ↦ x ^ 2) (continuous_id.pow 2) (by norm_num) t]

end ProbabilityTheory

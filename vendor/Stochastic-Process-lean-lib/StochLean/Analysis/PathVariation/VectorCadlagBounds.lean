/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagBounded
public import StochLean.Probability.Process.Path.LeftLimit
public import Mathlib.Analysis.Normed.Group.Real

/-! # Compact range and pair bounds for proper normed cadlag paths

The closed ball contains both each path value and its actual strict-left
limit, including the bottom endpoint's canonical Mathlib convention.
-/

@[expose] public section

open Set Filter ProbabilityTheory Metric
open scoped NNReal Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

theorem range_leftLim_mem_closedBall_of_cadlag (hx : IsCadlagPath x)
    {T : ℝ≥0} {R : ℝ} (hR : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ R)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) :
    x t ∈ closedBall 0 R ∧ Function.leftLim x t ∈ closedBall 0 R := by
  have hm (u : ℝ≥0) (hu : u ∈ Icc 0 T) : x u ∈ closedBall 0 R := by
    simpa only [mem_closedBall, dist_zero_right] using hR u hu
  refine ⟨hm t ht, ?_⟩
  by_cases ht0 : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
    exact hm 0 ht
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht0⟩
    apply isClosed_closedBall.mem_of_tendsto (tendsto_leftLim_of_tendsto (hx.2 t ht0))
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hm u ⟨bot_le, (show u < t from hu).le.trans ht.2⟩

theorem exists_compact_vector_pair_bound_of_cadlag [ProperSpace E] (hx : IsCadlagPath x)
    (T : ℝ≥0) {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2)) :
    ∃ C : ℝ, (∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, ‖Φ (x a) (x b)‖ ≤ C) ∧
      (∀ t ∈ Icc 0 T, ‖Φ (Function.leftLim x t) (x t)‖ ≤ C) := by
  obtain ⟨R, _, hR⟩ := hx.exists_norm_bound_Icc T
  have hm {t : ℝ≥0} (ht : t ∈ Icc 0 T) := range_leftLim_mem_closedBall_of_cadlag hx hR ht
  have hK := (isCompact_closedBall (0 : E) R).prod (isCompact_closedBall (0 : E) R)
  obtain ⟨C, hC⟩ := (hK.image hΦ).isBounded.exists_norm_le
  refine ⟨C, ?_, ?_⟩
  · intro a ha b hb
    exact hC _ (mem_image_of_mem (fun p : E × E ↦ Φ p.1 p.2)
      (show (x a, x b) ∈ closedBall (0 : E) R ×ˢ closedBall (0 : E) R from
        ⟨(hm ha).1, (hm hb).1⟩))
  · intro t ht
    exact hC _ (mem_image_of_mem (fun p : E × E ↦ Φ p.1 p.2)
      (show (Function.leftLim x t, x t) ∈ closedBall (0 : E) R ×ˢ closedBall (0 : E) R from
        ⟨(hm ht).2, (hm ht).1⟩))

end StochLean

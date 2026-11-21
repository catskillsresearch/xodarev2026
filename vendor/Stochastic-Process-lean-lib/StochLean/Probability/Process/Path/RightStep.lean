/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag

/-! # Right-continuous step paths at finite and infinite lifetimes

A step at zero retains its new value at zero. An infinite lifetime has no
finite-time step. No terminal process value is introduced.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] [Zero E]

theorem isCadlagPath_step_Ici (a : ℝ≥0) (c : E) :
    IsCadlagPath (fun t : ℝ≥0 ↦ if a ≤ t then c else 0) := by
  constructor
  · intro t
    change Tendsto _ (𝓝[≥] t) (𝓝 (if a ≤ t then c else 0))
    by_cases ht : a ≤ t
    · rw [if_pos ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_pos (ht.trans (show t ≤ s from hs))).symm
    · rw [if_neg ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ht))] with s hs
      exact (if_neg (not_le_of_gt (show s < a from hs))).symm
  · intro t _
    by_cases ht : a < t
    · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
      exact (if_pos (show a ≤ s from (show a < s from hs).le)).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (not_le_of_gt ((show s < t from hs).trans_le (le_of_not_gt ht)))).symm

theorem isCadlagPath_indicator_lifetime_le {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (Z : Ω → E) (ω : Ω) :
    IsCadlagPath (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) := by
  classical
  cases ht : τ ω with
  | top =>
    have he : (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) =
        fun _ ↦ 0 := by
      funext t
      simp only [Set.indicator_apply, mem_ofPred_eq, ht, WithTop.not_top_le_coe, if_false]
    rw [he]
    exact IsContinuousPath.isCadlagPath continuous_const
  | coe a =>
    simpa only [Set.indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe] using
      isCadlagPath_step_Ici a (Z ω)

end ProbabilityTheory

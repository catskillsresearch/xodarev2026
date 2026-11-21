/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Algebra
public import Mathlib.Analysis.Normed.Group.Basic

/-! # Caglad initial spikes and left-open, right-closed step paths -/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem isCagladPath_step_Ioi (a : ℝ≥0) (c : ℝ) :
    IsCagladPath (fun t : ℝ≥0 ↦ if a < t then c else 0) := by
  constructor
  · intro t
    change Tendsto _ (𝓝[≤] t) (𝓝 (if a < t then c else 0))
    by_cases ha : a < t
    · rw [if_pos ha]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with s hs
      exact (if_pos (show a < s from hs)).symm
    · rw [if_neg ha]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (not_lt_of_ge ((show s ≤ t from hs).trans (le_of_not_gt ha)))).symm
  · intro t
    by_cases ha : a ≤ t
    · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_pos (ha.trans_lt (show t < s from hs))).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ha))] with s hs
      exact (if_neg (not_lt_of_ge (show s ≤ a from (show s < a from hs).le))).symm

theorem isCagladPath_initialSpike (c : ℝ) :
    IsCagladPath (fun t : ℝ≥0 ↦ if t = 0 then c else 0) := by
  have hconst : IsCagladPath (fun _ : ℝ≥0 ↦ c) :=
    IsContinuousPath.isCagladPath continuous_const
  have h := hconst.add ((isCagladPath_step_Ioi 0 c).continuous_comp continuous_neg)
  convert h using 1
  funext t
  by_cases ht : t = 0
  · simp [ht]
  · simp [ht, pos_iff_ne_zero.mpr ht]

theorem isCagladPath_step_Ioc {a b : ℝ≥0} (hab : a ≤ b) (c : ℝ) :
    IsCagladPath (fun t : ℝ≥0 ↦ if a < t ∧ t ≤ b then c else 0) := by
  have h := (isCagladPath_step_Ioi a c).add
    ((isCagladPath_step_Ioi b c).continuous_comp continuous_neg)
  convert h using 1
  funext t
  by_cases ha : a < t <;> by_cases hb : b < t
  · simp [ha, hb, not_le_of_gt hb]
  · simp [ha, hb, le_of_not_gt hb]
  · exact (ha (hab.trans_lt hb)).elim
  · simp [ha, hb]

theorem IsCagladPath.finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0 → ℝ)
    (hf : ∀ i ∈ s, IsCagladPath (f i)) : IsCagladPath (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (IsContinuousPath.isCagladPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

end ProbabilityTheory

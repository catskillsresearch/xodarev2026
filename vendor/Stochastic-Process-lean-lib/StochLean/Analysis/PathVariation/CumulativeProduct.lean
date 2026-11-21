/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Topology.Order.StepCutoffLimits
public import StochLean.Probability.Process.Path.Cadlag
public import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-! # One-sided regularity of locally absolutely convergent cumulative products

Closed positive-time products include the jump at the current time; their
strict-left limits are the products on the corresponding open interval.
Zero and negative factors are permitted. Dominated convergence is applied
to deviations from one, not to logarithms of possibly nonpositive factors.
-/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem tprod_Ioc_cutoff_le (f : ℝ≥0 → ℝ) (a t : ℝ≥0) :
    (∏' s : Ioc 0 t, (if (s : ℝ≥0) ≤ a then f s else 1)) =
      ∏' s : Ioc 0 (min t a), f s := by
  classical
  rw [tprod_subtype (Ioc 0 t) (fun s ↦ if s ≤ a then f s else 1),
    tprod_subtype (Ioc 0 (min t a)) f]
  apply tprod_congr
  intro s
  by_cases hs0 : 0 < s <;> by_cases hst : s ≤ t <;> by_cases hsa : s ≤ a <;>
    simp only [Set.mulIndicator, mem_Ioc, le_min_iff, hs0, hst, hsa,
      and_true, and_false, if_true, if_false]

theorem tprod_Ioc_cutoff_lt (f : ℝ≥0 → ℝ) {a t : ℝ≥0} (ha : a ≤ t) :
    (∏' s : Ioc 0 t, (if (s : ℝ≥0) < a then f s else 1)) = ∏' s : Ioo 0 a, f s := by
  classical
  rw [tprod_subtype (Ioc 0 t) (fun s ↦ if s < a then f s else 1), tprod_subtype (Ioo 0 a) f]
  apply tprod_congr
  intro s
  by_cases hs0 : 0 < s <;> by_cases hsa : s < a
  · simp only [Set.mulIndicator, mem_Ioc, mem_Ioo, hs0, hsa, (hsa.le.trans ha),
      and_self, if_true]
  all_goals simp [Set.mulIndicator, hs0, hsa]

theorem isRightContinuousPath_tprod_Ioc {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    IsRightContinuousPath (fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) := by
  intro t
  let T : ℝ≥0 := t + 1
  have htT : t < T := by dsimp only [T]; exact lt_add_one t
  have hlim := tendsto_tprod_one_add_of_dominated_convergence (hs T)
    (fun s : Ioc 0 T ↦ tendsto_stepCutoff_right (s : ℝ≥0) t (f s - 1))
    (Filter.Eventually.of_forall (fun (u : ℝ≥0) (s : Ioc 0 T) ↦ by
      split_ifs <;> simp [abs_nonneg]))
  have he (u : ℝ≥0) : (∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) ≤ u then f s - 1 else 0)) =
      ∏' s : Ioc 0 (min T u), f s := by
    convert tprod_Ioc_cutoff_le f u T using 1
    apply tprod_congr
    intro s
    split_ifs <;> ring
  simp only [he] at hlim
  rw [min_eq_right htT.le] at hlim
  apply hlim.congr'
  have hu : ∀ᶠ u in 𝓝[≥] t, u < T :=
    (eventually_lt_nhds htT).filter_mono nhdsWithin_le_nhds
  filter_upwards [hu] with u hu
  rw [min_eq_right hu.le]

theorem tendsto_tprod_Ioc_left {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 ↦ ∏' s : Ioc 0 u, f s) (𝓝[<] t)
      (𝓝 (∏' s : Ioo 0 t, f s)) := by
  let T : ℝ≥0 := t + 1
  have htT : t ≤ T := (lt_add_one t).le
  have hlim := tendsto_tprod_one_add_of_dominated_convergence (hs T)
    (fun s : Ioc 0 T ↦ tendsto_stepCutoff_left (s : ℝ≥0) t (f s - 1))
    (Filter.Eventually.of_forall (fun (u : ℝ≥0) (s : Ioc 0 T) ↦ by
      split_ifs <;> simp [abs_nonneg]))
  have he (u : ℝ≥0) : (∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) ≤ u then f s - 1 else 0)) =
      ∏' s : Ioc 0 (min T u), f s := by
    convert tprod_Ioc_cutoff_le f u T using 1
    apply tprod_congr
    intro s
    split_ifs <;> ring
  have heleft : (∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) < t then f s - 1 else 0)) =
      ∏' s : Ioo 0 t, f s := by
    convert tprod_Ioc_cutoff_lt f htT using 1
    apply tprod_congr
    intro s
    split_ifs <;> ring
  simp only [he, heleft] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [min_eq_right ((show u < t from hu).le.trans htT)]

theorem isCadlagPath_tprod_Ioc {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    IsCadlagPath (fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) :=
  ⟨isRightContinuousPath_tprod_Ioc hs, fun t _ ↦ ⟨_, tendsto_tprod_Ioc_left hs t⟩⟩

end StochLean

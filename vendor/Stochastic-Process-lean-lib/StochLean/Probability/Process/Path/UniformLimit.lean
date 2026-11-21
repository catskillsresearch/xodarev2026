/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag
public import StochLean.ForMathlib.Topology.UniformLimit
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Locally uniform limits of cadlag paths

The finite left limit is constructed using completeness of the state space.
No convergence of the left limits is postulated, and time zero needs no left limit.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [MetricSpace E] {x : ℕ → ℝ≥0 → E} {y : ℝ≥0 → E}

theorem isRightContinuousPath_of_locallyUniform
    (hx : ∀ n, IsRightContinuousPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T)) : IsRightContinuousPath y := by
  intro t
  have hq : 𝓝[≥] t ≤ 𝓟 (Icc 0 (t + 1)) := by
    apply le_principal_iff.mpr
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one t))] with u hu
    exact ⟨bot_le, hu.le⟩
  exact ((hu (t + 1)).tendstoUniformlyOnFilter.mono_right hq).tendsto_of_eventually_tendsto
    (Eventually.of_forall fun n ↦ hx n t) ((hu (t + 1)).tendsto_at ⟨bot_le, le_add_right le_rfl⟩)

theorem isCadlagPath_of_locallyUniform [CompleteSpace E]
    (hx : ∀ n, IsCadlagPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T)) : IsCadlagPath y := by
  refine ⟨isRightContinuousPath_of_locallyUniform (fun n ↦ (hx n).1) hu, ?_⟩
  intro t ht
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
  have hq : 𝓝[<] t ≤ 𝓟 (Icc 0 t) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact ⟨bot_le, hu.le⟩
  exact (hu t).exists_tendsto_of_exists_tendsto hq (fun n ↦ (hx n).2 t ht)

end ProbabilityTheory

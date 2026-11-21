/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CagladBounded
public import StochLean.Probability.Process.Path.Cadlag

/-! # Local and compact bounds for cadlag paths

The lower endpoint is treated by right continuity alone. At positive times,
the actual finite left limit and right continuity give a neighborhood bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

theorem IsCadlagPath.exists_local_norm_bound (hx : IsCadlagPath x) (t : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in 𝓝 t, ‖x s‖ ≤ C := by
  have hr : ∀ᶠ s in 𝓝[≥] t, ‖x s‖ < ‖x t‖ + 1 :=
    (hx.1 t).norm.tendsto.eventually (Iio_mem_nhds (lt_add_one _))
  by_cases ht : t = 0
  · subst t
    refine ⟨‖x 0‖ + 1, by positivity, ?_⟩
    simpa only [show Ici (0 : ℝ≥0) = univ from Ici_bot, nhdsWithin_univ] using
      hr.mono (fun _ hs ↦ hs.le)
  · obtain ⟨y, hy⟩ := hx.2 t ht
    have hl : ∀ᶠ s in 𝓝[<] t, ‖x s‖ < ‖y‖ + 1 :=
      hy.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨max (‖y‖ + 1) (‖x t‖ + 1), by positivity, ?_⟩
    rw [← nhdsLT_sup_nhdsGE t, Filter.eventually_sup]
    exact ⟨hl.mono (fun _ hs ↦ hs.le.trans (le_max_left _ _)),
      hr.mono (fun _ hs ↦ hs.le.trans (le_max_right _ _))⟩

theorem IsCadlagPath.exists_norm_bound_on_compact (hx : IsCadlagPath x)
    {K : Set ℝ≥0} (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ‖x t‖ ≤ C := by
  classical
  choose C hCpos hC using hx.exists_local_norm_bound
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover (fun t ↦ {u | ‖x u‖ ≤ C t}) (fun t _ ↦ hC t)
  refine ⟨∑ t ∈ s, C t, Finset.sum_nonneg (fun t _ ↦ hCpos t), ?_⟩
  intro t ht
  obtain ⟨u, hu, hut⟩ := mem_iUnion₂.mp (hs ht)
  exact hut.trans (Finset.single_le_sum (fun v _ ↦ hCpos v) hu)

theorem IsCadlagPath.exists_norm_bound_Icc (hx : IsCadlagPath x) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖x t‖ ≤ C :=
  hx.exists_norm_bound_on_compact isCompact_Icc

end ProbabilityTheory

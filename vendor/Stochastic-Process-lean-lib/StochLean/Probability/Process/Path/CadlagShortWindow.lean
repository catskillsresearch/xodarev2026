/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagFiniteOscillation

/-! # Short cadlag windows controlled by the largest positive-time jump

On a compact horizon, a cadlag path whose positive-time jumps have size at most
`b` has short-window oscillations at most `b + ε`. One-sided limits give local
control, including across a jump; the metric Lebesgue number lemma makes the
window width uniform. The initial value is unrestricted: there is no left
window at time zero and no bound on the source's initial jump is required.
-/

@[expose] public section

open Set Filter Metric
open scoped NNReal Topology

namespace ProbabilityTheory

theorem IsCadlagPath.exists_oscillation_neighborhood_of_jump_bound
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (t : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : 0 < t → dist (x t) (Function.leftLim x t) ≤ b) :
    ∃ U : Set ℝ≥0, U ∈ 𝓝 t ∧ ∀ r ∈ U, ∀ s ∈ U, r ≤ s →
      dist (x r) (x s) < b + ε := by
  let U : Set ℝ≥0 := {s | if s < t then dist (x s) (Function.leftLim x t) < ε / 2
    else dist (x s) (x t) < ε / 2}
  have hU : U ∈ 𝓝 t := by
    rw [← nhdsLT_sup_nhdsGE t, Filter.mem_sup]
    constructor
    · by_cases ht : t = 0
      · subst t
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact ((not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ s)) hs).elim
      · have hl := (tendsto_leftLim_of_tendsto (hx.2 t ht)).eventually
          (Metric.ball_mem_nhds _ (half_pos hε))
        filter_upwards [hl, self_mem_nhdsWithin] with s hs hst
        simpa only [U, mem_ofPred_eq, if_pos (show s < t from hst), mem_ball] using hs
    · have hr := (hx.1 t).tendsto.eventually (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [hr, self_mem_nhdsWithin] with s hs hst
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge (show t ≤ s from hst)), mem_ball]
        using hs
  refine ⟨U, hU, fun r hr s hs hrs ↦ ?_⟩
  by_cases hrt : r < t
  · have hr' : dist (x r) (Function.leftLim x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_pos hrt] using hr
    by_cases hst : s < t
    · have hs' : dist (x s) (Function.leftLim x t) < ε / 2 := by
        simpa only [U, mem_ofPred_eq, if_pos hst] using hs
      have h := dist_triangle_right (x r) (x s) (Function.leftLim x t)
      linarith only [h, hr', hs', hb]
    · have hs' : dist (x s) (x t) < ε / 2 := by
        simpa only [U, mem_ofPred_eq, if_neg hst] using hs
      have hj' := hj (lt_of_le_of_lt (bot_le : (0 : ℝ≥0) ≤ r) hrt)
      have h₁ := dist_triangle (x r) (Function.leftLim x t) (x s)
      have h₂ := dist_triangle (Function.leftLim x t) (x t) (x s)
      rw [dist_comm (Function.leftLim x t) (x t), dist_comm (x t) (x s)] at h₂
      linarith only [h₁, h₂, hr', hs', hj']
  · have hst : ¬ s < t := not_lt_of_ge ((le_of_not_gt hrt).trans hrs)
    have hr' : dist (x r) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg hrt] using hr
    have hs' : dist (x s) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg hst] using hs
    have h := dist_triangle_right (x r) (x s) (x t)
    linarith only [h, hr', hs', hb]

theorem IsCadlagPath.exists_uniform_dist_lt_on_Icc_of_jump_bound
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (a T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t ∈ Icc a T, 0 < t → dist (x t) (Function.leftLim x t) ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc a T, ∀ s ∈ Icc a T,
      dist r s < δ → dist (x r) (x s) < b + ε := by
  classical
  choose U hU hosc using fun t : Icc a T ↦
    hx.exists_oscillation_neighborhood_of_jump_bound t hb hε (hj t t.2)
  have hcov : Icc a T ⊆ ⋃ t : Icc a T, interior (U t) := by
    intro r hr
    apply mem_iUnion.mpr
    exact ⟨⟨r, hr⟩, mem_of_mem_nhds (interior_mem_nhds.mpr (hU ⟨r, hr⟩))⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ : Icc a T ↦ isOpen_interior) hcov
  refine ⟨δ, hδ, fun r hr s _ hdist ↦ ?_⟩
  obtain ⟨t, ht⟩ := hball r hr
  have hru : r ∈ U t := interior_subset (ht (mem_ball_self hδ))
  have hsu : s ∈ U t := interior_subset (ht (by simpa only [mem_ball, dist_comm] using hdist))
  rcases le_total r s with hrs | hsr
  · exact hosc t r hru s hsu hrs
  · simpa only [dist_comm (x s) (x r)] using hosc t s hsu r hru hsr

theorem IsCadlagPath.exists_short_window_dist_lt_on_Icc_of_jump_bound
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (a T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t ∈ Icc a T, 0 < t → dist (x t) (Function.leftLim x t) ≤ b) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ r s : ℝ≥0, a ≤ r → r ≤ s → s ≤ T → s ≤ r + δ →
      dist (x r) (x s) < b + ε := by
  obtain ⟨d, hd, hmod⟩ := hx.exists_uniform_dist_lt_on_Icc_of_jump_bound a T hb hε hj
  let δ : ℝ≥0 := ⟨d / 2, (half_pos hd).le⟩
  refine ⟨δ, by exact_mod_cast half_pos hd, fun r s har hrs hsT hsd ↦ ?_⟩
  apply hmod r ⟨har, hrs.trans hsT⟩ s ⟨har.trans hrs, hsT⟩
  rw [dist_comm r s, NNReal.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hrs))]
  have hsd' : (s : ℝ) ≤ (r : ℝ) + d / 2 := by exact_mod_cast hsd
  linarith only [hsd', hd]

theorem IsCadlagPath.exists_short_window_dist_lt_of_jump_bound
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t, 0 < t → t ≤ T → dist (x t) (Function.leftLim x t) ≤ b) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ r s : ℝ≥0, r ≤ s → s ≤ T → s ≤ r + δ →
      dist (x r) (x s) < b + ε := by
  classical
  choose U hU hosc using fun t : Icc (0 : ℝ≥0) T ↦
    hx.exists_oscillation_neighborhood_of_jump_bound t hb hε (fun ht ↦ hj t ht t.2.2)
  have hcov : Icc 0 T ⊆ ⋃ t : Icc (0 : ℝ≥0) T, interior (U t) := by
    intro r hr
    apply mem_iUnion.mpr
    exact ⟨⟨r, hr⟩, mem_of_mem_nhds (interior_mem_nhds.mpr (hU ⟨r, hr⟩))⟩
  obtain ⟨d, hd, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ : Icc (0 : ℝ≥0) T ↦ isOpen_interior) hcov
  let δ : ℝ≥0 := ⟨d / 2, (half_pos hd).le⟩
  refine ⟨δ, by exact_mod_cast half_pos hd, fun r s hrs hsT hsd ↦ ?_⟩
  have hrT : r ∈ Icc 0 T := ⟨bot_le, hrs.trans hsT⟩
  obtain ⟨t, ht⟩ := hball r hrT
  have hru : r ∈ U t := interior_subset (ht (mem_ball_self hd))
  have hdist : dist s r < d := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hrs))]
    have hsd' : (s : ℝ) ≤ (r : ℝ) + d / 2 := by exact_mod_cast hsd
    linarith only [hsd', hd]
  have hsu : s ∈ U t := interior_subset (ht hdist)
  exact hosc t r hru s hsu hrs

theorem IsCadlagPath.eventually_short_window_dist_le_of_jump_bound
    {E ι : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t, 0 < t → t ≤ T → dist (x t) (Function.leftLim x t) ≤ b)
    {l : Filter ι} {δ : ι → ℝ≥0} (hδ : Tendsto δ l (𝓝 0)) :
    ∀ᶠ i in l, ∀ r s : ℝ≥0, r ≤ s → s ≤ T → s ≤ r + δ i →
      dist (x r) (x s) ≤ b + ε := by
  obtain ⟨d, hd, hmod⟩ := hx.exists_short_window_dist_lt_of_jump_bound T hb hε hj
  filter_upwards [hδ.eventually_le_const hd] with i hi r s hrs hsT hsd
  apply (hmod r s hrs hsT ?_).le
  have hsum : r + δ i ≤ r + d := by gcongr
  exact hsd.trans hsum

theorem IsCadlagPath.exists_short_window_norm_le_of_jumpProcess_bound
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hx : IsCadlagPath (X · ω)) (T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t, 0 < t → t ≤ T → ‖jumpProcess X t ω‖ ≤ b) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ r s : ℝ≥0, r ≤ s → s ≤ T → s ≤ r + δ →
      ‖X s ω - X r ω‖ ≤ b + ε := by
  have hj' : ∀ t, 0 < t → t ≤ T →
      dist (X t ω) (Function.leftLim (X · ω) t) ≤ b := by
    intro t ht htT
    simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg (ne_of_gt ht), dist_eq_norm]
      using hj t ht htT
  obtain ⟨δ, hδ, hmod⟩ := hx.exists_short_window_dist_lt_of_jump_bound T hb hε hj'
  refine ⟨δ, hδ, fun r s hrs hsT hsd ↦ ?_⟩
  have h := (hmod r s hrs hsT hsd).le
  simpa only [dist_comm (X r ω) (X s ω), dist_eq_norm] using h

end ProbabilityTheory

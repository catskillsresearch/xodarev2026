/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Order.Basic

/-! # Joint continuity of the real differentiated slope

The existing Mathlib `dslope` fills in the diagonal by the actual derivative.
The real mean value theorem controls this diagonal as both endpoints vary.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem dslope_comm_real (f : ℝ → ℝ) (a b : ℝ) : dslope f a b = dslope f b a := by
  by_cases h : b = a
  · subst b
    rfl
  · rw [dslope_of_ne _ h, dslope_of_ne _ (Ne.symm h), slope_comm]

theorem exists_deriv_eq_dslope {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ∃ c ∈ uIcc a b, deriv f c = dslope f a b := by
  rcases lt_trichotomy a b with h | h | h
  · obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope' f h hf.continuous.continuousOn
      hf.differentiable_one.differentiableOn
    refine ⟨c, ?_, ?_⟩
    · simpa only [uIcc_of_le h.le] using ⟨hc.1.le, hc.2.le⟩
    · rwa [dslope_of_ne _ (ne_of_gt h)]
  · subst b
    exact ⟨a, left_mem_uIcc, (dslope_same f a).symm⟩
  · obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope' f h hf.continuous.continuousOn
      hf.differentiable_one.differentiableOn
    refine ⟨c, ?_, ?_⟩
    · simpa only [uIcc_of_ge h.le] using ⟨hc.1.le, hc.2.le⟩
    · rwa [dslope_comm_real, dslope_of_ne _ (ne_of_gt h)]

theorem norm_dslope_le_of_deriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b C : ℝ} (hC : ∀ c ∈ uIcc a b, ‖deriv f c‖ ≤ C) :
    ‖dslope f a b‖ ≤ C := by
  obtain ⟨c, hc, he⟩ := exists_deriv_eq_dslope hf a b
  rw [← he]
  exact hC c hc

theorem tendsto_dslope_of_contDiff {α : Type*} {l : Filter α} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {a b : α → ℝ} {x y : ℝ}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 y)) :
    Tendsto (fun i ↦ dslope f (a i) (b i)) l (𝓝 (dslope f x y)) := by
  by_cases h : y = x
  · subst y
    choose c hc he using fun i ↦ exists_deriv_eq_dslope hf (a i) (b i)
    have hmin : Tendsto (fun i ↦ min (a i) (b i)) l (𝓝 x) := by
      simpa only [min_self] using ha.min hb
    have hmax : Tendsto (fun i ↦ max (a i) (b i)) l (𝓝 x) := by
      simpa only [max_self] using ha.max hb
    have hlim : Tendsto c l (𝓝 x) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hmin hmax
        (fun i ↦ (hc i).1) (fun i ↦ (hc i).2)
    rw [dslope_same]
    exact ((hf.continuous_deriv_one.tendsto x).comp hlim).congr he
  · have hn : ∀ᶠ i in l, b i - a i ≠ 0 := (hb.sub ha).eventually_ne (sub_ne_zero.mpr h)
    rw [dslope_of_ne _ h, slope_def_field]
    apply (((hf.continuous.tendsto y).comp hb).sub
      ((hf.continuous.tendsto x).comp ha)).div (hb.sub ha) (sub_ne_zero.mpr h) |>.congr'
    filter_upwards [hn] with i hi
    rw [dslope_of_ne _ (sub_ne_zero.mp hi), slope_def_field]
    rfl

theorem continuous_dslope_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ ↦ dslope f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_dslope_of_contDiff hf continuous_fst.continuousAt continuous_snd.continuousAt

end StochLean

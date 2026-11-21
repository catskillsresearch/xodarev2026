/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.DSlopeContinuous
public import Mathlib.Analysis.Calculus.Taylor

/-! # The continuous quadratic Taylor quotient of a real C2 function

The diagonal is filled with one half of the second derivative, not the
totalized quotient's zero value. This is the coefficient of squared increments
in the exact finite-cell Taylor identity used for Ito's formula.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem exists_second_deriv_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃ c ∈ uIcc a b, f b - f a - deriv f a * (b - a) =
      (deriv (deriv f) c / 2) * (b - a) ^ 2 := by
  by_cases h : a = b
  · subst b
    exact ⟨a, left_mem_uIcc, by simp⟩
  · obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) h hf.contDiffOn
    have hd : iteratedDerivWithin 1 f (uIcc a b) a = deriv f a := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h)
        ((hf.of_le (by decide)).contDiffAt) left_mem_uIcc, iteratedDeriv_one]
    have ht : taylorWithinEval f 1 (uIcc a b) a b = f a + (b - a) * deriv f a := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval]
      norm_num [hd, smul_eq_mul]
    rw [ht] at he
    norm_num [iteratedDeriv_succ, iteratedDeriv_one] at he
    refine ⟨c, ⟨hc.1.le, hc.2.le⟩, ?_⟩
    nlinarith only [he]

noncomputable def quadraticTaylorSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a = b then deriv (deriv f) a / 2 else
    (f b - f a - deriv f a * (b - a)) / (b - a) ^ 2

@[simp] theorem quadraticTaylorSlope_self (f : ℝ → ℝ) (a : ℝ) :
    quadraticTaylorSlope f a a = deriv (deriv f) a / 2 := by
  simp only [quadraticTaylorSlope, ↓reduceIte]

theorem quadraticTaylorSlope_mul_sq (f : ℝ → ℝ) (a b : ℝ) :
    quadraticTaylorSlope f a b * (b - a) ^ 2 = f b - f a - deriv f a * (b - a) := by
  by_cases h : a = b
  · subst b
    simp
  · rw [quadraticTaylorSlope, if_neg h,
      div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h)))]

theorem exists_second_deriv_eq_quadraticTaylorSlope {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃ c ∈ uIcc a b, deriv (deriv f) c / 2 = quadraticTaylorSlope f a b := by
  by_cases h : a = b
  · subst b
    exact ⟨a, left_mem_uIcc, (quadraticTaylorSlope_self f a).symm⟩
  · obtain ⟨c, hc, he⟩ := exists_second_deriv_remainder hf a b
    refine ⟨c, hc, ?_⟩
    rw [quadraticTaylorSlope, if_neg h]
    exact (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h)))).mpr he.symm

theorem tendsto_quadraticTaylorSlope_of_contDiff {α : Type*} {l : Filter α}
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : α → ℝ} {x y : ℝ}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 y)) :
    Tendsto (fun i ↦ quadraticTaylorSlope f (a i) (b i)) l
      (𝓝 (quadraticTaylorSlope f x y)) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  by_cases h : y = x
  · subst y
    choose c hc he using fun i ↦ exists_second_deriv_eq_quadraticTaylorSlope hf (a i) (b i)
    have hmin : Tendsto (fun i ↦ min (a i) (b i)) l (𝓝 x) := by
      simpa only [min_self] using ha.min hb
    have hmax : Tendsto (fun i ↦ max (a i) (b i)) l (𝓝 x) := by
      simpa only [max_self] using ha.max hb
    have hlim : Tendsto c l (𝓝 x) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hmin hmax
        (fun i ↦ (hc i).1) (fun i ↦ (hc i).2)
    rw [quadraticTaylorSlope_self]
    exact (((hd.continuous_deriv_one.tendsto x).comp hlim).div_const 2).congr he
  · have hn : ∀ᶠ i in l, b i - a i ≠ 0 := (hb.sub ha).eventually_ne (sub_ne_zero.mpr h)
    rw [quadraticTaylorSlope, if_neg (Ne.symm h)]
    have hlim := ((((hf.continuous.tendsto y).comp hb).sub
      ((hf.continuous.tendsto x).comp ha)).sub
      (((hf.continuous_deriv (by decide)).tendsto x).comp ha |>.mul (hb.sub ha))).div
      ((hb.sub ha).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr h))
    apply hlim.congr'
    filter_upwards [hn] with i hi
    rw [quadraticTaylorSlope, if_neg (Ne.symm (sub_ne_zero.mp hi))]
    rfl

theorem continuous_quadraticTaylorSlope_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun p : ℝ × ℝ ↦ quadraticTaylorSlope f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_quadraticTaylorSlope_of_contDiff hf
    continuous_fst.continuousAt continuous_snd.continuousAt

theorem norm_quadraticTaylorSlope_le_of_second_deriv_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b C : ℝ}
    (hC : ∀ c ∈ uIcc a b, ‖deriv (deriv f) c‖ ≤ C) :
    ‖quadraticTaylorSlope f a b‖ ≤ C / 2 := by
  obtain ⟨c, hc, he⟩ := exists_second_deriv_eq_quadraticTaylorSlope hf a b
  rw [← he, norm_div, show ‖(2 : ℝ)‖ = 2 from by norm_num]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr (hC c hc)

theorem norm_quadraticTaylorSlope_sub_halfSecondDeriv_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b C : ℝ}
    (hC : ∀ c ∈ uIcc a b, ‖deriv (deriv f) c - deriv (deriv f) a‖ ≤ C) :
    ‖quadraticTaylorSlope f a b - deriv (deriv f) a / 2‖ ≤ C / 2 := by
  obtain ⟨c, hc, he⟩ := exists_second_deriv_eq_quadraticTaylorSlope hf a b
  rw [← he, ← sub_div, norm_div, show ‖(2 : ℝ)‖ = 2 from by norm_num]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr (hC c hc)

end StochLean

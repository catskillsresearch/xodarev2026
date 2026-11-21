/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.FrechetTaylorLine

/-! # A continuous diagonal-zero coefficient for the Frechet Taylor error

Dividing the actual second-order error by the squared increment norm gives
a coefficient continuous even on the diagonal. This makes the jump-separation
argument applicable to vector paths without a discontinuous directional choice.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

noncomputable def frechetSecondOrderRemainder (f : E → ℝ) (a b : E) : ℝ :=
  f b - f a - fderiv ℝ f a (b - a) -
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (b - a) (b - a)

noncomputable def frechetTaylorErrorCoefficient (f : E → ℝ) (a b : E) : ℝ :=
  frechetSecondOrderRemainder f a b / ‖b - a‖ ^ 2

@[simp] theorem frechetSecondOrderRemainder_self (f : E → ℝ) (a : E) :
    frechetSecondOrderRemainder f a a = 0 := by simp [frechetSecondOrderRemainder]

@[simp] theorem frechetTaylorErrorCoefficient_self (f : E → ℝ) (a : E) :
    frechetTaylorErrorCoefficient f a a = 0 := by simp [frechetTaylorErrorCoefficient]

theorem frechetTaylorErrorCoefficient_mul_norm_sq (f : E → ℝ) (a b : E) :
    frechetTaylorErrorCoefficient f a b * ‖b - a‖ ^ 2 = frechetSecondOrderRemainder f a b := by
  by_cases h : b = a
  · subst b
    simp
  · exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))

theorem exists_norm_frechetTaylorErrorCoefficient_le (hf : ContDiff ℝ 2 f) (a b : E) :
    ∃ θ ∈ Icc (0 : ℝ) 1, ‖frechetTaylorErrorCoefficient f a b‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) - fderiv ℝ (fderiv ℝ f) a‖ / 2 := by
  obtain ⟨θ, hθ, he⟩ := exists_frechet_second_deriv_remainder hf a b
  refine ⟨θ, hθ, ?_⟩
  let L := fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) - fderiv ℝ (fderiv ℝ f) a
  have hR : frechetSecondOrderRemainder f a b = (1 / 2 : ℝ) * L (b - a) (b - a) := by
    rw [frechetSecondOrderRemainder, he, ← mul_sub]
    rfl
  have hL : ‖L (b - a) (b - a)‖ ≤ ‖L‖ * ‖b - a‖ ^ 2 := by
    calc
      _ ≤ ‖L (b - a)‖ * ‖b - a‖ := (L (b - a)).le_opNorm _
      _ ≤ (‖L‖ * ‖b - a‖) * ‖b - a‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  by_cases h : b = a
  · subst b
    simp only [frechetTaylorErrorCoefficient_self, norm_zero]
    positivity
  · have hn : 0 < ‖b - a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h))
    rw [frechetTaylorErrorCoefficient, norm_div, norm_pow, norm_norm, hR, norm_mul,
      show ‖(1 / 2 : ℝ)‖ = 1 / 2 from by norm_num]
    apply (div_le_iff₀ hn).mpr
    change (1 / 2 : ℝ) * ‖L (b - a) (b - a)‖ ≤ ‖L‖ / 2 * ‖b - a‖ ^ 2
    nlinarith only [hL]

theorem tendsto_frechetTaylorErrorCoefficient_of_contDiff {α : Type*} {l : Filter α}
    (hf : ContDiff ℝ 2 f) {a b : α → E} {x y : E}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 y)) :
    Tendsto (fun i ↦ frechetTaylorErrorCoefficient f (a i) (b i)) l
      (𝓝 (frechetTaylorErrorCoefficient f x y)) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hH := hd.continuous_fderiv (by decide)
  by_cases h : y = x
  · subst y
    rw [frechetTaylorErrorCoefficient_self]
    choose θ hθ hbound using fun i ↦ exists_norm_frechetTaylorErrorCoefficient_le hf (a i) (b i)
    have hn : Tendsto (fun i ↦ ‖b i - a i‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hb.sub ha).norm
    have hv : Tendsto (fun i ↦ θ i • (b i - a i)) l (𝓝 0) := by
      apply squeeze_zero_norm (fun i ↦ ?_) hn
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθ i).2
    have hc : Tendsto (fun i ↦ a i + θ i • (b i - a i)) l (𝓝 x) := by
      simpa only [add_zero] using ha.add hv
    have hbnd : Tendsto (fun i ↦
        ‖fderiv ℝ (fderiv ℝ f) (a i + θ i • (b i - a i)) -
          fderiv ℝ (fderiv ℝ f) (a i)‖ / 2) l (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_div, Function.comp_apply] using
        ((((hH.tendsto x).comp hc).sub ((hH.tendsto x).comp ha)).norm.div_const 2)
    exact squeeze_zero_norm hbound hbnd
  · have hR : Tendsto (fun i ↦ frechetSecondOrderRemainder f (a i) (b i)) l
        (𝓝 (frechetSecondOrderRemainder f x y)) := by
      have hc : Continuous (fun p : E × E ↦ frechetSecondOrderRemainder f p.1 p.2) := by
        unfold frechetSecondOrderRemainder
        fun_prop
      exact (hc.tendsto (x, y)).comp (ha.prodMk_nhds hb)
    exact hR.div ((hb.sub ha).norm.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))

theorem continuous_frechetTaylorErrorCoefficient_of_contDiff (hf : ContDiff ℝ 2 f) :
    Continuous (fun p : E × E ↦ frechetTaylorErrorCoefficient f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_frechetTaylorErrorCoefficient_of_contDiff hf
    continuous_fst.continuousAt continuous_snd.continuousAt

end StochLean

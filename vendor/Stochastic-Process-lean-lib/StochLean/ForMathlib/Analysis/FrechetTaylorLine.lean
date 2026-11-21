/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.QuadraticTaylorSlope
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Second-order Taylor remainders along lines in real normed spaces

The scalar Lagrange remainder is applied to the actual line restriction.
No finite-dimensional assumption or globally bounded derivative is needed.
-/

@[expose] public section

open Set

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

theorem deriv_line_eq_fderiv (hf : Differentiable ℝ f) (a v : E) (t : ℝ) :
    deriv (fun r : ℝ ↦ f (a + r • v)) t = fderiv ℝ f (a + t • v) v := by
  have hl : HasDerivAt (fun r : ℝ ↦ a + r • v) v t := by
    simpa only [one_smul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const v)
  exact ((hf (a + t • v)).hasFDerivAt.comp_hasDerivAt t hl).deriv

theorem second_deriv_line_eq_fderiv (hf : ContDiff ℝ 2 f) (a v : E) (t : ℝ) :
    deriv (deriv (fun r : ℝ ↦ f (a + r • v))) t =
      fderiv ℝ (fderiv ℝ f) (a + t • v) v v := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hl : HasDerivAt (fun r : ℝ ↦ a + r • v) v t := by
    simpa only [one_smul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const v)
  have he : deriv (fun r : ℝ ↦ f (a + r • v)) =
      fun r ↦ fderiv ℝ f (a + r • v) v :=
    funext (deriv_line_eq_fderiv (hf.differentiable (by decide)) a v)
  rw [he]
  have hD := ((hd.differentiable (by decide)) (a + t • v)).hasFDerivAt
  have hD' : HasDerivAt (fun r : ℝ ↦ fderiv ℝ f (a + r • v))
      (fderiv ℝ (fderiv ℝ f) (a + t • v) v) t := hD.comp_hasDerivAt t hl
  have h := hD'.clm_apply (hasDerivAt_const t v)
  simpa only [map_zero, add_zero] using h.deriv

theorem exists_frechet_second_deriv_remainder (hf : ContDiff ℝ 2 f) (a b : E) :
    ∃ θ ∈ Icc (0 : ℝ) 1, f b - f a - fderiv ℝ f a (b - a) =
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) (b - a) (b - a) := by
  have hg : ContDiff ℝ 2 (fun r : ℝ ↦ f (a + r • (b - a))) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  obtain ⟨θ, hθ, he⟩ := exists_second_deriv_remainder hg 0 1
  refine ⟨θ, by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hθ, ?_⟩
  rw [deriv_line_eq_fderiv (hf.differentiable (by decide)),
    second_deriv_line_eq_fderiv hf] at he
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel, sub_zero, one_pow, mul_one,
    div_eq_mul_inv, mul_comm, one_mul] using he

theorem norm_frechet_second_order_remainder_le (hf : ContDiff ℝ 2 f) (a b : E)
    {C : ℝ} (hC : ∀ θ ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) - fderiv ℝ (fderiv ℝ f) a‖ ≤ C) :
    ‖f b - f a - fderiv ℝ f a (b - a) -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (b - a) (b - a)‖ ≤
      C / 2 * ‖b - a‖ ^ 2 := by
  obtain ⟨θ, hθ, he⟩ := exists_frechet_second_deriv_remainder hf a b
  rw [he, ← mul_sub]
  let L := fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) - fderiv ℝ (fderiv ℝ f) a
  have hL : ‖L (b - a) (b - a)‖ ≤ C * ‖b - a‖ ^ 2 := by
    calc
      _ ≤ ‖L (b - a)‖ * ‖b - a‖ := (L (b - a)).le_opNorm _
      _ ≤ (‖L‖ * ‖b - a‖) * ‖b - a‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
      _ ≤ (C * ‖b - a‖) * ‖b - a‖ := by gcongr; exact hC θ hθ
      _ = _ := by ring
  change ‖(1 / 2 : ℝ) * L (b - a) (b - a)‖ ≤ _
  rw [norm_mul, show ‖(1 / 2 : ℝ)‖ = 1 / 2 from by norm_num]
  nlinarith only [hL]

end StochLean

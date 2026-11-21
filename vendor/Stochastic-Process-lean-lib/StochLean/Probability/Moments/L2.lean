/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Real square integrals and the extended L2 norm -/

@[expose] public section

open Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {f g : Ω → ℝ}

theorem eLpNorm_two_eq_ofReal_integral_sq_rpow (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) :
    eLpNorm f 2 P = ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [show eLpNorm f 2 P =
      (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P) ^ (1 / 2 : ℝ) by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
    congr 2
    funext ω
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]]
  rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun ω ↦ sq_nonneg (f ω))]

theorem sq_eLpNorm_two_eq_ofReal_integral_sq (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) :
    (eLpNorm f 2 P) ^ 2 = ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂P) := by
  rw [eLpNorm_two_eq_ofReal_integral_sq_rpow hf, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem integral_sq_le_of_eLpNorm_two_le (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (h : eLpNorm f 2 P ≤ eLpNorm g 2 P) :
    ∫ ω, (f ω) ^ 2 ∂P ≤ ∫ ω, (g ω) ^ 2 ∂P := by
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun ω ↦ sq_nonneg (g ω)))).mp
  rw [← sq_eLpNorm_two_eq_ofReal_integral_sq hf.integrable_sq,
    ← sq_eLpNorm_two_eq_ofReal_integral_sq hg.integrable_sq]
  exact pow_le_pow_left' h 2

theorem eLpNorm_two_le_mul_of_integral_sq_le (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (C : ℝ≥0) (h : ∫ ω, (f ω) ^ 2 ∂P ≤ (C : ℝ) ^ 2 * ∫ ω, (g ω) ^ 2 ∂P) :
    eLpNorm f 2 P ≤ C * eLpNorm g 2 P := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, sq_eLpNorm_two_eq_ofReal_integral_sq hf.integrable_sq,
    sq_eLpNorm_two_eq_ofReal_integral_sq hg.integrable_sq]
  convert ENNReal.ofReal_le_ofReal h using 1
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow C.coe_nonneg]
  simp only [ENNReal.ofReal_coe_nnreal]

theorem measure_norm_ge_le_integral_sq_div [IsFiniteMeasure P]
    (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ ‖f ω‖} ≤ ENNReal.ofReal ((∫ ω, (f ω) ^ 2 ∂P) / ε ^ 2) := by
  have hs : {ω | ε ^ 2 ≤ (f ω) ^ 2} = {ω | ε ≤ ‖f ω‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, ← sq_abs (f ω)]
    exact sq_le_sq₀ hε.le (abs_nonneg _)
  have h := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all P (fun ω ↦ sq_nonneg (f ω))) hf (ε ^ 2)
  rw [hs] at h
  have hb : P.real {ω | ε ≤ ‖f ω‖} ≤ (∫ ω, (f ω) ^ 2 ∂P) / ε ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa only [mul_comm] using h)
  calc
    _ = ENNReal.ofReal (P.real {ω | ε ≤ ‖f ω‖}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb

end MeasureTheory

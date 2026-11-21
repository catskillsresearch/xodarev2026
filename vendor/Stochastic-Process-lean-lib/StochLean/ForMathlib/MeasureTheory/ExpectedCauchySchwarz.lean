/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.EssSup

/-! # Expectation bounds from pathwise energy Cauchy--Schwarz

The finite-conjugate and both endpoint forms use extended lower integrals.
Thus infinite energies and the zero-times-infinity cases retain their meaning.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace StochLean

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A B C : Ω → ℝ≥0∞}

theorem lintegral_le_Lp_mul_Lq_of_ae_sqrt_mul
    (h : ∀ᵐ ω ∂P, A ω ≤ (B ω) ^ (1 / 2 : ℝ) * (C ω) ^ (1 / 2 : ℝ))
    (hB : AEMeasurable B P) (hC : AEMeasurable C P)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∫⁻ ω, A ω ∂P) ≤
      (∫⁻ ω, (B ω) ^ (p / 2) ∂P) ^ (1 / p) *
        (∫⁻ ω, (C ω) ^ (q / 2) ∂P) ^ (1 / q) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq
    (hB.pow_const (1 / 2 : ℝ)) (hC.pow_const (1 / 2 : ℝ))
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul, one_div_mul_eq_div] at hh
  exact (lintegral_mono_ae h).trans hh

theorem lintegral_le_Linfty_mul_L1_of_ae_sqrt_mul
    (h : ∀ᵐ ω ∂P, A ω ≤ (B ω) ^ (1 / 2 : ℝ) * (C ω) ^ (1 / 2 : ℝ))
    (hC : AEMeasurable C P) :
    (∫⁻ ω, A ω ∂P) ≤
      essSup (fun ω ↦ (B ω) ^ (1 / 2 : ℝ)) P * (∫⁻ ω, (C ω) ^ (1 / 2 : ℝ) ∂P) := by
  rw [← lintegral_const_mul'' _ (hC.pow_const (1 / 2 : ℝ))]
  apply lintegral_mono_ae
  filter_upwards [h, ENNReal.ae_le_essSup (μ := P) (fun ω ↦ (B ω) ^ (1 / 2 : ℝ))]
    with ω hω hBω
  exact hω.trans (mul_le_mul' hBω le_rfl)

theorem lintegral_le_L1_mul_Linfty_of_ae_sqrt_mul
    (h : ∀ᵐ ω ∂P, A ω ≤ (B ω) ^ (1 / 2 : ℝ) * (C ω) ^ (1 / 2 : ℝ))
    (hB : AEMeasurable B P) :
    (∫⁻ ω, A ω ∂P) ≤
      (∫⁻ ω, (B ω) ^ (1 / 2 : ℝ) ∂P) * essSup (fun ω ↦ (C ω) ^ (1 / 2 : ℝ)) P := by
  have h' : ∀ᵐ ω ∂P, A ω ≤ (C ω) ^ (1 / 2 : ℝ) * (B ω) ^ (1 / 2 : ℝ) := by
    simpa only [mul_comm] using h
  simpa only [mul_comm] using lintegral_le_Linfty_mul_L1_of_ae_sqrt_mul h' hB

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.RNDerivativeCauchySchwarz
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Weighted Cauchy--Schwarz for three dominated measures

Weights are arbitrary measurable extended nonnegative functions. Both sides
are lower integrals, so no finite-energy premise or totalized Bochner integral
can hide a divergent case.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν ξ ρ : Measure Ω}
  [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ] [SigmaFinite ρ]

theorem lintegral_mul_le_of_rnDeriv_cauchySchwarz
    (hμρ : μ ≪ ρ) (hνρ : ν ≪ ρ) (hξρ : ξ ≪ ρ)
    (hd : ∀ᵐ ω ∂ρ, μ.rnDeriv ρ ω ≤
      (ν.rnDeriv ρ ω) ^ (1 / 2 : ℝ) * (ξ.rnDeriv ρ ω) ^ (1 / 2 : ℝ))
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, f ω * g ω ∂μ) ≤
      (∫⁻ ω, (f ω) ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, (g ω) ^ 2 ∂ξ) ^ (1 / 2 : ℝ) := by
  have hsq (x y : ℝ≥0∞) : (x * y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x ^ 2 * y := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul]
    norm_num
  have hF := hf.mul ((Measure.measurable_rnDeriv ν ρ).pow_const (1 / 2 : ℝ))
  have hG := hg.mul ((Measure.measurable_rnDeriv ξ ρ).pow_const (1 / 2 : ℝ))
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two
    hF.aemeasurable hG.aemeasurable
  have hEF : (∫⁻ ω, (f ω * (ν.rnDeriv ρ ω) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂ρ) =
      ∫⁻ ω, (f ω) ^ 2 ∂ν := by
    simp only [hsq]
    simp_rw [mul_comm ((f _) ^ 2)]
    exact lintegral_rnDeriv_mul hνρ (hf.pow_const 2).aemeasurable
  have hEG : (∫⁻ ω, (g ω * (ξ.rnDeriv ρ ω) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂ρ) =
      ∫⁻ ω, (g ω) ^ 2 ∂ξ := by
    simp only [hsq]
    simp_rw [mul_comm ((g _) ^ 2)]
    exact lintegral_rnDeriv_mul hξρ (hg.pow_const 2).aemeasurable
  simp only [Pi.mul_apply] at hholder
  rw [hEF, hEG] at hholder
  apply le_trans ?_ hholder
  rw [← lintegral_rnDeriv_mul (f := fun ω ↦ f ω * g ω) hμρ (hf.mul hg).aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [hd] with ω hω
  calc
    _ ≤ ((ν.rnDeriv ρ ω) ^ (1 / 2 : ℝ) * (ξ.rnDeriv ρ ω) ^ (1 / 2 : ℝ)) * (f ω * g ω) :=
      mul_le_mul' hω le_rfl
    _ = _ := by ac_rfl

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra
public import StochLean.ForMathlib.Analysis.ComplexRealLinear

/-! # Real linear functionals commute with complex-integrand integration

The proof expands the functional in the real basis (1, I) and uses only
linearity of the existing scalar integral on its legal adapted caglad domain.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}

theorem IsSemimartingale.stochasticIntegral_complex_component
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (L : ℂ →L[ℝ] ℝ) :
    Indistinguishable
      (hX.stochasticIntegral hF (fun t ↦ L.continuous.measurable.comp (ha t))
        (hr.continuous_comp L.continuous))
      (fun t ω ↦ L (hX.complexIntegrandIntegral hF ha hr t ω)) P := by
  let haR : Adapted F (fun t ω ↦ (H t ω).re) :=
    fun t ↦ Complex.continuous_re.measurable.comp (ha t)
  let haI : Adapted F (fun t ω ↦ (H t ω).im) :=
    fun t ↦ Complex.continuous_im.measurable.comp (ha t)
  let hrR := hr.continuous_comp Complex.continuous_re
  let hrI := hr.continuous_comp Complex.continuous_im
  let haA : Adapted F (fun t ω ↦ L 1 * (H t ω).re) := fun t ↦ (haR t).const_mul (L 1)
  let haB : Adapted F (fun t ω ↦ L Complex.I * (H t ω).im) :=
    fun t ↦ (haI t).const_mul (L Complex.I)
  let hrA := hrR.continuous_comp (continuous_const.mul continuous_id :
    Continuous (fun r : ℝ ↦ L 1 * r))
  let hrB := hrI.continuous_comp (continuous_const.mul continuous_id :
    Continuous (fun r : ℝ ↦ L Complex.I * r))
  have he := hX.stochasticIntegral_congr_integrand hF
    (fun t ↦ L.continuous.measurable.comp (ha t)) (hr.continuous_comp L.continuous)
    (fun t ↦ (haA t).add (haB t)) (hrA.add hrB)
    (ae_of_all _ (fun ω t ↦ realLinearMap_complex_apply L (H t ω)))
  filter_upwards [he, hX.stochasticIntegral_add hF haA hrA haB hrB,
    hX.stochasticIntegral_smul hF haR hrR (L 1),
    hX.stochasticIntegral_smul hF haI hrI (L Complex.I)] with ω heω hs hR hI t
  rw [heω t, hs t]
  simp only [Pi.add_apply, hR t, hI t, Pi.smul_apply, smul_eq_mul]
  rw [realLinearMap_complex_apply L (hX.complexIntegrandIntegral hF ha hr t ω)]
  rfl

theorem IsSemimartingale.complexIntegrandIntegral_const_mul
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (c : ℂ) :
    Indistinguishable
      (hX.complexIntegrandIntegral hF (fun t ↦ (ha t).const_mul c)
        (hr.continuous_comp (continuous_const.mul continuous_id)))
      (fun t ω ↦ c * hX.complexIntegrandIntegral hF ha hr t ω) P := by
  let M : ℂ →L[ℝ] ℂ := c • (1 : ℂ →L[ℝ] ℂ)
  filter_upwards [hX.stochasticIntegral_complex_component hF ha hr (Complex.reCLM.comp M),
    hX.stochasticIntegral_complex_component hF ha hr (Complex.imCLM.comp M)]
      with ω hR hI t
  apply Complex.ext
  · exact hR t
  · exact hI t

end ProbabilityTheory

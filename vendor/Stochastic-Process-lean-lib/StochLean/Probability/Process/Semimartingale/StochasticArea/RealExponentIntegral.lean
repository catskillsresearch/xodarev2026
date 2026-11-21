/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.RealDynamics
public import StochLean.Probability.Process.Semimartingale.Complex.ConstantIntegrator
public import StochLean.Probability.Process.Semimartingale.Complex.Associativity
public import StochLean.Probability.Process.Semimartingale.Complex.IntegratorAlgebra

/-! # Complex-valued integration against the real area exponent

The proved real-coordinate representation and the existing integral algebra
identify every adapted caglad complex integral against it. The outer initial
product `H_0 beta(0)` is retained, not implicitly assumed to vanish.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.complexIntegrandIntegral_stochasticAreaExponent_re
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
    let haAX : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * X t ω) :=
      fun t ↦ (haA t).mul (hX.adapted t)
    let hrAX := hrA.mul hcX.hasCagladPaths
    let haAY : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * Y t ω) :=
      fun t ↦ (haA t).mul (hY.adapted t)
    let hrAY := hrA.mul hcY.hasCagladPaths
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
      simpa only [pow_two, Pi.mul_def, Pi.add_def] using
        (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
          (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
    let haD : Adapted F (fun t ω ↦ (X t ω ^ 2 + Y t ω ^ 2) *
        (levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2)) :=
      fun t ↦ (haR t).mul (((haA t).pow_const 2).sub measurable_const)
    let hrD := hrR.mul (hcQ.hasCagladPaths.continuous_comp
      ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2))))
    let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
    Indistinguishable (hK.1.complexIntegrandIntegral hF ha hr)
      (fun t ω ↦ H 0 ω * (levyAreaBeta u T 0 : ℂ) -
        hX.complexIntegrandIntegral hF
          (fun r ↦ (ha r).mul (Complex.continuous_ofReal.measurable.comp (haAX r)))
          (hr.mul (hrAX.continuous_comp Complex.continuous_ofReal)) t ω -
        hY.complexIntegrandIntegral hF
          (fun r ↦ (ha r).mul (Complex.continuous_ofReal.measurable.comp (haAY r)))
          (hr.mul (hrAY.continuous_comp Complex.continuous_ofReal)) t ω -
        (1 / 2 : ℂ) * hQ.complexIntegrandIntegral hF
          (fun r ↦ (ha r).mul (Complex.continuous_ofReal.measurable.comp (haD r)))
          (hr.mul (hrD.continuous_comp Complex.continuous_ofReal)) t ω) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
  let haAX : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * X t ω) :=
    fun t ↦ (haA t).mul (hX.adapted t)
  let hrAX := hrA.mul hcX.hasCagladPaths
  let haAY : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * Y t ω) :=
    fun t ↦ (haA t).mul (hY.adapted t)
  let hrAY := hrA.mul hcY.hasCagladPaths
  let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
    fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
  let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
    simpa only [pow_two, Pi.mul_def, Pi.add_def] using
      (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
        (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
  let haD : Adapted F (fun t ω ↦ (X t ω ^ 2 + Y t ω ^ 2) *
      (levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2)) :=
    fun t ↦ (haR t).mul (((haA t).pow_const 2).sub measurable_const)
  let hrD := hrR.mul (hcQ.hasCagladPaths.continuous_comp
    ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2))))
  let hJX := hX.isSemimartingale_stochasticIntegral hF haAX hrAX
  let hJY := hY.isSemimartingale_stochasticIntegral hF haAY hrAY
  let hJD := hQ.isSemimartingale_stochasticIntegral hF haD hrD
  let hC := isSemimartingale_const_initial (P := P) (F := F)
    (Z := fun _ : Ω ↦ levyAreaBeta u T 0) measurable_const
  let hS1 := hC.sub hJX
  let hS2 := hS1.sub hJY
  let hS3 := hS2.sub (hJD.const_mul (1 / 2 : ℝ))
  let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
  have he := hK.1.complexIntegrandIntegral_congr_integrator hS3 hF ha hr
    (hX.stochasticAreaExponent_re_eq_integrals hY hQ hF hqX hqY
      hcX hcY hvQ hcQ h0X h0Y h0Q u T)
  filter_upwards [he, hS2.complexIntegrandIntegral_sub_integrator
      (hJD.const_mul (1 / 2 : ℝ)) hF ha hr,
    hS1.complexIntegrandIntegral_sub_integrator hJY hF ha hr,
    hC.complexIntegrandIntegral_sub_integrator hJX hF ha hr,
    complexIntegrandIntegral_const_initial (P := P) (F := F)
      (Z := fun _ : Ω ↦ levyAreaBeta u T 0) measurable_const hF ha hr,
    hJD.complexIntegrandIntegral_const_mul_integrator hF ha hr (1 / 2 : ℝ),
    hX.complexIntegrandIntegral_stochasticIntegral hF ha hr haAX hrAX,
    hY.complexIntegrandIntegral_stochasticIntegral hF ha hr haAY hrAY,
    hQ.complexIntegrandIntegral_stochasticIntegral hF ha hr haD hrD]
      with ω heω hs3 hs2 hs1 hconst hd hx hy hq t
  rw [heω t, hs3 t]
  simp only [Pi.sub_apply, hs2 t, hs1 t, hconst t, hd t, Pi.smul_apply,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    hx t, hy t, hq t]

end ProbabilityTheory

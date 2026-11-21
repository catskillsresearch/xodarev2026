/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.RadiusBracket
public import StochLean.Probability.Process.Semimartingale.StochasticArea.Exponent
public import StochLean.Probability.Process.Semimartingale.Complex.QuadraticVariation
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousFVMultiplier

/-! # Brackets of the actual Riccati-compensated area exponent

The squared-radius bracket and FV multiplier calculus identify both coordinate
brackets and the vanishing cross bracket. Their combination proves the actual
complex bilinear bracket, distinct from the nonnegative energy. No assumed
stochastic differential supplies the result.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticVariation_stochasticAreaExponent_re
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
      simpa only [pow_two, Pi.mul_def, Pi.add_def] using
        (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
          (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
    let hrA2 : HasCagladPaths (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2) P := by
      simpa only [pow_two, Pi.mul_def] using hrA.mul hrA
    let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
    Indistinguishable (hK.1.continuousQuadraticVariation hF)
      (hQ.stochasticIntegral hF
        (fun t ↦ ((haA t).pow_const 2).mul (haR t)) (hrA2.mul hrR)) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let hβ : ContDiff ℝ 1 (levyAreaBeta u T) := contDiff_levyAreaBeta u T
  let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hvQ hcQ hα
  let hB := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hvQ hcQ hβ
  let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
  let haA2 : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2) :=
    fun t ↦ (haA t).pow_const 2
  let hrA2 : HasCagladPaths (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2) P := by
    simpa only [pow_two, Pi.mul_def] using hrA.mul hrA
  let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
    fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
  have hcR : HasContinuousPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
    filter_upwards [hcX, hcY] with ω hx hy
    exact (hx.pow 2).add (hy.pow 2)
  let hrR := hcR.hasCagladPaths
  let hJ := hQ.isSemimartingale_stochasticIntegral hF haR hrR
  have hqR := hX.continuousQuadraticVariation_sq_add_sq_of_orthogonal_clock hY hQ hF
    hqX hqY ho hcX hcY hvQ h0X h0Y
  let hQR := hR.isSemimartingale_continuousQuadraticVariation hF
  have hi := hQR.stochasticIntegral_congr_integrator (hJ.const_mul 4) hF haA2 hrA2 hqR
  have hvB := hvQ.contDiff_comp hcQ hβ
  let hC := (hA.mul hR hF).const_mul (-(1 / 2 : ℝ))
  let hU := hC.add hB
  change Indistinguishable (hU.continuousQuadraticVariation hF)
    (hQ.stochasticIntegral hF (fun t ↦ (haA2 t).mul (haR t)) (hrA2.mul hrR)) P
  filter_upwards [hC.continuousQuadraticVariation_add_finiteVariation hB hF hvB,
    (hA.mul hR hF).continuousQuadraticVariation_const_mul hF (-(1 / 2 : ℝ)),
    hQ.continuousQuadraticVariation_contDiff_clock_mul hR hF hvQ hcQ hcR h0Q hα,
    hi, hJ.stochasticIntegral_const_mul_integrator hF haA2 hrA2 4,
    hQ.stochasticIntegral_stochasticIntegral hF haA2 hrA2 haR hrR]
      with ω hb hs hm hiω hc ha t
  rw [hb t, hs t]
  simp only [Pi.smul_apply, smul_eq_mul, hm t, hiω t, hc t, ha t]
  ring

theorem IsSemimartingale.continuousQuadraticVariation_stochasticAreaExponent_im
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P) (u T : ℝ) :
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
      simpa only [pow_two, Pi.mul_def, Pi.add_def] using
        (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
          (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
    let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
    Indistinguishable (hK.2.continuousQuadraticVariation hF)
      (fun t ω ↦ u ^ 2 * hQ.stochasticIntegral hF haR hrR t ω) P := by
  let hArea := hX.isSemimartingale_stochasticArea hY hF
  let hI := hArea.const_mul u
  filter_upwards [hArea.continuousQuadraticVariation_const_mul hF u,
    hX.continuousQuadraticVariation_stochasticArea_of_orthogonal_clock hY hQ hF
      hcX hcY hqX hqY ho] with ω hs ha t
  change hI.continuousQuadraticVariation hF t ω = _
  rw [hs t]
  simp only [Pi.smul_apply, smul_eq_mul, ha t]

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticAreaExponent_re_im
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
    Indistinguishable (hK.1.continuousQuadraticCovariation hK.2 hF) 0 P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let hβ : ContDiff ℝ 1 (levyAreaBeta u T) := contDiff_levyAreaBeta u T
  let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hvQ hcQ hα
  let hB := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hvQ hcQ hβ
  let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
  let hArea := hX.isSemimartingale_stochasticArea hY hF
  let hAR := hA.mul hR hF
  let hC := hAR.const_mul (-(1 / 2 : ℝ))
  let hU := hC.add hB
  let hI := hArea.const_mul u
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
  have hcR : HasContinuousPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
    filter_upwards [hcX, hcY] with ω hx hy
    exact (hx.pow 2).add (hy.pow 2)
  have hvB := hvQ.contDiff_comp hcQ hβ
  have hzR := hX.continuousQuadraticCovariation_sq_add_sq_stochasticArea hY hQ hF
    hqX hqY ho hcX hcY hvQ h0X h0Y
  let hBkt := hR.isSemimartingale_continuousQuadraticCovariation hArea hF
  have hzI := hBkt.stochasticIntegral_eq_zero_of_integrator_eq_zero hF haA hrA hzR
  have hm := hQ.continuousQuadraticCovariation_contDiff_clock_mul_left hR hArea hF
    hvQ hcQ hcR h0Q hα
  change Indistinguishable (hU.continuousQuadraticCovariation hI hF) 0 P
  filter_upwards [hC.continuousQuadraticCovariation_add_finiteVariation_left hI hB hF hvB,
    hAR.continuousQuadraticCovariation_const_mul_left hI hF (-(1 / 2 : ℝ)),
    hAR.continuousQuadraticCovariation_const_mul_right hArea hF u, hm.trans hzI]
      with ω hb hs hi hz t
  rw [hb t, hs t]
  simp only [Pi.smul_apply, smul_eq_mul, hi t, hz t, Pi.zero_apply, mul_zero]

theorem IsSemimartingale.continuousQuadraticVariation_stochasticAreaExponent
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
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
    Indistinguishable (hK.continuousQuadraticVariation hF)
      (fun t ω ↦ (hQ.stochasticIntegral hF haD hrD t ω : ℂ)) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
  let hrA2 : HasCagladPaths (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2) P := by
    simpa only [pow_two, Pi.mul_def] using hrA.mul hrA
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
  let haV : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2 *
      (X t ω ^ 2 + Y t ω ^ 2)) := fun t ↦ ((haA t).pow_const 2).mul (haR t)
  let hrV := hrA2.mul hrR
  let haW : Adapted F (fun t ω ↦ u ^ 2 * (X t ω ^ 2 + Y t ω ^ 2)) :=
    fun t ↦ (haR t).const_mul (u ^ 2)
  let hrW := hrR.continuous_comp
    (continuous_const.mul continuous_id : Continuous (fun x : ℝ ↦ u ^ 2 * x))
  have he := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ (haV t).sub (haW t)) (hrV.sub hrW) haD hrD
    (Eventually.of_forall fun _ _ ↦ by
      dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
      ring)
  have hcqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P := by
    filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hcX, hqX, h0X]
      with ω hc hq hz t
    simpa only [hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc t
  have hcqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P := by
    filter_upwards [hY.continuousQuadraticVariation_eq_of_continuous hF hcY, hqY, h0Y]
      with ω hc hq hz t
    simpa only [hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc t
  filter_upwards [hX.continuousQuadraticVariation_stochasticAreaExponent_re hY hQ hF
      hqX hqY ho hcX hcY hvQ hcQ h0X h0Y h0Q u T,
    hX.continuousQuadraticVariation_stochasticAreaExponent_im hY hQ hF
      hcX hcY hcqX hcqY ho u T,
    hX.continuousQuadraticCovariation_stochasticAreaExponent_re_im hY hQ hF
      hqX hqY ho hcX hcY hvQ hcQ h0X h0Y h0Q u T,
    hQ.stochasticIntegral_sub hF haV hrV haW hrW,
    hQ.stochasticIntegral_smul hF haR hrR (u ^ 2), he]
      with ω hr hi hm hs hu heω t
  have hs' := hs t
  have hu' := hu t
  dsimp only [Pi.sub_apply] at hs'
  dsimp only [Pi.smul_apply, smul_eq_mul] at hu'
  rw [heω t] at hs'
  apply Complex.ext
  · change _ - _ = hQ.stochasticIntegral hF haD hrD t ω
    rw [hr t, hi t]
    linarith
  · change 2 * _ = (0 : ℝ)
    rw [hm t]
    simp only [Pi.zero_apply, mul_zero]

end ProbabilityTheory

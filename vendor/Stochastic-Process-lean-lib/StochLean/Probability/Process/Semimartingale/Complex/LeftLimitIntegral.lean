/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.RealLinearIntegral
public import StochLean.Probability.Process.Path.ComplexLeftLimitLinear
public import StochLean.Probability.Process.Measurability.ComplexLeftLimit

/-! # Coordinate integrals of complex source left limits

Real-linear commutation includes the source time-zero convention and
identifies the existing scalar integrals, not just their positive-time values.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_complex_left_component
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F G) (hr : HasCadlagPaths G P) (L : ℂ →L[ℝ] ℝ) :
    let haL : Adapted F (fun t ω ↦ L (G t ω)) :=
      fun t ↦ L.continuous.measurable.comp (ha t)
    let hrL := hr.continuous_comp L.continuous
    Indistinguishable
      (hX.stochasticIntegral hF (haL.leftLimitProcess_of_usual hF hrL)
        hrL.hasCagladPaths_leftLimitProcess)
      (fun t ω ↦ L (hX.complexIntegrandIntegral hF
        (Adapted.complexLeftLimitProcess_of_usual ha hF hr)
        hr.hasCagladPaths_complexLeftLimitProcess t ω)) P := by
  dsimp only
  let haL : Adapted F (fun t ω ↦ L (G t ω)) :=
    fun t ↦ L.continuous.measurable.comp (ha t)
  let hrL := hr.continuous_comp L.continuous
  let haC := Adapted.complexLeftLimitProcess_of_usual ha hF hr
  let hrC := hr.hasCagladPaths_complexLeftLimitProcess
  exact (hX.stochasticIntegral_congr_integrand hF
    (haL.leftLimitProcess_of_usual hF hrL) hrL.hasCagladPaths_leftLimitProcess
    (fun t ↦ L.continuous.measurable.comp (haC t)) (hrC.continuous_comp L.continuous)
    (hr.leftLimitProcess_realLinear_complex L)).trans
      (hX.stochasticIntegral_complex_component hF haC hrC L)

theorem IsSemimartingale.stochasticIntegral_complex_left_component_of_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X E : ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F G) (hr : HasCadlagPaths G P) (L : ℂ →L[ℝ] ℝ)
    (haE : Adapted F E) (hrE : HasCadlagPaths E P) (he : ∀ t ω, E t ω = L (G t ω)) :
    Indistinguishable
      (hX.stochasticIntegral hF (haE.leftLimitProcess_of_usual hF hrE)
        hrE.hasCagladPaths_leftLimitProcess)
      (fun t ω ↦ L (hX.complexIntegrandIntegral hF
        (Adapted.complexLeftLimitProcess_of_usual ha hF hr)
        hr.hasCagladPaths_complexLeftLimitProcess t ω)) P := by
  have he' : E = fun t ω ↦ L (G t ω) := funext (fun t ↦ funext (he t))
  subst E
  exact hX.stochasticIntegral_complex_left_component hF ha hr L

end ProbabilityTheory

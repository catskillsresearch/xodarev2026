/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.ContinuousDynamics
public import StochLean.Probability.Process.Semimartingale.Complex.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.Complex.Associativity

/-! # Complex-valued integration against the actual continuous stochastic area

The source area representation and real-inner-integral associativity identify
the integral. Initial coordinates and the outer integrand may be nonzero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.complexIntegrandIntegral_stochasticArea
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let haHX : Adapted F (fun t ω ↦ H t ω * (X t ω : ℂ)) :=
      fun t ↦ (ha t).mul (Complex.continuous_ofReal.measurable.comp (hX.adapted t))
    let hrHX := hr.mul (hcX.hasCagladPaths.continuous_comp Complex.continuous_ofReal)
    let haHY : Adapted F (fun t ω ↦ H t ω * (Y t ω : ℂ)) :=
      fun t ↦ (ha t).mul (Complex.continuous_ofReal.measurable.comp (hY.adapted t))
    let hrHY := hr.mul (hcY.hasCagladPaths.continuous_comp Complex.continuous_ofReal)
    Indistinguishable
      ((hX.isSemimartingale_stochasticArea hY hF).complexIntegrandIntegral hF ha hr)
      (hY.complexIntegrandIntegral hF haHX hrHX - hX.complexIntegrandIntegral hF haHY hrHY) P := by
  let hJY := hY.isSemimartingale_stochasticIntegral hF hX.adapted hcX.hasCagladPaths
  let hJX := hX.isSemimartingale_stochasticIntegral hF hY.adapted hcY.hasCagladPaths
  let hA := hX.isSemimartingale_stochasticArea hY hF
  have he := hA.complexIntegrandIntegral_congr_integrator (hJY.sub hJX) hF ha hr
    (hX.stochasticArea_eq_integrals_of_continuous hY hF hcX hcY)
  filter_upwards [he, hJY.complexIntegrandIntegral_sub_integrator hJX hF ha hr,
    hY.complexIntegrandIntegral_stochasticIntegral hF ha hr hX.adapted hcX.hasCagladPaths,
    hX.complexIntegrandIntegral_stochasticIntegral hF ha hr hY.adapted hcY.hasCagladPaths]
      with ω heω hs hy hx t
  rw [heω t, hs t]
  simp only [Pi.sub_apply, hy t, hx t]

end ProbabilityTheory

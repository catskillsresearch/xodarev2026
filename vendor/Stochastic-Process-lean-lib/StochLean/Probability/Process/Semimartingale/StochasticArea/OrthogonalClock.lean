/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.ContinuousDynamics
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IsotropicIntegralPair

/-! # The actual area energy under an orthogonal continuous clock

Continuous coordinates identify the antisymmetric area with two actual
integrals. Their common-clock bracket contracts to the squared radius. Initial
coordinates need not vanish, and no Brownian or local-martingale law is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.continuousQuadraticVariation_stochasticArea_of_orthogonal_clock
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticArea hY hF).continuousQuadraticVariation hF)
      (hQ.stochasticIntegral (H := fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) hF
        (fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2))
        (by
          simpa only [pow_two, Pi.mul_def, Pi.add_def] using
            (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
              (hcY.hasCagladPaths.mul hcY.hasCagladPaths))) P := by
  let haN : Adapted F (fun t ω ↦ (-1 : ℝ) * Y t ω) :=
    fun t ↦ (hY.adapted t).const_mul (-1)
  let hrN := hcY.hasCagladPaths.continuous_comp
    (continuous_const.mul continuous_id : Continuous (fun x : ℝ ↦ (-1 : ℝ) * x))
  let hJ := (hX.isSemimartingale_stochasticIntegral hF haN hrN).add
    (hY.isSemimartingale_stochasticIntegral hF hX.adapted hcX.hasCagladPaths)
  have he : Indistinguishable (hX.stochasticArea hY hF)
      (hX.stochasticIntegral hF haN hrN +
        hY.stochasticIntegral hF hX.adapted hcX.hasCagladPaths) P := by
    filter_upwards [hX.stochasticArea_eq_integrals_of_continuous hY hF hcX hcY,
      hX.stochasticIntegral_smul hF hY.adapted hcY.hasCagladPaths (-1)] with ω ha hn t
    simp only [ha t, Pi.sub_apply, Pi.add_apply, hn t, Pi.smul_apply, smul_eq_mul]
    ring
  have hi := hX.continuousQuadraticVariation_stochasticIntegral_pair hY hQ hF hqX hqY ho
    haN hrN hX.adapted hcX.hasCagladPaths
  have hc := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ ((haN t).pow_const 2).add ((hX.adapted t).pow_const 2))
    (by simpa only [pow_two, Pi.mul_def, Pi.add_def]
      using (hrN.mul hrN).add (hcX.hasCagladPaths.mul hcX.hasCagladPaths))
    (fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2))
    (by
      simpa only [pow_two, Pi.mul_def, Pi.add_def] using
        (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
          (hcY.hasCagladPaths.mul hcY.hasCagladPaths))
    (Eventually.of_forall fun _ _ ↦ by
      dsimp only [Pi.add_apply, Pi.mul_apply]
      ring)
  exact ((hX.isSemimartingale_stochasticArea hY hF).continuousQuadraticVariation_congr
    hJ hF he).trans (hi.trans hc)

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Associativity
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra

/-! # Complex outer integrands in real stochastic-integral associativity

The coordinatewise real associativity theorem gives integration against an
actual real stochastic integral. The product integrand is the original
complex integrand times the real inner integrand, including initial products.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.complexIntegrandIntegral_stochasticIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X K : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    let haP : Adapted F (fun t ω ↦ H t ω * (K t ω : ℂ)) :=
      fun t ↦ (haH t).mul (Complex.continuous_ofReal.measurable.comp (haK t))
    let hrP := hrH.mul (hrK.continuous_comp Complex.continuous_ofReal)
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF haK hrK).complexIntegrandIntegral hF haH hrH)
      (hX.complexIntegrandIntegral hF haP hrP) P := by
  let haP : Adapted F (fun t ω ↦ H t ω * (K t ω : ℂ)) :=
    fun t ↦ (haH t).mul (Complex.continuous_ofReal.measurable.comp (haK t))
  let hrP := hrH.mul (hrK.continuous_comp Complex.continuous_ofReal)
  let haR : Adapted F (fun t ω ↦ (H t ω).re) :=
    fun t ↦ Complex.continuous_re.measurable.comp (haH t)
  let haI : Adapted F (fun t ω ↦ (H t ω).im) :=
    fun t ↦ Complex.continuous_im.measurable.comp (haH t)
  let hrR := hrH.continuous_comp Complex.continuous_re
  let hrI := hrH.continuous_comp Complex.continuous_im
  have heR := hX.stochasticIntegral_congr_integrand hF
    (fun t ↦ Complex.continuous_re.measurable.comp (haP t))
    (hrP.continuous_comp Complex.continuous_re)
    (fun t ↦ (haR t).mul (haK t)) (hrR.mul hrK)
    (Eventually.of_forall fun _ _ ↦ by simp)
  have heI := hX.stochasticIntegral_congr_integrand hF
    (fun t ↦ Complex.continuous_im.measurable.comp (haP t))
    (hrP.continuous_comp Complex.continuous_im)
    (fun t ↦ (haI t).mul (haK t)) (hrI.mul hrK)
    (Eventually.of_forall fun _ _ ↦ by simp)
  filter_upwards [hX.stochasticIntegral_stochasticIntegral hF haR hrR haK hrK,
    hX.stochasticIntegral_stochasticIntegral hF haI hrI haK hrK, heR, heI]
      with ω hR hI heRω heIω t
  exact Complex.ext ((hR t).trans (heRω t).symm) ((hI t).trans (heIω t).symm)

end ProbabilityTheory

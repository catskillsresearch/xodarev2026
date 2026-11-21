/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.LeftLimitIntegral

/-! # Combining the two real coordinate gradient integrals -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_complex_left_gradient
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y A B : ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F G) (hr : HasCadlagPaths G P) (L : ℂ →L[ℝ] ℝ)
    (haA : Adapted F A) (hrA : HasCadlagPaths A P)
    (haB : Adapted F B) (hrB : HasCadlagPaths B P)
    (hA : ∀ t ω, A t ω = L (G t ω))
    (hB : ∀ t ω, B t ω = L (Complex.I * G t ω)) :
    Indistinguishable
      (hX.stochasticIntegral hF (haA.leftLimitProcess_of_usual hF hrA)
          hrA.hasCagladPaths_leftLimitProcess +
        hY.stochasticIntegral hF (haB.leftLimitProcess_of_usual hF hrB)
          hrB.hasCagladPaths_leftLimitProcess)
      (fun t ω ↦ L ((hX.complex hY).stochasticIntegral hF
        (Adapted.complexLeftLimitProcess_of_usual ha hF hr)
        hr.hasCagladPaths_complexLeftLimitProcess t ω)) P := by
  let LI : ℂ →L[ℝ] ℝ := L.comp (Complex.I • (1 : ℂ →L[ℝ] ℂ))
  filter_upwards [hX.stochasticIntegral_complex_left_component_of_eq hF ha hr L haA hrA hA,
    hY.stochasticIntegral_complex_left_component_of_eq hF ha hr LI haB hrB hB]
      with ω hR hI t
  simpa only [IsComplexSemimartingale.stochasticIntegral, complexProcess, Pi.add_apply,
    Pi.smul_apply,
    smul_eq_mul, map_add, LI, ContinuousLinearMap.comp_apply, smul_apply,
    one_apply_eq_self] using congrArg₂ (· + ·) (hR t) (hI t)

end ProbabilityTheory

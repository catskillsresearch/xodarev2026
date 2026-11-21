/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Integral

/-! # Protter II.29: quadratic variation of a stochastic integral

The square formula follows from the already-proved mixed identity and the
diagonal of the same raw bracket. Initial squares are not discarded.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticVariation_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF ha hr).quadraticVariation hF)
      ((hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF
        (fun t ↦ (ha t).pow_const (2 : ℕ))
        (hr.continuous_comp (f := fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2))) P := by
  let hJ := hX.isSemimartingale_stochasticIntegral hF ha hr
  let hQ := hX.isSemimartingale_quadraticVariation hF
  have hdiag := IsSemimartingale.stochasticIntegral_congr_integrator
    (hX.isSemimartingale_quadraticCovariation hX hF) hQ hF
    (fun t ↦ (ha t).mul (ha t)) (hr.mul hr) (hX.quadraticCovariation_self hF)
  have hsq := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ (ha t).mul (ha t)) (hr.mul hr)
    (fun t ↦ (ha t).pow_const (2 : ℕ))
    (hr.continuous_comp (f := fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2))
    (ae_of_all _ fun _ _ ↦ (pow_two _).symm)
  exact (hJ.quadraticCovariation_self hF).symm.trans
    ((hX.quadraticCovariation_stochasticIntegral_both hX hF ha hr ha hr).trans
      (hdiag.trans hsq))

end ProbabilityTheory

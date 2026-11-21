/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ConstantIntegrator

/-! # The general integral theorem retains arbitrary initial values

This consumer invokes the actual general local-martingale integration theorem
on an arbitrary initial-measurable random constant. The integral is the original
initial product, not zero. If that product is not integrable, the conclusion
cannot be strengthened to true UI martingality.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ} {H : ℝ≥0 → Ω → ℝ}

/-- Actual III.33 applies even when the initial product has no first moment.
The old constant-integrator identity independently checks the retained term. -/
theorem stochasticIntegral_arbitrary_initial_constant_localMartingale
    (hZ : Measurable[F 0] Z) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let J := (isSemimartingale_const_initial (P := P) hZ).stochasticIntegral hF ha hr
    IsLocalMartingale J F P ∧ Indistinguishable J (fun _ ω ↦ H 0 ω * Z ω) P ∧
      (¬ Integrable (fun ω ↦ H 0 ω * Z ω) P → ¬ IsUIMartingale J F P) := by
  intro J
  have hM := (isContinuousLocalMartingale_const_initial (P := P) hZ).1
  have hJ : IsLocalMartingale J F P := hM.isLocalMartingale_stochasticIntegral hF ha hr
  have he := stochasticIntegral_const_initial hZ hF ha hr
  refine ⟨hJ, he, ?_⟩
  intro hi hu
  exact hi ((hu.1.integrable 0).congr (he.ae_eq 0))

end ProbabilityTheory

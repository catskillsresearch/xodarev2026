/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.ContinuousLocalMartingale
public import StochLean.Probability.Process.LocalMartingale.NonnegativeSupermartingale
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedUsual

/-! # Positive stochastic exponentials are supermartingales

This is the preliminary lemma before Protter III.43.  It is stated for the
single product-defined stochastic exponential already owned by the project.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure P] [SigmaFiniteFiltration P F]

/-- A zero-starting continuous local martingale has a positive stochastic
exponential supermartingale. -/
theorem IsContinuousLocalMartingale.supermartingale_stochasticExponential
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) :
    Supermartingale ((hM.isSemimartingale hF).stochasticExponential hF) F P := by
  let hS := hM.isSemimartingale hF
  let E := hS.stochasticExponential hF
  have hE := hM.isContinuousLocalMartingale_stochasticExponential hF
  have hEi : Integrable (E 0) P :=
    (integrable_const (1 : ℝ)).congr (hS.stochasticExponential_zero_ae hF h0).symm
  exact hE.1.supermartingale_of_nonneg hEi
    ((hS.stochasticExponential_pos_of_continuous hF hM.2).mono
      fun _ hω t ↦ (hω t).le)

/-- The expectation of the stochastic exponential at every bounded stopping
time is at most one. -/
theorem IsContinuousLocalMartingale.integral_stochasticExponential_stopped_le_one
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    (∫ ω, (hM.isSemimartingale hF).stochasticExponential hF (τ ω) ω ∂P) ≤ 1 := by
  let hS := hM.isSemimartingale hF
  let E := hS.stochasticExponential hF
  have hsm := hM.supermartingale_stochasticExponential hF h0
  have h := hsm.integral_finiteStoppingTime_value_le_initial_of_usual hF
    (hM.isContinuousLocalMartingale_stochasticExponential hF).2.hasRightContinuousPaths τ hb
  rw [integral_congr_ae (hS.stochasticExponential_zero_ae hF h0)] at h
  simpa only [Pi.one_apply, integral_const, probReal_univ, one_smul] using h

end ProbabilityTheory

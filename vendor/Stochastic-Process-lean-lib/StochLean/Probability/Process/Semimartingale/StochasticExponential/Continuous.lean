/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Basic
public import StochLean.Probability.Process.Semimartingale.Ito.Preservation
public import StochLean.Probability.Process.Semimartingale.UsualCongruence
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra

/-! # Continuous paths of the single product-defined stochastic exponential

The continuous case is a theorem about the same product expression, not a
separate exponential owner. No global moment or boundedness premise is imposed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.isSemimartingale_stochasticExponential_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    IsSemimartingale (hX.stochasticExponential hF) F P := by
  have hK := hX.sub ((hX.isSemimartingale_continuousQuadraticVariation hF).const_mul (1 / 2))
  exact (hK.contDiff_comp hF Real.contDiff_exp).congr_of_usual hF
    (hX.stochasticExponential_of_continuous hF hc).symm

theorem IsSemimartingale.hasContinuousPaths_stochasticExponential_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    HasContinuousPaths (hX.stochasticExponential hF) P := by
  filter_upwards [hc, hX.stochasticExponential_of_continuous hF hc] with ω hcω he
  have h : Continuous (fun t ↦ Real.exp
      (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω)) :=
    Real.continuous_exp.comp (hcω.sub
      ((hX.continuous_continuousQuadraticVariation hF ω).const_mul (1 / 2)))
  exact h.congr (fun t ↦ (he t).symm)

theorem IsSemimartingale.stochasticExponential_pos_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    ∀ᵐ ω ∂P, ∀ t, 0 < hX.stochasticExponential hF t ω := by
  filter_upwards [hX.stochasticExponential_of_continuous hF hc] with ω he t
  rw [he t]
  exact Real.exp_pos _

theorem IsSemimartingale.stochasticExponential_raw_formula_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (h0 : X 0 =ᵐ[P] 0) :
    Indistinguishable (hX.stochasticExponential hF)
      (fun t ω ↦ Real.exp (X t ω - (1 / 2 : ℝ) * hX.quadraticVariation hF t ω)) P := by
  filter_upwards [hX.stochasticExponential_of_continuous hF hc,
    hX.continuousQuadraticVariation_eq_of_continuous hF hc, h0] with ω he hq hzero t
  simpa only [hq t, hzero, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using he t

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.C1ChangeOfVariables
public import StochLean.Probability.Process.FiniteVariation.Integral
public import StochLean.Probability.Process.Semimartingale.FiniteVariation

/-! # Protter I.54: C1 change of variables for continuous FV processes

The increment formula has initial value subtracted. For the full Chapter II
integral, the separate `phi'(X_0) X_0` term is explicitly retained.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {φ : ℝ → ℝ}

theorem HasFiniteVariationPaths.contDiff_comp (hv : HasFiniteVariationPaths X P)
    (hx : HasContinuousPaths X P) (hφ : ContDiff ℝ 1 φ) :
    HasFiniteVariationPaths (fun t ω ↦ φ (X t ω)) P := by
  filter_upwards [hv, hx] with ω hvω hxω
  exact locallyBoundedVariationOn_contDiff_comp hvω hxω hφ

theorem isSemimartingale_contDiff_of_continuous_finiteVariation
    {F : Filtration ℝ≥0 mΩ} [IsFiniteMeasure P] (ha : Adapted F X) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) (hx : HasContinuousPaths X P) (hφ : ContDiff ℝ 1 φ) :
    IsSemimartingale (fun t ω ↦ φ (X t ω)) F P := by
  apply (hv.contDiff_comp hx hφ).isSemimartingale
    (fun t ↦ hφ.continuous.measurable.comp (ha t)) hF
  exact hx.mono fun _ hω ↦ IsContinuousPath.isCadlagPath (hφ.continuous.comp hω)

theorem ae_finiteVariationIntegral_contDiff
    (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))
    (hx : HasContinuousPaths X P) (hφ : ContDiff ℝ 1 φ) :
    ∀ᵐ ω ∂P, ∀ t, finiteVariationIntegral X hv hr (fun t ω ↦ deriv φ (X t ω)) t ω =
      deriv φ (X 0 ω) * X 0 ω + (φ (X t ω) - φ (X 0 ω)) := by
  filter_upwards [hx] with ω hω t
  exact pathStieltjesIntegral_chain_rule hω.continuousOn
    (fun z ↦ (hφ.differentiable_one z).hasDerivAt) hφ.continuous_deriv_one

theorem ae_pathStieltjesIncrementIntegral_substitution
    (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))
    (hx : HasContinuousPaths X P) {g : ℝ → ℝ} (hg : Continuous g) :
    ∀ᵐ ω ∂P, ∀ t, pathStieltjesIncrementIntegral (fun u ↦ X u ω) (hv ω) (hr ω)
      (fun u ↦ g (X u ω)) 0 t = ∫ v in X 0 ω..X t ω, g v :=
  hx.mono fun _ hω _ ↦ pathStieltjesIncrementIntegral_substitution hω.continuousOn hg

end ProbabilityTheory

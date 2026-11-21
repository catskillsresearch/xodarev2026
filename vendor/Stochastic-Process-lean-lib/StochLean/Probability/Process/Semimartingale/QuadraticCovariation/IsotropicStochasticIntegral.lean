/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IsotropicIntegral
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousIntegral
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.FiniteSum

/-! # Brackets of finite stochastic-integral sums under a common clock

The actual integral bracket theorem and finite-sum bilinearity reduce the
bracket to the existing isotropic contraction theorem. Empty index families,
arbitrary adapted caglad integrands and nonzero initial values are permitted.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X H K : ι → ℝ≥0 → Ω → ℝ} {Q : ℝ≥0 → Ω → ℝ}

theorem continuousQuadraticCovariation_sum_stochasticIntegral_of_isotropic
    (hX : ∀ i, IsSemimartingale (X i) F P) (hQ : IsSemimartingale Q F P)
    (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable ((hX i).continuousQuadraticCovariation (hX i) hF) Q P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P)
    (haH : ∀ i, Adapted F (H i)) (hrH : ∀ i, HasCagladPaths (H i) P)
    (haK : ∀ i, Adapted F (K i)) (hrK : ∀ i, HasCagladPaths (K i) P) :
    let hJ := fun i ↦ (hX i).isSemimartingale_stochasticIntegral hF (haH i) (hrH i)
    let hL := fun i ↦ (hX i).isSemimartingale_stochasticIntegral hF (haK i) (hrK i)
    Indistinguishable ((isSemimartingale_finset_sum univ hJ).continuousQuadraticCovariation
        (isSemimartingale_finset_sum univ hL) hF)
      (hQ.stochasticIntegral hF
        (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ (haH i t).mul (haK i t)))
        (HasCagladPaths.finset_sum univ (fun i _ ↦ (hrH i).mul (hrK i)))) P := by
  classical
  let hJ := fun i ↦ (hX i).isSemimartingale_stochasticIntegral hF (haH i) (hrH i)
  let hL := fun i ↦ (hX i).isSemimartingale_stochasticIntegral hF (haK i) (hrK i)
  have hi := ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦
    (hX i).continuousQuadraticCovariation_stochasticIntegral_both (hX j) hF
      (haH i) (hrH i) (haK j) (hrK j)
  filter_upwards [continuousQuadraticCovariation_finset_sum univ univ hJ hL hF, hi,
    continuousQuadraticCovariation_integral_sum_of_isotropic hX hQ hF hd ho
      (fun i j t ↦ (haH i t).mul (haK j t)) (fun i j ↦ (hrH i).mul (hrK j))]
      with ω hs hiω hc t
  rw [hs t, ← hc t]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ hiω i j t

theorem continuousQuadraticVariation_sum_stochasticIntegral_of_isotropic
    (hX : ∀ i, IsSemimartingale (X i) F P) (hQ : IsSemimartingale Q F P)
    (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable ((hX i).continuousQuadraticCovariation (hX i) hF) Q P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P)
    (ha : ∀ i, Adapted F (H i)) (hr : ∀ i, HasCagladPaths (H i) P) :
    let hJ := fun i ↦ (hX i).isSemimartingale_stochasticIntegral hF (ha i) (hr i)
    Indistinguishable ((isSemimartingale_finset_sum univ hJ).continuousQuadraticVariation hF)
      (hQ.stochasticIntegral (H := fun t ω ↦ ∑ i, H i t ω ^ 2) hF
        (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ (ha i t).pow_const 2))
        (HasCagladPaths.finset_sum univ
          (fun i _ ↦ by simpa only [pow_two, Pi.mul_def] using (hr i).mul (hr i)))) P := by
  classical
  let hJ := fun i ↦ (hX i).isSemimartingale_stochasticIntegral hF (ha i) (hr i)
  have hi := continuousQuadraticCovariation_sum_stochasticIntegral_of_isotropic
    hX hQ hF hd ho ha hr ha hr
  have he := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ (ha i t).mul (ha i t)))
    (HasCagladPaths.finset_sum univ (fun i _ ↦ (hr i).mul (hr i)))
    (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ (ha i t).pow_const 2))
    (HasCagladPaths.finset_sum univ
      (fun i _ ↦ by simpa only [pow_two, Pi.mul_def] using (hr i).mul (hr i)))
    (Eventually.of_forall fun ω t ↦ sum_congr rfl fun i _ ↦ (pow_two (H i t ω)).symm)
  exact ((isSemimartingale_finset_sum univ hJ).continuousQuadraticCovariation_self hF).symm.trans
    (hi.trans he)

end ProbabilityTheory

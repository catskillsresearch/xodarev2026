/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.FiniteSum
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation

/-! # Finite-sum linearity of the canonical stochastic integral

The identity retains the initial term and allows an arbitrary finite subset
of an uncountable family. All integrands are in the existing adapted-caglad
domain; no new integral operator or moment assumption is introduced.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_finset_sum
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {H : ι → ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (S : Finset ι)
    (ha : ∀ i, Adapted F (H i)) (hr : ∀ i, HasCagladPaths (H i) P) :
    Indistinguishable (hX.stochasticIntegral hF
      (fun t ↦ Finset.measurable_sum S (fun i _ ↦ ha i t))
      (HasCagladPaths.finset_sum S (fun i _ ↦ hr i)))
      (fun t ω ↦ ∑ i ∈ S, hX.stochasticIntegral hF (ha i) (hr i) t ω) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using hX.stochasticIntegral_zero_integrand hF
  | @insert i S hi ih =>
    let haS : Adapted F (fun t ω ↦ ∑ j ∈ S, H j t ω) :=
      fun t ↦ Finset.measurable_sum S (fun j _ ↦ ha j t)
    let hrS := HasCagladPaths.finset_sum S (fun j _ ↦ hr j)
    have he : Indistinguishable (fun t ω ↦ ∑ j ∈ insert i S, H j t ω)
        (H i + fun t ω ↦ ∑ j ∈ S, H j t ω) P := by
      apply Eventually.of_forall
      intro ω t
      exact Finset.sum_insert hi
    have hc := hX.stochasticIntegral_congr_integrand hF
      (fun t ↦ Finset.measurable_sum (insert i S) (fun j _ ↦ ha j t))
      (HasCagladPaths.finset_sum (insert i S) (fun j _ ↦ hr j))
      (fun t ↦ (ha i t).add (haS t)) ((hr i).add hrS) he
    filter_upwards [hc, hX.stochasticIntegral_add hF (ha i) (hr i) haS hrS, ih]
      with ω hcω haω hiω t
    rw [hcω t, haω t]
    simp only [Pi.add_apply, hiω t, Finset.sum_insert hi]

end ProbabilityTheory

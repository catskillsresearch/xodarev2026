/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteSum
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ZeroIntegrator
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra

/-! # Isotropic continuous brackets contract a matrix integrand to its trace

All mixed brackets are the existing canonical continuous covariations. When
off-diagonal brackets vanish and diagonal brackets share a clock, the full
ordered double sum of their integrals is the clock integral of the diagonal
sum. The statement includes empty coordinate families and arbitrary initial
integrand values, and imposes no moment assumptions.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal

namespace ProbabilityTheory

theorem continuousQuadraticCovariation_integral_sum_of_isotropic
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ}
    {H : ι → ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hA : IsSemimartingale A F P)
    (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable ((hX i).continuousQuadraticCovariation (hX i) hF) A P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P)
    (ha : ∀ i j, Adapted F (H i j)) (hr : ∀ i j, HasCagladPaths (H i j) P) :
    Indistinguishable (fun t ω ↦ ∑ i, ∑ j,
      ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF).stochasticIntegral
        hF (ha i j) (hr i j) t ω)
      (hA.stochasticIntegral hF
        (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ ha i i t))
        (HasCagladPaths.finset_sum univ (fun i _ ↦ hr i i))) P := by
  classical
  have he (i j : ι) : Indistinguishable
      (((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF).stochasticIntegral
        hF (ha i j) (hr i j))
      (fun t ω ↦ if i = j then hA.stochasticIntegral hF (ha i j) (hr i j) t ω else 0) P := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true] using IsSemimartingale.stochasticIntegral_congr_integrator
        ((hX i).isSemimartingale_continuousQuadraticCovariation (hX i) hF) hA hF
          (ha i i) (hr i i) (hd i)
    · simpa only [if_neg hij, Pi.zero_def] using
        IsSemimartingale.stochasticIntegral_eq_zero_of_integrator_eq_zero
          ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF) hF
          (ha i j) (hr i j) (ho i j hij)
  filter_upwards [ae_all_iff.2 (fun i ↦ ae_all_iff.2 (he i)),
    hA.stochasticIntegral_finset_sum hF univ (fun i ↦ ha i i) (fun i ↦ hr i i)]
      with ω heω hsω t
  rw [hsω t]
  apply sum_congr rfl
  intro i _
  calc
    _ = ∑ j, if i = j then hA.stochasticIntegral hF (ha i j) (hr i j) t ω else 0 :=
      sum_congr rfl (fun j _ ↦ heω i j t)
    _ = _ := by simp

theorem continuousQuadraticCovariation_integral_sum_eq_zero_of_trace_eq_zero
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ}
    {H : ι → ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hA : IsSemimartingale A F P)
    (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable ((hX i).continuousQuadraticCovariation (hX i) hF) A P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P)
    (ha : ∀ i j, Adapted F (H i j)) (hr : ∀ i j, HasCagladPaths (H i j) P)
    (htrace : Indistinguishable (fun t ω ↦ ∑ i, H i i t ω) 0 P) :
    Indistinguishable (fun t ω ↦ ∑ i, ∑ j,
      ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF).stochasticIntegral
        hF (ha i j) (hr i j) t ω) 0 P := by
  have hc := hA.stochasticIntegral_congr_integrand hF
    (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ ha i i t))
    (HasCagladPaths.finset_sum univ (fun i _ ↦ hr i i))
    (IsSimplePredictable.zero F).adapted ((IsSimplePredictable.zero F).hasCagladPaths P) htrace
  exact (continuousQuadraticCovariation_integral_sum_of_isotropic hX hA hF hd ho ha hr).trans
    (hc.trans (hA.stochasticIntegral_zero_integrand hF))

end ProbabilityTheory

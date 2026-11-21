/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Moments
public import StochLean.Probability.Process.Poisson.Semimartingale
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import StochLean.Probability.Process.Path.Subtraction
public import StochLean.ForMathlib.VariationAlgebra
public import Mathlib.Probability.ConditionalExpectation

/-! # The compensated Poisson martingale for an explicit filtration

The process is the actual real count minus its rate times time. Independent
future increments from the chosen past are explicit, so the theorem does not
assert a false martingale property for arbitrary enlarged filtrations.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem IsPoissonProcess.condExp_real_increment_of_indep_past
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N) {s t : ℝ≥0}
    (hi : Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P) :
    P[fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ) | F s] =ᵐ[P]
      fun _ ↦ (rate : ℝ) * ((t : ℝ) - s) := by
  have haR : Adapted F (fun t ω ↦ (N t ω : ℝ)) := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  have h := condExp_indep_eq ((haR.measurable (i := t)).sub
    (haR.measurable (i := s))).comap_le (F.le s)
    (comap_measurable (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ))).stronglyMeasurable hi.symm
  simpa only [hN.integral_real_increment s t] using h

theorem IsPoissonProcess.martingale_compensated_of_indep_past
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P) :
    Martingale (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) F P := by
  have haR : Adapted F (fun t ω ↦ (N t ω : ℝ)) := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  have haM : Adapted F (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) :=
    fun t ↦ (haR t).sub measurable_const
  refine ⟨haM.stronglyAdapted, fun s t hst ↦ ?_⟩
  have hinc := hN.condExp_real_increment_of_indep_past ha (hi s t hst)
  have hdiff := condExp_sub (hN.integrable_real t) (hN.integrable_real s) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) (haR s).stronglyMeasurable
    (hN.integrable_real s)] at hdiff
  have hcomp := condExp_sub (hN.integrable_real t) (integrable_const ((rate : ℝ) * t)) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) stronglyMeasurable_const
    (integrable_const ((rate : ℝ) * t))] at hcomp
  filter_upwards [hinc, hdiff, hcomp] with ω hiω hdω hcω
  change P[fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ) | F s] ω =
    P[fun ω ↦ (N t ω : ℝ) | F s] ω - (N s ω : ℝ) at hdω
  change P[fun ω ↦ (N t ω : ℝ) - (rate : ℝ) * t | F s] ω =
    P[fun ω ↦ (N t ω : ℝ) | F s] ω - (rate : ℝ) * t at hcω
  linear_combination hcω - hdω + hiω

theorem IsPoissonProcess.hasCadlagPaths_compensated (hN : IsPoissonProcess N rate P) :
    HasCadlagPaths (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) P := by
  apply hN.hasCadlagPaths_real.sub
  exact (show HasContinuousPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P from
    Filter.Eventually.of_forall fun _ ↦ continuous_const.mul NNReal.continuous_coe).hasCadlagPaths

theorem IsPoissonProcess.isLocalMartingale_compensated_of_indep_past
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P) :
    IsLocalMartingale (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) F P :=
  (hN.martingale_compensated_of_indep_past ha hi).isLocalMartingale hN.hasCadlagPaths_compensated

theorem IsPoissonProcess.hasFiniteVariationPaths_compensated (hN : IsPoissonProcess N rate P) :
    HasFiniteVariationPaths (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) P := by
  have hm : Monotone (fun t : ℝ≥0 ↦ (rate : ℝ) * t) := fun _ _ h ↦
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr h) rate.2
  filter_upwards [hN.hasFiniteVariationPaths_real] with ω hv
  exact StochLean.locallyBoundedVariationOn_sub hv
    (hm.monotoneOn Set.univ).locallyBoundedVariationOn

theorem IsPoissonProcess.isSemimartingale_compensated
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    IsSemimartingale (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) F P := by
  apply hN.hasFiniteVariationPaths_compensated.isSemimartingale _ hF hN.hasCadlagPaths_compensated
  intro t
  exact ((continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp
    (ha t)).sub measurable_const

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Basic
public import StochLean.Probability.Process.Semimartingale.FiniteVariation

/-! # The real-valued Poisson counting process is a semimartingale

Real left limits follow from monotonicity; right continuity is transported from the
canonical counting-process predicate. No cadlag path realization is assumed in addition
to those existing path properties. Adaptedness to the chosen filtration remains explicit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem hasMonotonePaths_real (hN : IsPoissonProcess N rate P) :
    HasMonotonePaths (fun t ω ↦ (N t ω : ℝ)) P := by
  filter_upwards [hN.monotonePaths] with ω hω
  intro s t hst
  change (N s ω : ℝ) ≤ (N t ω : ℝ)
  exact_mod_cast hω hst

theorem hasFiniteVariationPaths_real (hN : IsPoissonProcess N rate P) :
    HasFiniteVariationPaths (fun t ω ↦ (N t ω : ℝ)) P :=
  hN.hasMonotonePaths_real.hasFiniteVariationPaths

theorem hasCadlagPaths_real (hN : IsPoissonProcess N rate P) :
    HasCadlagPaths (fun t ω ↦ (N t ω : ℝ)) P := by
  filter_upwards [hN.hasMonotonePaths_real, hN.rightContinuousPaths] with ω hm hr
  refine ⟨fun t ↦ ?_, fun t _ ↦ ⟨Function.leftLim (fun s ↦ (N s ω : ℝ)) t, hm.tendsto_leftLim t⟩⟩
  have hcast : Continuous (fun n : ℕ ↦ (n : ℝ)) := continuous_of_discreteTopology
  exact hcast.continuousAt.comp_continuousWithinAt (hr t)

theorem isSemimartingale_real (hN : IsPoissonProcess N rate P)
    {F : Filtration ℝ≥0 mΩ} (hF : F.IsUsual P) (ha : Adapted F N) :
    IsSemimartingale (fun t ω ↦ (N t ω : ℝ)) F P := by
  apply hN.hasFiniteVariationPaths_real.isSemimartingale ?_ hF hN.hasCadlagPaths_real
  intro t
  exact (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)

end ProbabilityTheory.IsPoissonProcess

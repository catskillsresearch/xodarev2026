/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Variation

/-! # Canonical increasing components of a finite-variation process

Both components start at zero. They decompose increments, with the initial
random variable kept separate. No integrability of the variation is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def positiveVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathPositiveVariation (fun s ↦ X s ω) t

noncomputable def negativeVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathNegativeVariation (fun s ↦ X s ω) t

@[simp] theorem positiveVariationProcess_zero (X : ℝ≥0 → Ω → ℝ) :
    positiveVariationProcess X 0 = 0 := by
  funext ω
  exact pathPositiveVariation_zero _

@[simp] theorem negativeVariationProcess_zero (X : ℝ≥0 → Ω → ℝ) :
    negativeVariationProcess X 0 = 0 := by
  funext ω
  exact pathNegativeVariation_zero _

theorem positiveVariationProcess_add_negative (X : ℝ≥0 → Ω → ℝ) :
    positiveVariationProcess X + negativeVariationProcess X = totalVariationProcess X := by
  funext t ω
  exact pathPositiveVariation_add_negative _ t

theorem positiveVariationProcess_sub_negative (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    positiveVariationProcess X t ω - negativeVariationProcess X t ω = X t ω - X 0 ω :=
  pathPositiveVariation_sub_negative _ t

theorem finiteVariationProcess_reconstruction (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    X t ω = X 0 ω + positiveVariationProcess X t ω - negativeVariationProcess X t ω := by
  linarith [positiveVariationProcess_sub_negative X t ω]

theorem HasFiniteVariationPaths.hasMonotonePaths_positiveVariationProcess
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hv : HasFiniteVariationPaths X P) :
    HasMonotonePaths (positiveVariationProcess X) P :=
  hv.mono fun _ hω ↦ pathPositiveVariation_monotone hω

theorem HasFiniteVariationPaths.hasMonotonePaths_negativeVariationProcess
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hv : HasFiniteVariationPaths X P) :
    HasMonotonePaths (negativeVariationProcess X) P :=
  hv.mono fun _ hω ↦ pathNegativeVariation_monotone hω

theorem HasFiniteVariationPaths.hasCadlagPaths_positiveVariationProcess
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hv : HasFiniteVariationPaths X P)
    (hr : HasRightContinuousPaths X P) : HasCadlagPaths (positiveVariationProcess X) P := by
  filter_upwards [hv, hr] with ω hvω hrω
  have hm := pathPositiveVariation_monotone hvω
  refine ⟨?_, fun t _ ↦ ⟨_, hm.tendsto_leftLim t⟩⟩
  intro t
  have h := rightContinuous_pathTotalVariation hvω hrω t
  exact ((h.add (hrω t)).sub_const (X 0 ω)).div_const 2

theorem HasFiniteVariationPaths.hasCadlagPaths_negativeVariationProcess
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hv : HasFiniteVariationPaths X P)
    (hr : HasRightContinuousPaths X P) : HasCadlagPaths (negativeVariationProcess X) P := by
  filter_upwards [hv, hr] with ω hvω hrω
  have hm := pathNegativeVariation_monotone hvω
  refine ⟨?_, fun t _ ↦ ⟨_, hm.tendsto_leftLim t⟩⟩
  intro t
  have h := rightContinuous_pathTotalVariation hvω hrω t
  exact ((h.sub (hrω t)).add_const (X 0 ω)).div_const 2

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem Adapted.positiveVariationProcess_of_rightContinuous (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.positiveVariationProcess X) := by
  intro t
  have h := ha.totalVariationProcess_of_rightContinuous hr t
  exact ((h.add (ha t)).sub ((ha 0).mono (F.mono bot_le) le_rfl)).div_const 2

theorem Adapted.negativeVariationProcess_of_rightContinuous (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.negativeVariationProcess X) := by
  intro t
  have h := ha.totalVariationProcess_of_rightContinuous hr t
  exact ((h.sub (ha t)).add ((ha 0).mono (F.mono bot_le) le_rfl)).div_const 2

theorem Adapted.positiveVariationProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.positiveVariationProcess X) := by
  intro t
  have h := ha.totalVariationProcess_of_usual hF hc t
  exact ((h.add (ha t)).sub ((ha 0).mono (F.mono bot_le) le_rfl)).div_const 2

theorem Adapted.negativeVariationProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.negativeVariationProcess X) := by
  intro t
  have h := ha.totalVariationProcess_of_usual hF hc t
  exact ((h.sub (ha t)).add ((ha 0).mono (F.mono bot_le) le_rfl)).div_const 2

end MeasureTheory

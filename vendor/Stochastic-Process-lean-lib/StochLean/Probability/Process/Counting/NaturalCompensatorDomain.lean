/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Compensator
public import StochLean.Probability.Process.Filtration.Augmentation
public import StochLean.Probability.Independence.Completion

/-! # Natural compensation domain for an almost-sure counting process

An original coordinatewise measurable count satisfying the actual almost-
sure counting-process predicate has its compensation domain in its genuine
usual natural augmentation. The original count is retained on exceptional
paths; neither an everywhere path assumption nor an expected count bound
is added. Unit jumps and the existing local-IV theorem give the domain.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveCountingProcess

/-- The original almost-sure count, not a selected path version, has the
actual local-IV compensation domain in its genuine usual natural filtration. -/
theorem natural_usual_compensator_domain
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℝ≥0 → Ω → ℕ} (hN : IsNonexplosiveCountingProcess N P)
    (hMeas : ∀ t, Measurable (N t)) :
    let F := Filtration.natural N (fun t ↦ (hMeas t).stronglyMeasurable)
    let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ (N t ω : ℝ)
    Adapted (F.usualAugmentation P) C ∧ HasCadlagPaths C P.completion ∧
      HasLocallyIntegrableVariation C (F.usualAugmentation P) P.completion := by
  let F := Filtration.natural N (fun t ↦ (hMeas t).stronglyMeasurable)
  let G := F.usualAugmentation P
  let N' := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ N t ω
  have haRaw : Adapted F N :=
    (Filtration.stronglyAdapted_natural (fun t ↦ (hMeas t).stronglyMeasurable)).adapted
  have ha : Adapted G N' := fun t ↦ (haRaw t).mono (F.le_usualAugmentation P t) le_rfl
  have hN' : IsNonexplosiveCountingProcess N' P.completion :=
    ⟨fun t ↦ ((ha t).mono (G.le t) le_rfl).aemeasurable,
      hN.initial, hN.monotonePaths, hN.rightContinuousPaths, hN.unitJumps⟩
  exact ⟨ha.natCast_real, hN'.hasCadlagPaths_real,
    hN'.hasLocallyIntegrableVariation_real ha (F.usualAugmentation_isUsual P)⟩

end ProbabilityTheory.IsNonexplosiveCountingProcess

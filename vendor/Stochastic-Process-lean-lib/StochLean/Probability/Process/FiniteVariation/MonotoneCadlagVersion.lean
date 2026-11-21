/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Stieltjes
public import StochLean.Probability.Process.Path.Monotone

/-! # An everywhere-monotone cadlag version of an adapted process

The complement of the common cadlag-and-monotone event is null. The usual
initial completeness assumption makes that specific event measurable at time
zero, so resetting the source to zero there preserves adaptedness. Both path
properties then hold everywhere, and the original process is indistinguishable
from the constructed version.

This is an existence bridge for the existing Stieltjes-kernel domain, not a
new version selector. Initial values and expected total variation are not
restricted; any integrability properties can be transferred separately.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- Usual initial completeness upgrades common-AE cadlag and monotone paths
to an adapted version with both properties everywhere. Neither an initial
moment nor integrable total variation is required. -/
theorem Adapted.exists_cadlag_monotone_indistinguishable_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hm : HasMonotonePaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Adapted F Y ∧
      (∀ ω, IsCadlagPath (Y · ω) ∧ Monotone (Y · ω)) ∧ Indistinguishable X Y P := by
  classical
  let bad : Set Ω := {ω | ¬ (IsCadlagPath (X · ω) ∧ Monotone (X · ω))}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp (hc.and hm))
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have haY : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hpath (ω : Ω) : IsCadlagPath (Y · ω) ∧ Monotone (Y · ω) := by
    by_cases hω : ω ∈ bad
    · simp only [Y, if_pos hω]
      exact ⟨IsContinuousPath.isCadlagPath continuous_const, monotone_const⟩
    · simpa only [Y, if_neg hω] using
        (not_not.mp hω : IsCadlagPath (X · ω) ∧ Monotone (X · ω))
  refine ⟨Y, haY, hpath, ?_⟩
  filter_upwards [hc, hm] with ω hcω hmω t
  exact (if_neg (show ω ∉ bad from fun hω ↦ hω ⟨hcω, hmω⟩)).symm

end MeasureTheory

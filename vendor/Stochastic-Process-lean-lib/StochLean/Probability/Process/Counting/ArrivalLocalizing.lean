/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalStoppingInformation
public import Mathlib.Probability.Process.LocalProperty

/-! # The original arrivals form a positive native localizing sequence

The actual arrival sequence, without reindexing or replacing its infinite
tail, is a Mathlib localizing sequence in the raw natural count filtration.
Stopping-time measurability comes from the existing actual-history theorem;
monotonicity and divergence come from the original path guard.

Every lifetime is strictly positive on every path. Thus the native positive
lifetime indicator is genuinely one, rather than being silently omitted.
No finiteness, probability, usual-condition or finite-arrival assumption is
needed, and no new localizer selector is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- The original arrivals are a native localizing sequence in the actual
count's raw natural filtration and are strictly positive everywhere. -/
theorem isLocalizingSequence_natural_count
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) (P : Measure Ω) :
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    IsLocalizingSequence F Γ P ∧ ∀ n ω, (0 : WithTop ℝ≥0) < Γ n ω := by
  intro F
  refine ⟨?_, fun n ω ↦ (hΓ ω).positive n⟩
  exact
    { isStoppingTime := (isStoppingTime_and_measurable_history_natural_count hΓ hMeas).1
      tendsto_top := ae_of_all P fun ω ↦ (hΓ ω).tendsto_top
      mono := ae_of_all P fun ω ↦ (hΓ ω).monotone }

end ProbabilityTheory.IsNonexplosiveArrivalSequence

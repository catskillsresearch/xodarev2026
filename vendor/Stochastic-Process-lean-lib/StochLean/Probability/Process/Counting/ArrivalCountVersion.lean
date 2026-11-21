/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalVersion
public import StochLean.Probability.Process.Counting.ArrivalTimes
public import StochLean.Probability.Process.Equivalence

/-! # Everywhere-valid arrivals representing an actual counting process

The original hitting times of a nonexplosive counting process are valid
arrival data on one common almost-sure event and are actual stopping times.
The existing arrival-version theorem resets their common exceptional set
using initial completeness. Its everywhere-valid sequence therefore has
measurable coordinates and an adapted guarded count.

On the same common event, the original count and the guarded count have
exactly the same strict natural-number lower cuts at every time. They are
thus indistinguishable, not merely coordinatewise modifications. No new
arrival or count selector is defined, and no moment assumption is used.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveCountingProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ}

/-- An actual adapted nonexplosive count admits an everywhere-valid
arrival representative whose guarded count is indistinguishable from the
original process. All original hitting times agree on one common event. -/
theorem exists_arrivalSequence_count_version
    (hN : IsNonexplosiveCountingProcess N P) (ha : Adapted F N)
    (hF : F.IsUsual P) :
    ∃ Γ' : ℕ → Ω → WithTop ℝ≥0,
      ∃ hΓ' : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ' n ω),
        (∀ n, Measurable (Γ' n)) ∧
        Adapted F (fun t ω ↦ (hΓ' ω).count t) ∧
        Indistinguishable (fun t ω ↦ (hΓ' ω).count t) N P ∧
        (∀ᵐ ω ∂P, ∀ n, Γ' n ω = hittingAfter N (Ioi n) 0 ω) := by
  have hvalid : ∀ᵐ ω ∂P,
      IsNonexplosiveArrivalSequence (fun n ↦ hittingAfter N (Ioi n) 0 ω) :=
    hN.ae_hittingAfter_arrival_properties.mono fun _ hω ↦
      ⟨hω.1, hω.2.1, hω.2.2.2.1, hω.2.2.2.2⟩
  obtain ⟨Γ', hΓ', hstop, he⟩ :=
    exists_nonexplosiveArrivalSequence_version hF.complete_initial
      (hN.isStoppingTime_hittingAfter ha hF) hvalid
  refine ⟨Γ', hΓ', fun n ↦ (hstop n).measurable',
    (IsNonexplosiveArrivalSequence.adapted_count_iff hΓ' F).mpr hstop, ?_, he⟩
  filter_upwards [he, hN.ae_hittingAfter_le_iff] with ω heω hhitω t
  apply eq_of_forall_lt_iff
  intro n
  rw [(hΓ' ω).lt_count_iff, heω n]
  exact hhitω n t

end ProbabilityTheory.IsNonexplosiveCountingProcess

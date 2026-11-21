/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.JumpCoefficients
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps

/-!
# The stopping-time split underlying the Meyer--Feller theorem

Protter III.4 splits a positive stopping time `T` at the event where a
cadlag process jumps at `T`.  This file proves the filtration-theoretic core
of that statement for real processes:

* the finite stopped-jump event belongs to `F_T`;
* restricting `T` to that event and its complement gives stopping times;
* their pointwise minimum is exactly `T`;
* if the process has totally inaccessible positive-time jumps, the jump
  restriction is totally inaccessible;
* the finite complement restriction samples a zero jump.

This is not labelled as the full Meyer--Feller theorem.  The current Markov
library has a kernel-level Feller semigroup, but no continuous-time strong
Markov process structure connecting a process, its natural completed
filtration and that semigroup.  In particular, the genuinely Feller/strong
Markov implication that the zero-jump complement is predictable is not
available and is not introduced here as a hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

/-- Protter III.4's event `A = {T < ∞, X_T ≠ X_{T-}}`, expressed with the
project's explicitly zero-terminal stopped-jump convention. -/
noncomputable def stoppingJumpEvent (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) : Set Ω :=
  {ω | τ ω ≠ ⊤ ∧
    stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω ≠ 0}

@[simp]
theorem mem_stoppingJumpEvent_iff {X : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} :
    ω ∈ stoppingJumpEvent X τ ↔ τ ω ≠ ⊤ ∧
      stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω ≠ 0 :=
  Iff.rfl

/-- At a finite lifetime, `stoppingJumpEvent` is literally the source event
`X_T ≠ X_{T-}`. -/
theorem mem_stoppingJumpEvent_iff_exists {X : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} :
    ω ∈ stoppingJumpEvent X τ ↔
      ∃ t : ℝ≥0, τ ω = (t : WithTop ℝ≥0) ∧
        X t ω ≠ leftLimitProcess X t ω := by
  constructor
  · intro hA
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
      (mem_stoppingJumpEvent_iff.mp hA).1
    have hτt : τ ω = (t : WithTop ℝ≥0) := ht.symm
    refine ⟨t, hτt, ?_⟩
    have hjump := (mem_stoppingJumpEvent_iff.mp hA).2
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe hτt] at hjump
    simpa only [jumpProcess, Pi.sub_apply, sub_ne_zero] using hjump
  · rintro ⟨t, hτt, hjump⟩
    apply mem_stoppingJumpEvent_iff.mpr
    refine ⟨hτt ▸ WithTop.coe_ne_top, ?_⟩
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe hτt]
    simpa only [jumpProcess, Pi.sub_apply, sub_ne_zero] using hjump

/-- The two restrictions in the Meyer split reconstruct the original
stopping time pointwise, including samples where it is infinite. -/
theorem min_restrictedStoppingTime_stoppingJumpEvent_compl
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    (fun ω ↦ min
      (restrictedStoppingTime τ (stoppingJumpEvent X τ) ω)
      (restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ ω)) = τ :=
  min_restrictedStoppingTime_compl τ (stoppingJumpEvent X τ)

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- The finite stopped-jump event is measurable at the stopping time.  This
is the exact measurability input needed to form both restrictions in III.4. -/
theorem Adapted.measurableSet_stoppingJumpEvent (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hτ : IsStoppingTime F τ) :
    MeasurableSet[hτ.measurableSpace] (stoppingJumpEvent X τ) := by
  have hfinite : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    (hτ.measurable (measurableSet_singleton ⊤)).compl
  have hjump : MeasurableSet[hτ.measurableSpace]
      {ω | stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω ≠ 0} :=
    ((hX.stronglyMeasurable_stopped_jump hc hτ).measurable
      (measurableSet_singleton (0 : ℝ))).compl
  exact hfinite.inter hjump

/-- The jump branch of the Meyer split is a stopping time. -/
theorem Adapted.isStoppingTime_restricted_stoppingJumpEvent
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω))
    (hτ : IsStoppingTime F τ) :
    IsStoppingTime F (restrictedStoppingTime τ (stoppingJumpEvent X τ)) :=
  hτ.restrictedStoppingTime (hX.measurableSet_stoppingJumpEvent hc hτ)

/-- The zero-jump complement branch of the Meyer split is a stopping time. -/
theorem Adapted.isStoppingTime_restricted_stoppingJumpEvent_compl
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω))
    (hτ : IsStoppingTime F τ) :
    IsStoppingTime F (restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ) :=
  hτ.restrictedStoppingTime (hX.measurableSet_stoppingJumpEvent hc hτ).compl

/-- If every positive-time jump of `X` is totally inaccessible, then the
restriction of a positive stopping time to its nonzero-jump event is totally
inaccessible.  No classification of the complement is assumed. -/
theorem HasTotallyInaccessibleJumps.isTotallyInaccessibleStoppingTime_jumpPart
    (hJ : HasTotallyInaccessibleJumps F X P)
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω))
    (hτ : IsStoppingTime F τ) (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    IsTotallyInaccessibleStoppingTime F
      (restrictedStoppingTime τ (stoppingJumpEvent X τ)) P := by
  apply hJ.isTotallyInaccessibleStoppingTime_of_jump_graph
    (hX.isStoppingTime_restricted_stoppingJumpEvent hc hτ)
  filter_upwards [hpos] with ω hpositive hfinite
  obtain ⟨hA, hτfinite⟩ :=
    (restrictedStoppingTime_ne_top_iff τ (stoppingJumpEvent X τ) ω).mp hfinite
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτfinite
  have hτt : τ ω = (t : WithTop ℝ≥0) := ht.symm
  have htpos : 0 < t := WithTop.coe_lt_coe.mp (hτt ▸ hpositive)
  have hjump := (mem_stoppingJumpEvent_iff.mp hA).2
  rw [stoppedValueWithTerminal_jump_eq_of_eq_coe hτt] at hjump
  exact ⟨t, htpos,
    (restrictedStoppingTime_of_mem τ hA).trans hτt, hjump⟩

/-- On the finite complement branch of the Meyer split, the original process
has zero jump at the selected positive time.  This isolates the remaining
Meyer--Feller bridge: proving that this branch is predictable. -/
theorem ae_complementPart_samples_zero_jump
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    ∀ᵐ ω ∂P, restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ ω ≠ ⊤ →
      ∃ t : ℝ≥0, 0 < t ∧
        restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ ω =
          (t : WithTop ℝ≥0) ∧ jumpProcess X t ω = 0 := by
  filter_upwards [hpos] with ω hpositive hfinite
  obtain ⟨hAc, hτfinite⟩ :=
    (restrictedStoppingTime_ne_top_iff τ (stoppingJumpEvent X τ)ᶜ ω).mp hfinite
  have hnotA : ω ∉ stoppingJumpEvent X τ := by
    simpa only [mem_compl_iff] using hAc
  have hzero :
      stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω = 0 := by
    by_contra hne
    exact hnotA (mem_stoppingJumpEvent_iff.mpr ⟨hτfinite, hne⟩)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτfinite
  have hτt : τ ω = (t : WithTop ℝ≥0) := ht.symm
  have htpos : 0 < t := WithTop.coe_lt_coe.mp (hτt ▸ hpositive)
  rw [stoppedValueWithTerminal_jump_eq_of_eq_coe hτt] at hzero
  exact ⟨t, htpos,
    (restrictedStoppingTime_of_mem τ hAc).trans hτt, hzero⟩

/-- The complete filtration-theoretic core of the Meyer split currently
derivable from the project APIs.  The absent full III.4 conclusion is precisely
`IsPredictableStoppingTime` for the second restriction under the source's
strong-Markov/Feller hypotheses. -/
theorem meyerFeller_jumpSplit_core
    (hJ : HasTotallyInaccessibleJumps F X P)
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω))
    (hτ : IsStoppingTime F τ) (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    IsStoppingTime F (restrictedStoppingTime τ (stoppingJumpEvent X τ)) ∧
      IsStoppingTime F (restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ) ∧
      (fun ω ↦ min
        (restrictedStoppingTime τ (stoppingJumpEvent X τ) ω)
        (restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ ω)) = τ ∧
      IsTotallyInaccessibleStoppingTime F
        (restrictedStoppingTime τ (stoppingJumpEvent X τ)) P ∧
      (∀ᵐ ω ∂P, restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ ω ≠ ⊤ →
        ∃ t : ℝ≥0, 0 < t ∧
          restrictedStoppingTime τ (stoppingJumpEvent X τ)ᶜ ω =
            (t : WithTop ℝ≥0) ∧ jumpProcess X t ω = 0) := by
  exact ⟨hX.isStoppingTime_restricted_stoppingJumpEvent hc hτ,
    hX.isStoppingTime_restricted_stoppingJumpEvent_compl hc hτ,
    min_restrictedStoppingTime_stoppingJumpEvent_compl X τ,
    HasTotallyInaccessibleJumps.isTotallyInaccessibleStoppingTime_jumpPart
      hJ hX hc hτ hpos,
    ae_complementPart_samples_zero_jump hpos⟩

end MeasureTheory

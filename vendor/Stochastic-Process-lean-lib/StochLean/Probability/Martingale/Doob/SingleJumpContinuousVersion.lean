/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJumpContinuous

/-! # An everywhere continuous increasing version of the single-jump compensator

The existing totally inaccessible single-jump construction supplies the
actual compensator. Resetting its exceptional nonmonotone paths on an
initial measurable null event gives a version suitable for actual Stieltjes
kernels. The unit-jump process is unchanged, and its difference with this
version remains a true martingale. Infinite lifetimes are allowed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

/-- An actual unit jump at a totally inaccessible lifetime has a compensator
whose paths are all continuous and increasing, not merely almost surely so. -/
theorem IsTotallyInaccessibleStoppingTime.exists_continuous_monotone_compensator_one
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P) :
    ∃ B : ℝ≥0 → Ω → ℝ, Adapted F B ∧
      (∀ ω, Continuous (B · ω)) ∧ (∀ ω, Monotone (B · ω)) ∧ B 0 = 0 ∧
      (∀ t, Integrable (B t) P) ∧
      Martingale ((fun t : ℝ≥0 ↦
        {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ))) - B) F P := by
  classical
  obtain ⟨A, _, _, haA, _, hcA, hA0, hmA, _, hDA, _, _, _, _, _, hM, _⟩ :=
    hτ.exists_continuous_compensator_neg (C := fun _ ↦ (1 : ℝ)) hF
      stronglyMeasurable_const (integrable_const 1) (ae_of_all _ fun _ ↦ zero_le_one)
  let bad := {ω | ¬ Monotone (A · ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hmA)
  let B : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else A t ω
  have haB : Adapted F B := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (haA t)
  have hcB (ω : Ω) : Continuous (B · ω) := by
    by_cases hω : ω ∈ bad
    · simp only [B, if_pos hω]
      exact continuous_const
    · simpa only [B, if_neg hω] using hcA ω
  have hmB (ω : Ω) : Monotone (B · ω) := by
    by_cases hω : ω ∈ bad
    · simp only [B, if_pos hω]
      exact monotone_const
    · simpa only [B, if_neg hω] using (not_not.mp hω : Monotone (A · ω))
  have hB0 : B 0 = 0 := by
    funext ω
    by_cases hω : ω ∈ bad <;> simp only [B, hω, if_true, if_false, hA0, Pi.zero_apply]
  have heAB : Indistinguishable A B P := by
    filter_upwards [hmA] with ω hω t
    exact (if_neg (show ω ∉ bad from fun h ↦ h hω)).symm
  have hiB (t : ℝ≥0) : Integrable (B t) P :=
    (hDA.integrable t).congr (heAB.ae_eq t)
  let N : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ))
  have haN : StronglyAdapted F N := fun t ↦ stronglyMeasurable_const.indicator (hτ.1 t)
  refine ⟨B, haB, hcB, hmB, hB0, hiB, ?_⟩
  apply hM.neg.congr (haN.sub haB.stronglyAdapted)
  intro t
  filter_upwards [heAB] with ω hω
  change -({ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ -(1 : ℝ)) ω + A t ω) =
    N t ω - B t ω
  rw [← hω t]
  by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
  · simp only [N, indicator_apply, mem_ofPred_eq, if_pos ht]
    ring
  · simp only [N, indicator_apply, mem_ofPred_eq, if_neg ht, zero_add, zero_sub]

end ProbabilityTheory

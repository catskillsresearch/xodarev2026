/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Restriction
public import StochLean.Probability.Process.Stopping.PredictableProcess
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Predictable activation after a stopping time

Information measurable at a stopping time is predictably available strictly
after that time. This follows from the existing strict-future theorem applied
to the original stopping time restricted to the event in question.

Consequently a Borel function of a stopped-field mark and the elapsed time is
predictable when its value at elapsed time zero vanishes. The theorem uses
closed activation, retaining the stopping endpoint, where the zero-value
hypothesis makes closed and strict activation agree. The auxiliary clock is
the actual finite clock `min t L`, so an infinite lifetime never activates
the process. No infinite-time value is assigned a mathematical meaning.

The mark is measurable at `L`, not at time zero. No measure, usual conditions,
finiteness or predictability of `L`, or standard Borel assumption on the mark
space is required. The arbitrary default mark is only used outside the
strict future and does not occur in the resulting process.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω K : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
  {F : Filtration ℝ≥0 mΩ} {L : Ω → WithTop ℝ≥0}

/-- An event in the actual stopped sigma field becomes predictably visible
strictly after its stopping time, without predictability of that time. -/
theorem IsStoppingTime.measurableSet_predictable_lt_mem (hL : IsStoppingTime F L)
    {E : Set Ω} (hE : MeasurableSet[hL.measurableSpace] E) :
    MeasurableSet[F.predictable]
      {p : ℝ≥0 × Ω | L p.2 < (p.1 : WithTop ℝ≥0) ∧ p.2 ∈ E} := by
  have hp := (hL.restrictedStoppingTime hE).measurableSet_predictable_lt
  convert hp using 1
  ext ⟨t, ω⟩
  change (L ω < (t : WithTop ℝ≥0) ∧ ω ∈ E) ↔
    ProbabilityTheory.restrictedStoppingTime L E ω < (t : WithTop ℝ≥0)
  by_cases hω : ω ∈ E
  · rw [restrictedStoppingTime_of_mem L hω]
    simp only [hω, and_true]
  · rw [restrictedStoppingTime_of_notMem L hω]
    simp only [hω, and_false, not_top_lt]

/-- A Borel function of an actual stopped-field mark and the elapsed time,
with zero value at elapsed time zero, has predictable closed activation.
The default mark has no effect on the stated process. -/
theorem Measurable.isStronglyPredictable_delayed_of_zero
    {Z : Ω → K} {f : K × ℝ≥0 → ℝ} (hf : Measurable f)
    (hL : IsStoppingTime F L) (hZ : Measurable[hL.measurableSpace] Z)
    (z₀ : K) (hf0 : ∀ z, f (z, 0) = 0) :
    IsStronglyPredictable F
      (fun t ω ↦ if L ω ≤ (t : WithTop ℝ≥0)
        then f (Z ω, t - (L ω).untopA) else 0) := by
  classical
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let R : ℝ≥0 × Ω → K :=
    fun p ↦ if L p.2 < (p.1 : WithTop ℝ≥0) then Z p.2 else z₀
  let age : ℝ≥0 × Ω → ℝ≥0 :=
    fun p ↦ p.1 - (min (p.1 : WithTop ℝ≥0) (L p.2)).untopA
  have hS := hL.measurableSet_predictable_lt
  have hR : Measurable R := by
    intro B hB
    have hmarked := hL.measurableSet_predictable_lt_mem (hZ hB)
    by_cases hz : z₀ ∈ B
    · have he : R ⁻¹' B =
          {p | L p.2 < (p.1 : WithTop ℝ≥0) ∧ Z p.2 ∈ B} ∪
            {p | L p.2 < (p.1 : WithTop ℝ≥0)}ᶜ := by
        ext p
        change (if L p.2 < (p.1 : WithTop ℝ≥0) then Z p.2 else z₀) ∈ B ↔
          (L p.2 < (p.1 : WithTop ℝ≥0) ∧ Z p.2 ∈ B) ∨
            ¬L p.2 < (p.1 : WithTop ℝ≥0)
        by_cases hp : L p.2 < (p.1 : WithTop ℝ≥0)
        · rw [if_pos hp]
          tauto
        · rw [if_neg hp]
          tauto
      rw [he]
      exact hmarked.union hS.compl
    · have he : R ⁻¹' B =
          {p | L p.2 < (p.1 : WithTop ℝ≥0) ∧ Z p.2 ∈ B} := by
        ext p
        change (if L p.2 < (p.1 : WithTop ℝ≥0) then Z p.2 else z₀) ∈ B ↔
          L p.2 < (p.1 : WithTop ℝ≥0) ∧ Z p.2 ∈ B
        by_cases hp : L p.2 < (p.1 : WithTop ℝ≥0)
        · rw [if_pos hp]
          tauto
        · rw [if_neg hp]
          tauto
      rw [he]
      exact hmarked
  have htime : Measurable (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := by
    apply measurable_of_Ioi
    intro t
    simpa only [prod_univ] using
      measurableSet_predictable_Ioi_prod (𝓕 := F) (i := t) MeasurableSet.univ
  have hclock : Measurable (fun p : ℝ≥0 × Ω ↦
      (min (p.1 : WithTop ℝ≥0) (L p.2)).untopA) :=
    htime.comp hL.measurable_predictable_stopping_pair
  have hage : Measurable age := htime.sub hclock
  have hmeas := (hf.comp (hR.prodMk hage)).stronglyMeasurable
  have he : (fun p : ℝ≥0 × Ω ↦ f (R p, age p)) =
      Function.uncurry (fun (t : ℝ≥0) ω ↦ if L ω ≤ (t : WithTop ℝ≥0)
        then f (Z ω, t - (L ω).untopA) else 0) := by
    funext ⟨t, ω⟩
    change f (R (t, ω), age (t, ω)) =
      if L ω ≤ (t : WithTop ℝ≥0) then f (Z ω, t - (L ω).untopA) else 0
    rcases lt_trichotomy (L ω) (t : WithTop ℝ≥0) with hlt | heq | hgt
    · simp only [R, age, if_pos hlt, if_pos hlt.le, min_eq_right hlt.le]
    · simp only [R, age, heq, lt_self_iff_false, if_false, min_self,
        WithTop.untopA, WithTop.untopD_coe, tsub_self, le_refl, if_true, hf0]
    · simp only [R, age, if_neg (not_lt_of_ge hgt.le), min_eq_left hgt.le,
        WithTop.untopA, WithTop.untopD_coe, tsub_self, hf0, if_neg (not_le_of_gt hgt)]
  change StronglyMeasurable (Function.uncurry _)
  rw [← he]
  exact hmeas

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.RealIndependentIncrements
public import StochLean.Probability.Process.Poisson.Completion
public import StochLean.Probability.Process.Poisson.TotallyInaccessibleJumps
public import StochLean.Probability.Process.IndependentIncrements.NaturalFiltration
public import StochLean.Probability.Process.Filtration.NaturalNatCast
public import StochLean.Probability.Process.Filtration.IndependentIncrementsAugmentation

/-! # Poisson jumps in the genuine usual natural filtration

Native joint independent increments imply independence of future real
increments from the whole original natural past. The actual natural
filtrations of the count and its real cast agree, using measurable casting
and the exact measurable floor inverse on natural values.

Genuine completion preserves the same process and all its increment laws.
Right continuity transfers the proved past independence to the genuine
usual augmentation. Thus the original Poisson jumps and original hitting
arrivals are totally inaccessible there, without an independent-past
certificate, a supplied usual filtration, or a new process realization.

Coordinate measurability is explicit because the raw natural filtration
is formed from the original process. No positive-rate or finite-arrival
assumption is made. These statements do not concern arbitrary enlarged
filtrations or general Levy/Feller process realization.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

/-- Actual future real count increments are independent of the entire
original count-generated natural past, by joint independent increments. -/
theorem indep_increment_natural (hN : IsPoissonProcess N rate P)
    (hNm : ∀ u, Measurable (N u)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (Filtration.natural N (fun u ↦ (hNm u).stronglyMeasurable) s)
      (MeasurableSpace.comap (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P := by
  have hRm : ∀ u, Measurable (fun ω ↦ (N u ω : ℝ)) := fun u ↦
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (hNm u)
  have hR0 : (fun ω ↦ (N 0 ω : ℝ)) =ᵐ[P] 0 := by
    filter_upwards [hN.initial] with ω hω
    change (N 0 ω : ℝ) = 0
    rw [hω, Nat.cast_zero]
  have hi := hN.hasIndepIncrements_real.indep_increment_natural hRm hR0 hst
  rw [Filtration.natural_natCast_real_eq N hNm] at hi
  exact hi

/-- The derived whole-past independence survives actual completion and
right continuation, for the original process and original natural filtration. -/
theorem indep_increment_natural_usualAugmentation (hN : IsPoissonProcess N rate P)
    (hNm : ∀ u, Measurable (N u)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep
      ((Filtration.natural N (fun u ↦ (hNm u).stronglyMeasurable)).usualAugmentation P s)
      (MeasurableSpace.comap
        (fun ω : NullMeasurableSpace Ω P ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance)
      P.completion := by
  have ha := (Filtration.stronglyAdapted_natural
    (fun u ↦ (hNm u).stronglyMeasurable)).adapted
  exact hN.hasCadlagPaths_real.hasRightContinuousPaths.indep_increment_usualAugmentation
    ha.natCast_real (fun _ _ huv ↦ hN.indep_increment_natural hNm huv) hst

/-- The actual Poisson process has totally inaccessible positive-time
jumps in its genuine usual natural filtration. Past independence and
usualness are constructed, not additional hypotheses. -/
theorem hasTotallyInaccessibleJumps_real_natural_usualAugmentation
    (hN : IsPoissonProcess N rate P) (hNm : ∀ u, Measurable (N u)) :
    HasTotallyInaccessibleJumps
      ((Filtration.natural N (fun u ↦ (hNm u).stronglyMeasurable)).usualAugmentation P)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ (N t ω : ℝ)) P.completion := by
  let F := Filtration.natural N (fun u ↦ (hNm u).stronglyMeasurable)
  have ha : Adapted F N := (Filtration.stronglyAdapted_natural _).adapted
  exact hN.completion.hasTotallyInaccessibleJumps_real_of_indep_past
    (F.usualAugmentation_isUsual P) (ha.usualAugmentation P)
    (fun _ _ hst ↦ hN.indep_increment_natural_usualAugmentation hNm hst)

/-- Each original hitting arrival is totally inaccessible in the genuine
usual natural filtration, including rate zero and possibly infinite arrivals. -/
theorem isTotallyInaccessibleStoppingTime_hittingAfter_natural_usualAugmentation
    (hN : IsPoissonProcess N rate P) (hNm : ∀ u, Measurable (N u)) (n : ℕ) :
    IsTotallyInaccessibleStoppingTime
      ((Filtration.natural N (fun u ↦ (hNm u).stronglyMeasurable)).usualAugmentation P)
      (fun ω : NullMeasurableSpace Ω P ↦ hittingAfter N (Ioi n) 0 ω) P.completion := by
  let F := Filtration.natural N (fun u ↦ (hNm u).stronglyMeasurable)
  have ha : Adapted F N := (Filtration.stronglyAdapted_natural _).adapted
  exact hN.completion.isTotallyInaccessibleStoppingTime_hittingAfter_of_indep_past
    (F.usualAugmentation_isUsual P) (ha.usualAugmentation P)
    (fun _ _ hst ↦ hN.indep_increment_natural_usualAugmentation hNm hst) n

end ProbabilityTheory.IsPoissonProcess

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CauseSpecificHazardBalance
public import StochLean.Probability.Process.Counting.MarkedSingleJumpInformation
public import StochLean.Probability.Process.Stopping.PredictableProcess
public import Mathlib.Probability.Martingale.Basic

/-! # The true compensated martingale for a marked single jump

The observations are the actual pair of closed counts for a measurable mark
and its complement. The observation law is the pushforward of the original
lifetime, and its actual cause submeasure is the pushforward restricted to
the mark. No independence of the mark and lifetime is imposed.

The original stopped cause hazard is predictable because its deterministic
time path is Borel and the original lifetime is a stopping time for this
pair's natural filtration. Its true coordinate L1 and survival increment
balance pull back from the actual observation law, without an injectivity
assumption. The marked count increment has exactly the matching cause mass.

Before the lifetime, each natural-information event has either empty or full
trace on survival; after the lifetime the actual compensated increment is
zero. These facts prove every conditional testing identity and hence the
true martingale property. The mark is never assumed initially measurable.

Zero and infinite lifetimes are retained. The initial marked count may be
nonzero, and no global uniform-integrability or compensator selection result
is inferred here. The martingale requires only a finite original measure;
predictability alone does not require even that finiteness assumption.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {B : Set Ω}

open Classical in
/-- The original stopped cause hazard is predictable in the actual marked
pair's natural filtration, without initially revealing the mark. -/
theorem isStronglyPredictable_stopped_causeSpecificHazard_marked
    (hτ : Measurable τ) (hB : MeasurableSet B) :
    let F := Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)
    IsStronglyPredictable F (stoppedProcess
      (fun r (_ : Ω) ↦ (eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ) r).toReal)
      τ) := by
  classical
  intro F
  have hstop : IsStoppingTime F τ := isStoppingTime_natural_markedSingleJumpCount hτ hB
  have htime : Measurable[F.predictable] (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := by
    apply measurable_of_Ioi
    intro s
    simpa only [prod_univ] using
      measurableSet_predictable_Ioi_prod (𝓕 := F) (i := s) MeasurableSet.univ
  have hdet : IsStronglyPredictable F (fun r (_ : Ω) ↦
      (eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ) r).toReal) :=
    ((measurable_eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ)).ennreal_toReal.comp
      htime).stronglyMeasurable
  exact hdet.stoppedProcess hstop

open Classical in
/-- The actual marked closed count minus its stopped cause hazard is a
true martingale for the original pair's natural filtration and finite measure. -/
theorem martingale_markedSingleJump_sub_causeSpecificHazard [IsFiniteMeasure P]
    (hτ : Measurable τ) (hB : MeasurableSet B) :
    let F := Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)
    let μ := P.map τ
    let ρ := (P.restrict B).map τ
    let A := stoppedProcess (fun r (_ : Ω) ↦ (eCauseSpecificHazard μ ρ r).toReal) τ
    Martingale (fun (t : ℝ≥0) ω ↦
      (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0) - A t ω) F P := by
  classical
  intro F μ ρ A
  let N : ℝ≥0 → Ω → ℕ × ℕ := fun t ω ↦
    (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then 1 else 0,
     if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then 1 else 0)
  let C : ℝ≥0 → Ω → ℝ := fun t ω ↦
    if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then 1 else 0
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ C t ω - A t ω
  let a := stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id
  have hρ : ρ ≤ μ := Measure.map_mono Measure.restrict_le_self hτ
  have hmC (t : ℝ≥0) : StronglyMeasurable[F t] (C t) := by
    have hN : StronglyAdapted F N :=
      Filtration.stronglyAdapted_natural (stronglyMeasurable_markedSingleJumpCount hτ hB)
    have hcast : Measurable[F t] (fun ω ↦ ((N t ω).1 : ℝ)) :=
      (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (hN t).measurable.fst
    convert hcast.stronglyMeasurable using 1
    funext ω
    by_cases hω : τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B
    · simp only [C, N, if_pos hω, Nat.cast_one]
    · simp only [C, N, if_neg hω, Nat.cast_zero]
  have hpA : IsStronglyPredictable F A :=
    isStronglyPredictable_stopped_causeSpecificHazard_marked (P := P) hτ hB
  have hm : StronglyAdapted F M := fun t ↦ (hmC t).sub (hpA.stronglyAdapted t)
  have hiC (t : ℝ≥0) : Integrable (C t) P := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hmC t).mono (F.le t)).aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    change ‖if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0‖ ≤ 1
    by_cases hω : τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B
    · simp only [if_pos hω, norm_one, le_refl]
    · simp only [if_neg hω, norm_zero, zero_le_one]
  have hia (t : ℝ≥0) : Integrable (a t) μ :=
    (integrable_stoppedProcess_eCauseSpecificHazard μ ρ hρ t).1
  have hiA (t : ℝ≥0) : Integrable (A t) P := (hia t).comp_measurable hτ
  have hiM (t : ℝ≥0) : Integrable (M t) P := (hiC t).sub (hiA t)
  change Martingale M F P
  refine ⟨hm, fun s t hst ↦ ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hiM t)
    (fun _ _ _ ↦ (hiM s).integrableOn) ?_ (hm s).aestronglyMeasurable
  intro E hE _
  let G : Set Ω := τ ⁻¹' Ioi (s : WithTop ℝ≥0)
  have hG : MeasurableSet G := hτ measurableSet_Ioi
  have hstopped (ω : Ω) (hω : τ ω ≤ (s : WithTop ℝ≥0)) : M t ω = M s ω := by
    have ht : τ ω ≤ (t : WithTop ℝ≥0) := hω.trans (WithTop.coe_le_coe.mpr hst)
    dsimp only [M, C, A]
    rw [stoppedProcess_eq_of_ge ht, stoppedProcess_eq_of_ge hω]
    simp only [ht, hω, true_and]
  have hcount : (∫ ω in G, C t ω - C s ω ∂P) =
      ρ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
    let Q : Set Ω := τ ⁻¹' Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ∩ B
    have hQ : MeasurableSet Q := (hτ measurableSet_Ioc).inter hB
    have hQG : Q ⊆ G := fun _ hω ↦ hω.1.1
    have he : (fun ω ↦ C t ω - C s ω) = Q.indicator (fun _ ↦ (1 : ℝ)) := by
      funext ω
      by_cases hv : τ ω ≤ (s : WithTop ℝ≥0)
      · have ht : τ ω ≤ (t : WithTop ℝ≥0) := hv.trans (WithTop.coe_le_coe.mpr hst)
        simp only [C, Q, indicator_apply, mem_inter_iff, mem_preimage, mem_Ioc,
          hv, ht, not_lt_of_ge hv, true_and, false_and, ite_false, sub_self]
      · have hs : (s : WithTop ℝ≥0) < τ ω := lt_of_not_ge hv
        simp only [C, Q, indicator_apply, mem_inter_iff, mem_preimage, mem_Ioc,
          hv, hs, true_and, false_and, ite_false, sub_zero]
    rw [he, setIntegral_indicator hQ, inter_eq_right.mpr hQG,
      setIntegral_const, smul_eq_mul, mul_one]
    change P.real Q = ((P.restrict B).map τ).real
      (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))
    rw [map_measureReal_apply hτ measurableSet_Ioc,
      measureReal_restrict_apply (hτ measurableSet_Ioc)]
  have hhazard : (∫ ω in G, A t ω - A s ω ∂P) =
      ρ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
    calc
      (∫ ω in G, A t ω - A s ω ∂P) =
          ∫ v in Ioi (s : WithTop ℝ≥0), a t v - a s v ∂μ :=
        (setIntegral_map measurableSet_Ioi ((hia t).sub (hia s)).aestronglyMeasurable
          hτ.aemeasurable).symm
      _ = _ := setIntegral_stoppedProcess_eCauseSpecificHazard_toReal_sub μ ρ hρ hst
  have hsurv : (∫ ω in G, M t ω - M s ω ∂P) = 0 := by
    calc
      (∫ ω in G, M t ω - M s ω ∂P) =
          ∫ ω in G, (C t ω - C s ω) - (A t ω - A s ω) ∂P := by
        apply setIntegral_congr_fun hG
        intro ω _
        dsimp only [M]
        ring
      _ = (∫ ω in G, C t ω - C s ω ∂P) - ∫ ω in G, A t ω - A s ω ∂P :=
        integral_sub ((hiC t).sub (hiC s)).integrableOn ((hiA t).sub (hiA s)).integrableOn
      _ = 0 := by rw [hcount, hhazard, sub_self]
  have htrace : E ∩ G = ∅ ∨ E ∩ G = G :=
    measurableSet_natural_markedSingleJumpCount_on_survival hτ hB s hE
  have he : E.indicator (fun ω ↦ M t ω - M s ω) =
      (E ∩ G).indicator (fun ω ↦ M t ω - M s ω) := by
    funext ω
    by_cases hω : ω ∈ G
    · by_cases hωE : ω ∈ E
      · simp only [indicator_apply, mem_inter_iff, hω, hωE, and_self, ite_true]
      · simp only [indicator_apply, mem_inter_iff, hω, hωE, false_and, ite_false]
    · have hzero : M t ω - M s ω = 0 := by
        rw [hstopped ω (le_of_not_gt hω), sub_self]
      simp only [indicator_apply, mem_inter_iff, hω, and_false, hzero, ite_self]
  have hinc : (∫ ω in E, M t ω - M s ω ∂P) = 0 := by
    rw [← integral_indicator (F.le s E hE), he]
    rcases htrace with htrace | htrace
    · rw [htrace, indicator_empty, integral_zero]
    · rw [htrace, integral_indicator hG]
      exact hsurv
  rw [integral_sub (hiM t).integrableOn (hiM s).integrableOn] at hinc
  exact (sub_eq_zero.mp hinc).symm

end ProbabilityTheory

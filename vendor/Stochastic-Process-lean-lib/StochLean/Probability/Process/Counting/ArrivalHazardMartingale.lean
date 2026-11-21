/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalGapClock
public import StochLean.Probability.Process.Counting.ArrivalInformation
public import StochLean.Probability.Process.Counting.ArrivalStoppingInformation
public import StochLean.Probability.Process.Counting.ConditionalHazardClock

/-! # The actual conditional hazard of one arrival stage

For an everywhere valid nonexplosive arrival sequence, the closed count of
one indexed arrival minus its actual delayed conditional-gap hazard is a
true uniformly integrable martingale in the raw natural filtration of the
original count. The history consists precisely of the earlier arrivals.

The history is measurable at the previous arrival, not initially. This
gives predictability of the original delayed hazard and hence adaptedness.
The actual safe elapsed-time identities give global uniform integrability
from the conditional-kernel clock theorem. To prove the martingale identity,
a natural event is represented by a history event only before the indexed
arrival; after that arrival the actual process has already stopped. The
remaining testing integral is exactly the previously proved conditional-gap
clock increment integral. No martingale or conditional-mean certificate is
assumed for the stage.

The original guarded count, absorbing interarrival durations, conditional
distribution, hazard and stopped process are retained. Stage zero has empty
history and starts at zero. Infinite earlier arrivals never activate a
stage, and the next arrival may itself be infinite. No new process or
compensator selector is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem standardBorel_arrivalHazard : StandardBorelSpace (WithTop ℝ≥0) :=
  inferInstanceAs (StandardBorelSpace ℝ≥0∞)

attribute [local instance] standardBorel_arrivalHazard

namespace IsNonexplosiveArrivalSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- Each actual arrival stage has a true globally uniformly integrable
compensated count in the original count's raw natural filtration. -/
theorem martingale_uniformIntegrable_arrival_sub_conditional_hazard
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) (n : ℕ) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    let H : Ω → Fin n → WithTop ℝ≥0 := fun ω i ↦ Γ i ω
    let L : Ω → WithTop ℝ≥0 :=
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let S : Ω → WithTop ℝ≥0 := fun ω ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
    let κ := condDistrib S H P
    let D : ℝ≥0 → Ω → ℝ := stoppedProcess
      (fun (s : ℝ≥0) (ω : Ω) ↦ if L ω ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (H ω)) (s - (L ω).untopA)).toReal else 0) (Γ n)
    let M : ℝ≥0 → Ω → ℝ := fun t ω ↦
      (if Γ n ω ≤ (t : WithTop ℝ≥0) then 1 else 0) - D t ω
    Martingale M F P ∧ UniformIntegrable M 1 P := by
  classical
  let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
    (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
  let H : Ω → Fin n → WithTop ℝ≥0 := fun ω i ↦ Γ i ω
  let L : Ω → WithTop ℝ≥0 :=
    Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
  let S : Ω → WithTop ℝ≥0 := fun ω ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
  let κ := condDistrib S H P
  let D : ℝ≥0 → Ω → ℝ := stoppedProcess
    (fun (s : ℝ≥0) (ω : Ω) ↦ if L ω ≤ (s : WithTop ℝ≥0)
      then (eCumulativeHazard (κ (H ω)) (s - (L ω).untopA)).toReal else 0) (Γ n)
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦
    (if Γ n ω ≤ (t : WithTop ℝ≥0) then 1 else 0) - D t ω
  change Martingale M F P ∧ UniformIntegrable M 1 P
  have hH : Measurable H := measurable_pi_lambda _ (fun i ↦ hMeas i)
  have hS : Measurable S := measurable_arrivalInterarrival hMeas n
  let ℓ : (Fin n → WithTop ℝ≥0) → WithTop ℝ≥0 :=
    Nat.casesOn (motive := fun k ↦ (Fin k → WithTop ℝ≥0) → WithTop ℝ≥0) n
      (fun _ ↦ 0) (fun k h ↦ h (Fin.last k))
  have hℓ : Measurable ℓ := by
    cases n with
    | zero => exact measurable_const
    | succ k => exact measurable_pi_apply (Fin.last k)
  have hℓH (ω : Ω) : ℓ (H ω) = L ω := by
    cases n <;> rfl
  let q : ℝ≥0 → (Fin n → WithTop ℝ≥0) → ℝ≥0 :=
    fun t h ↦ t - (min (t : WithTop ℝ≥0) (ℓ h)).untopA
  obtain ⟨hqJoint, hqMono, hqBound⟩ :=
    measurable_monotone_bounded_elapsedTime_of_lifetime hℓ
  have hq (t : ℝ≥0) : Measurable (q t) :=
    hqJoint.comp (measurable_const.prodMk measurable_id)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦
    (if S ω ≤ (q t (H ω) : WithTop ℝ≥0) then 1 else 0) -
      stoppedProcess (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal)
        S (q t (H ω)) ω
  have hcount (t : ℝ≥0) (ω : Ω) :
      Γ n ω ≤ (t : WithTop ℝ≥0) ↔ S ω ≤ (q t (H ω) : WithTop ℝ≥0) := by
    have hLc : Nat.casesOn (motive := fun _ ↦ WithTop ℝ≥0) n 0
        (fun k ↦ Γ k ω) = L ω := by
      cases n <;> rfl
    simpa only [q, hℓH, S, hLc] using
      (hΓ ω).arrival_le_iff_interarrival_le_elapsedTime n t
  have hDclock (t : ℝ≥0) (ω : Ω) : D t ω =
      stoppedProcess (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal)
        S (q t (H ω)) ω := by
    simpa only [D, q, hℓH, L, S, stoppedProcess, id_eq] using
      stoppedProcess_delayed_eCumulativeHazard_eq_arrivalInterarrival κ H hΓ n t ω
  have hMclock (t : ℝ≥0) (ω : Ω) : M t ω = Y t ω := by
    simp only [M, Y, hcount, hDclock]
  have huY : UniformIntegrable Y 1 P :=
    uniformIntegrable_singleJump_sub_hazard_condDistrib_clock hH hS hq hqBound
  have huM : UniformIntegrable M 1 P :=
    huY.ae_eq (fun t ↦ ae_of_all _ fun ω ↦ (hMclock t ω).symm)
  have hiM (t : ℝ≥0) : Integrable (M t) P := memLp_one_iff_integrable.mp (huM.memLp t)
  obtain ⟨hstop, hHist⟩ := isStoppingTime_and_measurable_history_natural_count hΓ hMeas
  obtain ⟨hL, hHL⟩ := hHist n
  have hpD : IsStronglyPredictable F D :=
    isStronglyPredictable_stopped_delayed_eCumulativeHazard κ hL (hstop n) hHL
      (fun _ ↦ ⊤)
  have hm : StronglyAdapted F M := by
    intro t
    have hC : Measurable[F t]
        (fun ω ↦ if Γ n ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      Measurable.ite (hstop n t) measurable_const measurable_const
    exact hC.stronglyMeasurable.sub (hpD.stronglyAdapted t)
  refine ⟨⟨hm, fun s t hst ↦ ?_⟩, huM⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hiM t)
    (fun _ _ _ ↦ (hiM s).integrableOn) ?_ (hm s).aestronglyMeasurable
  intro E hE _
  obtain ⟨B, hB, htrace⟩ := measurableSet_natural_count_on_survival hΓ hMeas s n hE
  let V : Set Ω := {ω | H ω ∈ B ∧ (q s (H ω) : WithTop ℝ≥0) < S ω}
  have hV : MeasurableSet V := (hH hB).inter
    (measurableSet_lt (WithTop.continuous_coe.measurable.comp ((hq s).comp hH)) hS)
  have hsurv (ω : Ω) : (s : WithTop ℝ≥0) < Γ n ω ↔
      (q s (H ω) : WithTop ℝ≥0) < S ω := by
    rw [lt_iff_not_ge, lt_iff_not_ge, hcount]
  have hstopped (ω : Ω) (hs : Γ n ω ≤ (s : WithTop ℝ≥0)) : M t ω = M s ω := by
    have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
    dsimp only [M, D]
    rw [if_pos ht, if_pos hs, stoppedProcess_eq_of_ge ht, stoppedProcess_eq_of_ge hs]
  have hI : E.indicator (fun ω ↦ M t ω - M s ω) =
      V.indicator (fun ω ↦ Y t ω - Y s ω) := by
    funext ω
    by_cases hs : (s : WithTop ℝ≥0) < Γ n ω
    · have he : ω ∈ E ↔ H ω ∈ B := by
        have hh := Set.ext_iff.mp htrace ω
        change (ω ∈ E ∧ (s : WithTop ℝ≥0) < Γ n ω) ↔
          (H ω ∈ B ∧ (s : WithTop ℝ≥0) < Γ n ω) at hh
        simpa only [hs, and_true] using hh
      have hg := (hsurv ω).mp hs
      simp only [indicator_apply, V, mem_ofPred_eq, hg, and_true, he, hMclock]
    · have hn : ω ∉ V := fun h ↦ hs ((hsurv ω).mpr h.2)
      rw [Set.indicator_of_notMem hn]
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω, hstopped ω (le_of_not_gt hs), sub_self]
      · rw [Set.indicator_of_notMem hω]
  have hz : (∫ ω in V, Y t ω - Y s ω ∂P) = 0 :=
    setIntegral_singleJump_sub_hazard_condDistrib_clock_sub hH hS (hq s) (hq t)
      (fun h ↦ hqMono h hst) (hqBound t) hB
  have hdiff : (∫ ω in E, M t ω - M s ω ∂P) = 0 := by
    rw [← integral_indicator (F.le s E hE), hI, integral_indicator hV]
    exact hz
  rw [integral_sub (hiM t).integrableOn (hiM s).integrableOn] at hdiff
  exact (sub_eq_zero.mp hdiff).symm

end IsNonexplosiveArrivalSequence
end ProbabilityTheory

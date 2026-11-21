/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalWindowSequence
public import StochLean.Probability.Process.Stopping.ConditionalWindowSampling
public import StochLean.Probability.Process.Stopping.ThresholdHitting
public import StochLean.Probability.Process.Stopping.ShrinkingWindow
public import StochLean.Probability.Process.Path.Supremum

/-! # Uniform small-window estimates at totally inaccessible times

The first-threshold argument is restricted to the actual trigger event.
Conditional sampling controls its probability, and the predictable strict
limit excludes a collision with the totally inaccessible lifetime. All running
suprema use the existing countable dense owner.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
  {δ : ℕ → ℝ≥0} {R : ℕ → ℝ≥0 → Ω → ℝ}

theorem IsTotallyInaccessibleStoppingTime.tendsto_conditional_window_supremum_of_ordered
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hδ : Tendsto δ atTop (𝓝 0))
    (haR : ∀ n, StronglyAdapted F (R n))
    (hrR : ∀ n ω, IsRightContinuousPath (fun t ↦ R n t ω))
    (heR : ∀ n (t : ℝ≥0), R n t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ n : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (hsupport : ∀ n (t : ℝ≥0) ω, τ ω ≤ t → R n t ω = 0)
    (hmono : ∀ t ω, Antitone (fun n ↦ R n t ω))
    (ν : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R n) ν ω})
      atTop (𝓝 0) := by
  let : F.IsRightContinuous := hF.rightContinuous
  let H : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ hittingAfter (R n) (Ioi a) 0
  have hH (n) : IsStoppingTime F (H n) := by
    have ha : Adapted F (R n) := fun t ↦ (haR n t).measurable
    exact ha.isStoppingTime_hittingAfter_isOpen (hrR n) isOpen_Ioi 0
  let σ : ℕ → FiniteStoppingTime F := fun n ↦ FiniteStoppingTime.truncate (hH n) ν
  let E : ℕ → Set Ω := fun n ↦ {ω | H n ω ≤ (ν : WithTop ℝ≥0)}
  have hmH (ω) : Monotone (fun n ↦ H n ω) :=
    monotone_hittingAfter_Ioi_of_antitone hmono a 0 ω
  have hmσ (ω) : Monotone (fun n ↦ σ n ω) := by
    intro i j hij
    exact FiniteStoppingTime.truncate_mono_of_le (hH i) (hH j) (fun ω ↦ hmH ω hij) ν ω
  have hbσ (n ω) : σ n ω ≤ ν := FiniteStoppingTime.truncate_le (hH n) ν ω
  have hEσ (n) : MeasurableSet[(σ n).measurableSpace] (E n) :=
    FiniteStoppingTime.measurableSet_truncate_trigger (hH n) ν
  have hE : Antitone E := fun _ _ hij _ hω ↦ (hmH _ hij).trans hω
  have hEm (n) : MeasurableSet (E n) := (σ n).measurableSpace_le _ (hEσ n)
  have hstrict (n) : ∀ᵐ ω ∂P, ω ∈ E n → (σ n ω : WithTop ℝ≥0) < τ ω := by
    filter_upwards with ω hω
    exact FiniteStoppingTime.truncate_hittingAfter_Ioi_lt_of_trigger
      (hH n) (hrR n) ha (hsupport n) hω
  have hlim := hτ.tendsto_measureReal_shrinking_stopping_window hF hmσ hbσ hE hEm hstrict hδ
  let B : ℕ → Set Ω := fun n ↦ E n ∩ {ω | (σ n ω : WithTop ℝ≥0) < τ ω ∧
    τ ω ≤ ((σ n ω + δ n : ℝ≥0) : WithTop ℝ≥0)}
  have hbound (n) : a * P.real (E n) ≤ P.real (B n) := by
    apply conditional_window_threshold_measure_le hτ.1 hF (haR n)
      (Eventually.of_forall (hrR n)) (heR n) (σ n) (hbσ n) (hEσ n)
    filter_upwards with ω hω
    exact FiniteStoppingTime.le_process_truncate_hittingAfter_Ioi_of_trigger
      (hH n) (hrR n) hω
  have hEbound (n) : P.real (E n) ≤ P.real (B n) / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using hbound n
  have hsub (n) : {ω | ENNReal.ofReal a < denseRunningSupremum (R n) ν ω} ⊆ E n := by
    intro ω hω
    change ENNReal.ofReal a < ⨆ k, ENNReal.ofReal (R n (denseTimeUpTo ν k) ω) at hω
    obtain ⟨k, hk⟩ := lt_iSup_iff.mp hω
    have hh : a < R n (denseTimeUpTo ν k) ω :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mp hk
    exact (hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ denseTimeUpTo ν k from bot_le) hh).trans
      (WithTop.coe_le_coe.mpr (min_le_left ν (TopologicalSpace.denseSeq ℝ≥0 k)))
  have hBlim : Tendsto (fun n ↦ P.real (B n) / a) atTop (𝓝 0) := by
    simpa only [zero_div] using hlim.div_const a
  exact squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun n ↦ (measureReal_mono (hsub n)).trans (hEbound n)) hBlim

theorem IsTotallyInaccessibleStoppingTime.tendsto_conditional_window_supremum_seq
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hδmono : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0))
    (hrR : ∀ n, HasRightContinuousPaths (R n) P)
    (heR : ∀ n (t : ℝ≥0), R n t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ n : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (ν : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R n) ν ω})
      atTop (𝓝 0) := by
  obtain ⟨Q, haQ, hcQ, heQ, hbQ, hmQ⟩ :=
    hτ.1.exists_coherent_conditional_windows hF δ hδmono
  have hlim := hτ.tendsto_conditional_window_supremum_of_ordered hF hδ haQ
    (fun n ω ↦ (hcQ n ω).1) heQ (fun n t ω ↦ (hbQ ω n t).2.2)
    (fun t ω ↦ hmQ ω t) ν ha
  have heq (n) :
      P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R n) ν ω} =
        P.real {ω | ENNReal.ofReal a < denseRunningSupremum (Q n) ν ω} := by
    have hind := cadlag_conditional_window_unique (hrR n)
      (Eventually.of_forall fun ω ↦ (hcQ n ω).1) (heR n) (heQ n)
    apply measureReal_congr
    filter_upwards [hind] with ω hω
    have hs : denseRunningSupremum (R n) ν ω = denseRunningSupremum (Q n) ν ω := by
      unfold denseRunningSupremum
      congr 1
      funext k
      rw [hω (denseTimeUpTo ν k)]
    change (ENNReal.ofReal a < denseRunningSupremum (R n) ν ω) =
      (ENNReal.ofReal a < denseRunningSupremum (Q n) ν ω)
    rw [hs]
  exact hlim.congr' (Eventually.of_forall fun n ↦ (heq n).symm)

end ProbabilityTheory

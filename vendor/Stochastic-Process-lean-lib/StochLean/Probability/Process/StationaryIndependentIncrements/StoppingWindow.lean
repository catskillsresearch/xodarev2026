/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrements.FiniteFutureStopping
public import StochLean.Probability.Process.Path.ShrinkingSupremum

/-! # Actual running-supremum windows after finite stopping times

Every finite prefix of the canonical dense grid has the same joint future
increment law after a finite stopping time as at zero. Applying these laws
to finite-prefix exceedance events and then continuity from below identifies
the tail measures of the original countable running suprema.

The equality retains arbitrary real thresholds, including nonpositive ones.
For positive thresholds, right continuity at zero then gives vanishing tail
measures along any shrinking sequence of windows and any sequence of finite
stopping times. No usual-filtration hypothesis, normalized initial value,
left limits, or separately supplied random-time supremum law is used.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual dense running-supremum tail after any finite stopping time
equals the tail of the centered reference window at zero. -/
theorem HasStationaryIncrements.measure_denseRunningSupremum_norm_after_eq
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F)
    (δ : ℝ≥0) (ε : ℝ) :
    P {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X (τ ω + u) ω - X (τ ω) ω‖) δ ω} =
      P {ω | ENNReal.ofReal ε < denseRunningSupremum
        (fun u ω ↦ ‖X u ω - X 0 ω‖) δ ω} := by
  let E (n : ℕ) : Set Ω := {ω | ∃ i : Fin (n + 1),
    ENNReal.ofReal ε < ENNReal.ofReal
      ‖X (τ ω + denseTimeUpTo δ i) ω - X (τ ω) ω‖}
  let G (n : ℕ) : Set Ω := {ω | ∃ i : Fin (n + 1),
    ENNReal.ofReal ε < ENNReal.ofReal
      ‖X (denseTimeUpTo δ i) ω - X 0 ω‖}
  have hE : Monotone E := by
    intro n m hnm ω
    rintro ⟨i, hi⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hnm 1)⟩, hi⟩
  have hG : Monotone G := by
    intro n m hnm ω
    rintro ⟨i, hi⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hnm 1)⟩, hi⟩
  have hprefix (n : ℕ) : P (E n) = P (G n) := by
    have htest : MeasurableSet {v : Fin (n + 1) → ℝ |
        ∃ i, ENNReal.ofReal ε < ENNReal.ofReal ‖v i‖} := by
      simp only [ofPred_exists]
      exact MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const
        (ENNReal.measurable_ofReal.comp (measurable_pi_apply i).norm)
    exact (hs.identDistrib_finite_future_after ha hi hr τ
      (fun i : Fin (n + 1) ↦ denseTimeUpTo δ i)).measure_mem_eq htest
  have he : {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X (τ ω + u) ω - X (τ ω) ω‖) δ ω} = ⋃ n, E n := by
    ext ω
    simp only [mem_ofPred_eq, denseRunningSupremum, lt_iSup_iff, mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, ⟨n, Nat.lt_succ_self n⟩, hn⟩
    · rintro ⟨n, i, hi⟩
      exact ⟨i.val, hi⟩
  have hg : {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X u ω - X 0 ω‖) δ ω} = ⋃ n, G n := by
    ext ω
    simp only [mem_ofPred_eq, denseRunningSupremum, lt_iSup_iff, mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, ⟨n, Nat.lt_succ_self n⟩, hn⟩
    · rintro ⟨n, i, hi⟩
      exact ⟨i.val, hi⟩
  rw [he, hg, hE.measure_iUnion, hG.measure_iUnion]
  exact iSup_congr hprefix

/-- Shrinking windows after arbitrary finite stopping times have vanishing
positive-threshold running-supremum tail measures. The stopping times and
window lengths need not be monotone. -/
theorem HasStationaryIncrements.tendsto_measure_denseRunningSupremum_norm_after
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hr : HasRightContinuousPaths X P) (τ : ℕ → FiniteStoppingTime F)
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X (τ n ω + u) ω - X (τ n ω) ω‖) (δ n) ω})
      atTop (𝓝 0) := by
  have he : (fun n ↦ P {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X (τ n ω + u) ω - X (τ n ω) ω‖) (δ n) ω}) =
      (fun n ↦ P {ω | ENNReal.ofReal ε < denseRunningSupremum
        (fun u ω ↦ ‖X u ω - X 0 ω‖) (δ n) ω}) := by
    funext n
    exact hs.measure_denseRunningSupremum_norm_after_eq ha hi hr (τ n) (δ n) ε
  rw [he]
  exact hr.tendsto_measure_denseRunningSupremum_norm_sub_initial
    (fun _ ↦ ha.measurable) hδ hε

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightStep
public import StochLean.Probability.Process.Path.Subtraction
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! # Left-open lifetime-window indicators

The window indicator is the difference of the shifted and current revealed
indicators. It is right-continuous, including at zero and infinite lifetimes.
Joint measurability requires only measurability of the lifetime, not stopping.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (δ : ℝ≥0)

theorem indicator_lifetime_window_eq_sub (t : ℝ≥0) :
    {ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) =
      {ω | τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) -
        {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext ω
  have htt : (t : WithTop ℝ≥0) ≤ (t + δ : ℝ≥0) :=
    WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show 0 ≤ δ from bot_le))
  simp only [Pi.sub_apply, indicator_apply, mem_ofPred_eq]
  by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
  · simp only [ht, ht.trans htt, not_lt_of_ge ht, if_true, false_and, if_false, sub_self]
  · simp only [ht, lt_of_not_ge ht, if_false, true_and, sub_zero]

theorem isRightContinuousPath_indicator_lifetime_window (ω : Ω) :
    IsRightContinuousPath (fun t : ℝ≥0 ↦
      {ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) ω) := by
  simp only [indicator_lifetime_window_eq_sub, Pi.sub_apply]
  intro t
  have hc := (isCadlagPath_indicator_lifetime_le τ (fun _ ↦ (1 : ℝ)) ω).1
  have hadd : ContinuousWithinAt (fun s : ℝ≥0 ↦ s + δ) (Ici t) t :=
    (continuous_id.add continuous_const).continuousWithinAt
  exact ((hc (t + δ)).comp (f := fun s : ℝ≥0 ↦ s + δ) (x := t) hadd
    (fun s hs ↦ show t + δ ≤ s + δ from add_le_add (show t ≤ s from hs) le_rfl)).sub (hc t)

theorem measurable_indicator_lifetime_window {mΩ : MeasurableSpace Ω} (hτ : Measurable τ) :
    Measurable (fun p : ℝ≥0 × Ω ↦
      {ω | (p.1 : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((p.1 + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) p.2) := by
  classical
  have hm : MeasurableSet {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < τ p.2 ∧
      τ p.2 ≤ ((p.1 + δ : ℝ≥0) : WithTop ℝ≥0)} :=
    (measurableSet_lt (WithTop.measurable_coe.comp measurable_fst) (hτ.comp measurable_snd)).inter
      (measurableSet_le (hτ.comp measurable_snd)
        (WithTop.measurable_coe.comp (measurable_fst.add measurable_const)))
  simp only [indicator_apply, mem_ofPred_eq]
  exact Measurable.ite hm measurable_const measurable_const

end ProbabilityTheory

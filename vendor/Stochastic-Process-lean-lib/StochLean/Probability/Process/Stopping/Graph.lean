/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AfterCoefficient
public import StochLean.Probability.Process.Path.Step

/-! # Finite-time graphs of stopping times

Protter III.2 includes time zero in a stopping-time graph and excludes infinity.
The strict-future region is predictable, the closed-future region is optional,
and every stopping-time graph is optional. Predictability of the graph is not
asserted for an arbitrary stopping time.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

/-- The graph on finite time times sample space; it has no point at infinity. -/
def stoppingTimeGraph {Ω : Type*} (τ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {p | τ p.2 = (p.1 : WithTop ℝ≥0)}

@[simp] theorem mem_stoppingTimeGraph {Ω : Type*} {τ : Ω → WithTop ℝ≥0}
    {p : ℝ≥0 × Ω} : p ∈ stoppingTimeGraph τ ↔ τ p.2 = (p.1 : WithTop ℝ≥0) := Iff.rfl

@[simp] theorem stoppingTimeGraph_top {Ω : Type*} :
    stoppingTimeGraph (fun _ : Ω ↦ ⊤) = ∅ := by
  ext p
  simp only [mem_stoppingTimeGraph, WithTop.top_ne_coe, mem_empty_iff_false]

theorem stoppingTimeGraph_const {Ω : Type*} (t : ℝ≥0) :
    stoppingTimeGraph (fun _ : Ω ↦ (t : WithTop ℝ≥0)) = {t} ×ˢ univ := by
  ext p
  simp only [mem_stoppingTimeGraph, WithTop.coe_inj, mem_prod, mem_singleton_iff,
    mem_univ, and_true, eq_comm]

theorem snd_image_stoppingTimeGraph {Ω : Type*} (τ : Ω → WithTop ℝ≥0) :
    Prod.snd '' stoppingTimeGraph τ = {ω | τ ω ≠ ⊤} := by
  ext ω
  constructor
  · rintro ⟨⟨t, u⟩, htu, rfl⟩
    change τ u ≠ ⊤
    change τ u = (t : WithTop ℝ≥0) at htu
    rw [htu]
    exact WithTop.coe_ne_top
  · intro ht
    obtain ⟨t, he⟩ := WithTop.ne_top_iff_exists.mp ht
    exact ⟨(t, ω), he.symm, rfl⟩

end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem isStronglyPredictable_indicator_lt (hτ : IsStoppingTime F τ) :
    IsStronglyPredictable F (fun t : ℝ≥0 ↦ {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ))) := by
  classical
  have ha : Adapted F (fun t : ℝ≥0 ↦ {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ))) :=
    fun t ↦ measurable_const.indicator (hτ.measurableSet_lt t)
  apply ha.isStronglyPredictable_of_leftContinuous
  intro ω
  cases ht : τ ω with
  | top =>
    have he : (fun t : ℝ≥0 ↦ {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) ω) = 0 := by
      funext t
      simp only [Set.indicator_apply, mem_ofPred_eq, ht, not_top_lt, if_false, Pi.zero_apply]
    rw [he]
    exact fun _ ↦ continuousWithinAt_const
  | coe a =>
    simpa only [Set.indicator_apply, mem_ofPred_eq, ht, WithTop.coe_lt_coe] using
      (isCagladPath_step_Ioi a 1).1

theorem measurableSet_predictable_lt (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | τ p.2 < (p.1 : WithTop ℝ≥0)} := by
  have hm := hτ.isStronglyPredictable_indicator_lt.measurable (measurableSet_singleton (1 : ℝ))
  convert hm using 1
  ext ⟨t, ω⟩
  simp [Function.uncurry]

theorem measurableSet_optional_le (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.optional] {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} := by
  have hc : StronglyMeasurable[hτ.measurableSpace] (fun _ : Ω ↦ (1 : ℝ)) :=
    stronglyMeasurable_const
  have hm := (hc.isStronglyOptional_indicator_stoppingTime_le hτ).measurable
    (measurableSet_singleton (1 : ℝ))
  convert hm using 1
  ext ⟨t, ω⟩
  simp [Function.uncurry]

theorem measurableSet_optional_graph (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.optional] (stoppingTimeGraph τ) := by
  have he : stoppingTimeGraph τ = {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} ∩
      {p : ℝ≥0 × Ω | τ p.2 < (p.1 : WithTop ℝ≥0)}ᶜ := by
    ext p
    simp only [mem_stoppingTimeGraph, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    constructor
    · intro hp
      rw [hp]
      exact ⟨le_rfl, lt_irrefl _⟩
    · rintro ⟨hle, hlt⟩
      exact le_antisymm hle (le_of_not_gt hlt)
  rw [he]
  exact hτ.measurableSet_optional_le.inter
    (F.predictable_le_optional _ hτ.measurableSet_predictable_lt).compl

end MeasureTheory.IsStoppingTime

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.BeforeSigmaOrder
public import StochLean.Probability.Process.Stopping.TerminalValue
public import Mathlib.Probability.Process.Predictable

/-! # Predictable evaluation is measurable strictly before stopping

Protter III.8 for ordinary finite evaluation and for the existing terminal-valued
owner. The latter uses an explicitly supplied terminal variable measurable in
`⨆ t, F t`. The auxiliary clock `untopD 0` is only a measurable map; it is not
asserted to be a stopping time and never defines an implicit value at infinity.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {τ : Ω → WithTop ℝ≥0}

theorem IsStoppingTime.measurable_predictable_pair_untopD
    (hτ : IsStoppingTime F τ) :
    @Measurable Ω (ℝ≥0 × Ω) hτ.measurableSpaceBefore F.predictable
      (fun ω ↦ ((τ ω).untopD 0, ω)) := by
  let : MeasurableSpace Ω := hτ.measurableSpaceBefore
  change @Measurable Ω (ℝ≥0 × Ω) _ (MeasurableSpace.generateFrom _) _
  apply measurable_generateFrom
  rintro _ (⟨A, hA, rfl⟩ | ⟨t, A, hA, rfl⟩)
  · have hm := (hτ.le_measurableSpaceBefore _ hA).inter
      ((hτ.measurable_before.untopD 0) (measurableSet_singleton 0))
    convert hm using 1
    ext ω
    simp only [mem_preimage, mem_prod, mem_singleton_iff, NNReal.bot_eq_zero,
      mem_inter_iff, and_comm]
  · have htop : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω = ⊤} :=
      hτ.measurable_before (measurableSet_singleton _)
    have hm := (hτ.measurableSet_inter_gt_before t hA).inter htop.compl
    convert hm using 1
    ext ω
    change (t < (τ ω).untopD 0 ∧ ω ∈ A) ↔
      (ω ∈ A ∧ (t : WithTop ℝ≥0) < τ ω) ∧ ¬ τ ω = ⊤
    cases τ ω with
    | top => simp
    | coe s => simp only [WithTop.untopD_coe, WithTop.coe_lt_coe,
        WithTop.coe_ne_top, not_false_eq_true, true_and, and_comm]

theorem _root_.ProbabilityTheory.FiniteStoppingTime.measurable_predictable_pair
    (τ : FiniteStoppingTime F) :
    @Measurable Ω (ℝ≥0 × Ω) τ.isStoppingTime.measurableSpaceBefore F.predictable
      (fun ω ↦ (τ ω, ω)) :=
  τ.isStoppingTime.measurable_predictable_pair_untopD

variable [TopologicalSpace E]

/-- Protter III.8 at an everywhere finite stopping time, with no path regularity
or usualness hypothesis. -/
theorem IsStronglyPredictable.stronglyMeasurable_finiteStoppingTime_before
    {X : ℝ≥0 → Ω → E} (hX : IsStronglyPredictable F X) (τ : FiniteStoppingTime F) :
    StronglyMeasurable[τ.isStoppingTime.measurableSpaceBefore] (fun ω ↦ X (τ ω) ω) :=
  hX.comp_measurable τ.measurable_predictable_pair

theorem StronglyMeasurable.indicator_stoppingTime_eq_top_before [Zero E]
    {Z : Ω → E} (hZ : StronglyMeasurable[⨆ t, F t] Z) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpaceBefore] ({ω | τ ω = ⊤}.indicator Z) := by
  have htop : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω = ⊤} :=
    hτ.measurable_before (measurableSet_singleton _)
  have htop' := hτ.measurableSpaceBefore_le_iSup _ htop
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on htop' ?_
    (hZ.indicator htop') ?_
  · intro A hA
    have hm := hτ.measurableSet_inter_eq_top_before hA
    convert hm using 1
    ext ω
    simp only [mem_inter_iff]
    tauto
  · intro ω hω
    exact Set.indicator_of_notMem hω _

/-- Infinite stopping uses supplied terminal information. It does not evaluate
the process at a fabricated finite time. -/
theorem IsStronglyPredictable.stronglyMeasurable_stoppedValueWithTerminal_before [Zero E]
    {X : ℝ≥0 → Ω → E} {Z : Ω → E} (hX : IsStronglyPredictable F X)
    (hZ : StronglyMeasurable[⨆ t, F t] Z) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpaceBefore] (stoppedValueWithTerminal X Z τ) := by
  classical
  have htop : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω = ⊤} :=
    hτ.measurable_before (measurableSet_singleton _)
  have hfinite : StronglyMeasurable[hτ.measurableSpaceBefore]
      (fun ω ↦ X ((τ ω).untopD 0) ω) :=
    hX.comp_measurable hτ.measurable_predictable_pair_untopD
  have hm : StronglyMeasurable[hτ.measurableSpaceBefore]
      ({ω | τ ω = ⊤}.piecewise ({ω | τ ω = ⊤}.indicator Z)
        (fun ω ↦ X ((τ ω).untopD 0) ω)) :=
    (hZ.indicator_stoppingTime_eq_top_before hτ).piecewise htop hfinite
  convert hm using 1
  funext ω
  by_cases ht : τ ω = ⊤
  · simp [stoppedValueWithTerminal, Set.piecewise, ht]
  · obtain ⟨t, hte⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [stoppedValueWithTerminal_of_ne_top ht]
    simp only [Set.piecewise, mem_ofPred_eq, ht, if_false]
    change X ((τ ω).untopA) ω = X ((τ ω).untopD 0) ω
    rw [← hte]
    rfl

end MeasureTheory

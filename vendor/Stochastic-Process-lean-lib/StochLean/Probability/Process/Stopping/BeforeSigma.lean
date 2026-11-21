/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Finite

/-! # The sigma-field strictly before a stopping time

Protter III.2 defines `F_{T-}` using `F_0` and the events `A ∩ {t < T}`,
where `A ∈ F_t` and `t > 0`. We allow `t = 0` in the sole owner below and
prove that this gives exactly the same sigma-field. This is a subfield of
Mathlib's existing stopped sigma-field, not a replacement for it.

At infinite lifetime this field is `⨆ t, F t`, not necessarily `F_0` or
the ambient sigma-field. No process value at infinity is defined here.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {τ : Ω → WithTop ℝ≥0}

/-- The sigma-field of information strictly before `τ`, including initial information. -/
@[instance_reducible] protected def measurableSpaceBefore (_hτ : IsStoppingTime F τ) :
    MeasurableSpace Ω :=
  F 0 ⊔ MeasurableSpace.generateFrom
    {B | ∃ (t : ℝ≥0) (A : Set Ω),
      MeasurableSet[F t] A ∧ B = A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}}

theorem le_measurableSpaceBefore (hτ : IsStoppingTime F τ) :
    F 0 ≤ hτ.measurableSpaceBefore := le_sup_left

theorem measurableSet_inter_gt_before (hτ : IsStoppingTime F τ) (t : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[F t] A) :
    MeasurableSet[hτ.measurableSpaceBefore] (A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}) :=
  (show MeasurableSpace.generateFrom _ ≤ hτ.measurableSpaceBefore from le_sup_right) _
    (MeasurableSpace.measurableSet_generateFrom ⟨t, A, hA, rfl⟩)

/-- The zero-time generators are already initial information. -/
theorem measurableSpaceBefore_eq_generateFrom_positive (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore = F 0 ⊔ MeasurableSpace.generateFrom
      {B | ∃ (t : ℝ≥0) (A : Set Ω), 0 < t ∧
        MeasurableSet[F t] A ∧ B = A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}} := by
  apply le_antisymm
  · refine sup_le le_sup_left (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨t, A, hA, rfl⟩
    by_cases ht : t = 0
    · subst t
      exact (show F 0 ≤ F 0 ⊔ _ from le_sup_left) _ (hA.inter (hτ.measurableSet_gt 0))
    · exact (show MeasurableSpace.generateFrom _ ≤ F 0 ⊔ _ from le_sup_right) _
        (MeasurableSpace.measurableSet_generateFrom
        ⟨t, A, pos_iff_ne_zero.mpr ht, hA, rfl⟩)
  · refine sup_le hτ.le_measurableSpaceBefore (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨t, A, _, hA, rfl⟩
    exact hτ.measurableSet_inter_gt_before t hA

theorem measurableSpaceBefore_le (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore ≤ hτ.measurableSpace := by
  refine sup_le (hτ.le_measurableSpace_of_const_le fun _ ↦ bot_le)
    (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨t, A, hA, rfl⟩
  refine ⟨le_iSup F t _ (hA.inter (hτ.measurableSet_gt t)), fun u ↦ ?_⟩
  by_cases hut : u ≤ t
  · have he : (A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}) ∩ {ω | τ ω ≤ u} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hω hle
      exact (not_lt_of_ge (hle.trans (WithTop.coe_le_coe.mpr hut))) hω.2
    rw [he]
    exact @MeasurableSet.empty Ω (F u)
  · exact ((F.mono (le_of_not_ge hut) _ hA).inter
      (F.mono (le_of_not_ge hut) _ (hτ.measurableSet_gt t))).inter (hτ u)

theorem measurableSpaceBefore_le_iSup (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore ≤ ⨆ t, F t :=
  hτ.measurableSpaceBefore_le.trans hτ.measurableSpace_le'

theorem measurableSpaceBefore_le_ambient (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore ≤ mΩ :=
  hτ.measurableSpaceBefore_le.trans hτ.measurableSpace_le

theorem measurableSet_gt_before (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | (t : WithTop ℝ≥0) < τ ω} := by
  simpa only [univ_inter] using hτ.measurableSet_inter_gt_before t MeasurableSet.univ

theorem measurable_before (hτ : IsStoppingTime F τ) :
    Measurable[hτ.measurableSpaceBefore] τ := by
  apply measurable_of_Ioi
  intro t
  cases t with
  | top => simp
  | coe t => exact hτ.measurableSet_gt_before t

@[simp] theorem measurableSpaceBefore_const_zero (F : Filtration ℝ≥0 mΩ) :
    (isStoppingTime_const F 0).measurableSpaceBefore = F 0 := by
  apply le_antisymm
  · exact (isStoppingTime_const F 0).measurableSpaceBefore_le.trans
      (measurableSpace_const F 0).le
  · exact (isStoppingTime_const F 0).le_measurableSpaceBefore

theorem measurableSpaceBefore_const (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    (isStoppingTime_const F T).measurableSpaceBefore =
      F 0 ⊔ ⨆ (t : ℝ≥0) (_ : t < T), F t := by
  apply le_antisymm
  · refine sup_le le_sup_left (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨t, A, hA, rfl⟩
    by_cases ht : t < T
    · have hle : F t ≤ F 0 ⊔ ⨆ (t : ℝ≥0) (_ : t < T), F t :=
        (le_iSup_of_le t (le_iSup (fun _ : t < T ↦ F t) ht)).trans le_sup_right
      simpa only [WithTop.coe_lt_coe, ht, ofPred_true, inter_univ] using hle _ hA
    · simp only [WithTop.coe_lt_coe, ht, ofPred_false, inter_empty, MeasurableSet.empty]
  · refine sup_le (isStoppingTime_const F T).le_measurableSpaceBefore ?_
    refine iSup_le fun t ↦ iSup_le fun ht ↦ ?_
    intro A hA
    simpa only [WithTop.coe_lt_coe, ht, ofPred_true, inter_univ] using
      (isStoppingTime_const F T).measurableSet_inter_gt_before t hA

theorem measurableSpaceBefore_top (hτ : IsStoppingTime F (fun _ ↦ ⊤)) :
    hτ.measurableSpaceBefore = ⨆ t, F t := by
  apply le_antisymm hτ.measurableSpaceBefore_le_iSup
  refine iSup_le fun t A hA ↦ ?_
  simpa only [WithTop.coe_lt_top, ofPred_true, inter_univ] using
    hτ.measurableSet_inter_gt_before t hA

end MeasureTheory.IsStoppingTime

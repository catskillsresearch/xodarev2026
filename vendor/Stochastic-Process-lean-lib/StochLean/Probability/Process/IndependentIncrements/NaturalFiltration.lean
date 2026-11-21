/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Independent increments are independent of the whole natural past

For a measurable real process starting at zero almost surely, native
independent increments imply independence of each future increment from
the actual natural filtration at its left endpoint.

A finite past is sorted using the existing finite-set order isomorphism.
The true adjacent increments on a grid containing zero, that past, and
the two endpoints are jointly independent. Actual telescoping sums recover
the whole finite past from the earlier increments. The native cylinder
independence theorem then passes to every coordinate of the natural past.
Pairwise independence is not substituted for this finite-family argument.

The original process and filtration are unchanged. The zero initial value
is only an almost-everywhere input to the finite-dimensional equality; no
path regularity, completed filtration, Gaussian law, or independent-past
certificate is assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

private theorem indep_grid_past_increment
    (hX : HasIndepIncrements X P) (hXm : ∀ u, Measurable (X u))
    (hX0 : X 0 =ᵐ[P] 0) {v : ℕ → ℝ≥0} (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) :
    IndepFun (fun ω (i : Fin (k + 1)) ↦ X (v i) ω)
      (fun ω ↦ X (v (k + 1)) ω - X (v k) ω) P := by
  classical
  let D : ℕ → Ω → ℝ := fun j ω ↦ X (v (j + 1)) ω - X (v j) ω
  let m : ℕ → MeasurableSpace Ω := fun j ↦ MeasurableSpace.comap (D j) inferInstance
  let mPast : MeasurableSpace Ω := ⨆ j ∈ Iio k, m j
  have hm (j : ℕ) : @Measurable Ω ℝ mΩ inferInstance (D j) :=
    (hXm _).sub (hXm _)
  have hi : iIndep m P := (iIndepFun_iff_iIndep _ _ _).mp (hX.nat hv)
  have hsep : Indep mPast (m k) P := by
    have hdis : Disjoint (Iio k) ({k} : Set ℕ) := by
      apply Set.disjoint_left.mpr
      intro j hj hk
      exact (lt_irrefl k) ((mem_singleton_iff.mp hk) ▸ hj)
    simpa only [mPast, mem_singleton_iff, iSup_iSup_eq_left] using
      indep_iSup_of_disjoint (fun j ↦ (hm j).comap_le) hi hdis
  have hD (j : ℕ) (hj : j < k) : Measurable[mPast] (D j) :=
    Measurable.of_comap_le (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have hcenter : Measurable[mPast]
      (fun ω (i : Fin (k + 1)) ↦ X (v i) ω - X (v 0) ω) := by
    apply measurable_pi_iff.mpr
    intro i
    have heq : (fun ω ↦ X (v i) ω - X (v 0) ω) =
        (fun ω ↦ ∑ j ∈ Finset.range i.val, D j ω) := by
      funext ω
      exact (Finset.sum_range_sub (fun j ↦ X (v j) ω) i.val).symm
    rw [heq]
    exact Finset.measurable_sum _ fun j hj ↦
      hD j ((Finset.mem_range.mp hj).trans_le (Nat.le_of_lt_succ i.isLt))
  have hcenterIndep : IndepFun
      (fun ω (i : Fin (k + 1)) ↦ X (v i) ω - X (v 0) ω) (D k) P :=
    (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hsep hcenter.comap_le)
  apply hcenterIndep.congr ?_ Filter.EventuallyEq.rfl
  filter_upwards [hX0] with ω hω
  funext i
  rw [hv0, show X 0 ω = 0 from hω, sub_zero]

private theorem indep_finite_past_increment
    (hX : HasIndepIncrements X P) (hXm : ∀ u, Measurable (X u))
    (hX0 : X 0 =ᵐ[P] 0) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset (Iic s)) :
    IndepFun (fun ω (i : I) ↦ X i.val.val ω) (fun ω ↦ X t ω - X s ω) P := by
  classical
  let S : Finset ℝ≥0 := insert 0 (insert s (I.image (fun u : Iic s ↦ (u : ℝ≥0))))
  have hzero : 0 ∈ S := Finset.mem_insert_self _ _
  have hs : s ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hSne : S.Nonempty := ⟨0, hzero⟩
  obtain ⟨k, hcard⟩ := Nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (Finset.card_pos.mpr hSne))
  let e : Fin (k + 1) ↪o ℝ≥0 := S.orderEmbOfFin hcard
  let v : ℕ → ℝ≥0 := fun j ↦ if hj : j ≤ k then e ⟨j, Nat.lt_succ_iff.mpr hj⟩ else t
  have hbound : ∀ u ∈ S, u ≤ s := by
    intro u hu
    simp only [S, Finset.mem_insert, Finset.mem_image] at hu
    rcases hu with rfl | rfl | ⟨q, _, rfl⟩
    · exact bot_le
    · exact le_rfl
    · exact q.property
  have hv : Monotone v := by
    intro i j hij
    by_cases hj : j ≤ k
    · have hi := hij.trans hj
      simp only [v, dif_pos hi, dif_pos hj]
      exact e.monotone hij
    · simp only [v, dif_neg hj]
      by_cases hi : i ≤ k
      · rw [dif_pos hi]
        exact (hbound _ (S.orderEmbOfFin_mem hcard _)).trans hst
      · rw [dif_neg hi]
  have hv0 : v 0 = 0 := by
    simp only [v, dif_pos (Nat.zero_le k)]
    rw [show e ⟨0, Nat.lt_succ_iff.mpr (Nat.zero_le k)⟩ = S.min' hSne from
      Finset.orderEmbOfFin_zero hcard (Nat.succ_pos k)]
    exact le_antisymm (S.min'_le 0 hzero) bot_le
  have hvk : v k = s := by
    have helast : e (Fin.last k) = S.max' hSne := by
      simpa only [e, Nat.succ_sub_one, Fin.last] using
        Finset.orderEmbOfFin_last hcard (Nat.succ_pos k)
    change (if hj : k ≤ k then e ⟨k, Nat.lt_succ_iff.mpr hj⟩ else t) = s
    rw [dif_pos le_rfl]
    change e (Fin.last k) = s
    rw [helast]
    exact le_antisymm (S.max'_le hSne s hbound) (S.le_max' s hs)
  have hvlast : v (k + 1) = t := by
    simp only [v, dif_neg (by omega : ¬ k + 1 ≤ k)]
  have hI (i : I) : i.val.val ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩))
  let idx : I → Fin (k + 1) := fun i ↦
    (S.orderIsoOfFin hcard).symm ⟨i.val.val, hI i⟩
  have hidx (i : I) : v (idx i) = i.val.val := by
    simp only [v, dif_pos (Nat.le_of_lt_succ (idx i).isLt)]
    exact congrArg Subtype.val ((S.orderIsoOfFin hcard).apply_symm_apply ⟨i.val.val, hI i⟩)
  have hmap : Measurable (fun p : Fin (k + 1) → ℝ ↦ fun i : I ↦ p (idx i)) :=
    measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _
  have hi := (indep_grid_past_increment hX hXm hX0 hv hv0 k).comp hmap measurable_id
  simpa only [Function.comp_def, id_eq, hidx, hvk, hvlast] using hi

/-- A genuine future increment of a measurable, almost-surely zero-initial
process with native independent increments is independent of its entire
original natural past, without path regularity or completion assumptions. -/
theorem HasIndepIncrements.indep_increment_natural
    [IsProbabilityMeasure P]
    (hX : HasIndepIncrements X P) (hXm : ∀ u, Measurable (X u))
    (hX0 : X 0 =ᵐ[P] 0) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (Filtration.natural X (fun u ↦ (hXm u).stronglyMeasurable) s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P := by
  have hi : IndepFun (fun ω (u : Iic s) ↦ X u ω) (fun ω ↦ X t ω - X s ω) P :=
    IndepFun.process_indepFun (fun u ↦ hXm u) ((hXm t).sub (hXm s))
      (fun I ↦ indep_finite_past_increment hX hXm hX0 hst I)
  rw [Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).mp hi

end ProbabilityTheory

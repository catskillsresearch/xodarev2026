/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardUnrestrictedBalance
public import StochLean.Probability.Process.Counting.HazardPredictable
public import Mathlib.Probability.Martingale.Basic

/-! # The uncapped compensated closed count is a true martingale

For every probability law of the extended lifetime, the actual closed count
minus its stopped cumulative hazard is a martingale in the original natural
filtration of the Nat-valued closed count. No deterministic positive-survival
guard or finite-horizon cap is imposed. Zero and infinite lifetime atoms are
allowed; the initial count is retained.

Coordinate integrability comes from the actual unrestricted stopped-hazard
mean theorem, which establishes extended finiteness before applying `toReal`.
The natural-information event decomposition gives the conditional identities.
No global uniform-integrability conclusion is inferred from coordinate L1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0))

private theorem setIntegral_hazard_sub_unrestricted [IsFiniteMeasure μ]
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ v in Ioi (s : WithTop ℝ≥0),
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id s v ∂μ) =
      μ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  classical
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id
  have hAt := integrable_stoppedProcess_eCumulativeHazard_unrestricted μ t
  have hAs := integrable_stoppedProcess_eCumulativeHazard_unrestricted μ s
  have he : (Ioi (s : WithTop ℝ≥0)).indicator (fun v ↦ A t v - A s v) =
      fun v ↦ A t v - A s v := by
    funext v
    by_cases hv : (s : WithTop ℝ≥0) < v
    · exact Set.indicator_of_mem (show v ∈ Ioi (s : WithTop ℝ≥0) from hv) _
    · rw [Set.indicator_of_notMem (show v ∉ Ioi (s : WithTop ℝ≥0) from hv)]
      have hvs : v ≤ (s : WithTop ℝ≥0) := le_of_not_gt hv
      symm
      dsimp only [A]
      rw [stoppedProcess_eq_of_ge (hvs.trans (WithTop.coe_le_coe.mpr hst)),
        stoppedProcess_eq_of_ge hvs, sub_self]
  have hsets : Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) \
      Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0) =
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    ext v
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · intro h
      exact ⟨lt_of_not_ge (fun hvs ↦ h.2 ⟨h.1.1, hvs⟩), h.1.2⟩
    · intro h
      exact ⟨⟨(WithTop.coe_le_coe.mpr (show (0 : ℝ≥0) ≤ s from bot_le)).trans_lt h.1,
        h.2⟩, fun hvs ↦ not_lt_of_ge hvs.2 h.1⟩
  change (∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ) = _
  calc
    (∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ) =
        ∫ v, A t v - A s v ∂μ := by rw [← integral_indicator measurableSet_Ioi, he]
    _ = (∫ v, A t v ∂μ) - ∫ v, A s v ∂μ := integral_sub hAt.1 hAs.1
    _ = μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) -
        μ.real (Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0)) := by rw [hAt.2, hAs.2]
    _ = μ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
      rw [← measureReal_sdiff
        (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst)) measurableSet_Ioc, hsets]

/-- The actual uncapped closed count minus stopped hazard is a true martingale,
including zero and infinite lifetime atoms and zero-survival support endpoints. -/
theorem martingale_singleJump_sub_hazard_unrestricted [IsProbabilityMeasure μ] :
    Martingale (fun (t : ℝ≥0) (v : WithTop ℝ≥0) ↦
      (if v ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v)
      (Filtration.natural
        (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount measurable_id)) μ := by
  classical
  let N : ℝ≥0 → WithTop ℝ≥0 → ℕ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount measurable_id)
  let C : ℝ≥0 → WithTop ℝ≥0 → ℝ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id
  let M : ℝ≥0 → WithTop ℝ≥0 → ℝ := fun t v ↦ C t v - A t v
  have hmC (t : ℝ≥0) : StronglyMeasurable[ℱ t] (C t) := by
    have hN : StronglyAdapted ℱ N :=
      Filtration.stronglyAdapted_natural (stronglyMeasurable_singleJumpCount measurable_id)
    have he : {v : WithTop ℝ≥0 | v ≤ (t : WithTop ℝ≥0)} = (N t) ⁻¹' {1} := by
      ext v
      change v ≤ (t : WithTop ℝ≥0) ↔
        (if v ≤ (t : WithTop ℝ≥0) then (1 : ℕ) else 0) = 1
      by_cases hv : v ≤ (t : WithTop ℝ≥0)
      · rw [if_pos hv]
        exact iff_of_true hv rfl
      · rw [if_neg hv]
        exact iff_of_false hv Nat.zero_ne_one
    have hs : MeasurableSet[ℱ t] {v | v ≤ (t : WithTop ℝ≥0)} := by
      rw [he]
      exact (hN t).measurable (measurableSet_singleton 1)
    exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
  have hmA (t : ℝ≥0) : StronglyMeasurable[ℱ t] (A t) := by
    have ht := (isStronglyPredictable_capped_stopped_eCumulativeHazard μ t).stronglyAdapted t
    simpa only [min_self] using ht
  have hm : StronglyAdapted ℱ M := fun t ↦ (hmC t).sub (hmA t)
  have hiC (u : ℝ≥0) : Integrable (C u) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hmC u).mono (ℱ.le u)).aestronglyMeasurable
    apply Eventually.of_forall
    intro v
    change ‖if v ≤ (u : WithTop ℝ≥0) then (1 : ℝ) else 0‖ ≤ 1
    by_cases hv : v ≤ (u : WithTop ℝ≥0)
    · simp only [if_pos hv, norm_one, le_refl]
    · simp only [if_neg hv, norm_zero, zero_le_one]
  have hiA (u : ℝ≥0) : Integrable (A u) μ :=
    (integrable_stoppedProcess_eCumulativeHazard_unrestricted μ u).1
  have hiM (u : ℝ≥0) : Integrable (M u) μ := (hiC u).sub (hiA u)
  change Martingale M ℱ μ
  refine ⟨hm, fun s t hst ↦ ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hiM t)
    (fun _ _ _ ↦ (hiM s).integrableOn) ?_ (hm s).aestronglyMeasurable
  intro E hE _
  have hstopped (v : WithTop ℝ≥0) (hv : v ≤ (s : WithTop ℝ≥0)) : M t v = M s v := by
    have hvt : v ≤ (t : WithTop ℝ≥0) := hv.trans (WithTop.coe_le_coe.mpr hst)
    dsimp only [M, C, A]
    rw [if_pos hvt, if_pos hv, stoppedProcess_eq_of_ge hvt, stoppedProcess_eq_of_ge hv]
  have hcount : (∫ v in Ioi (s : WithTop ℝ≥0), C t v - C s v ∂μ) =
      μ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
    calc
      (∫ v in Ioi (s : WithTop ℝ≥0), C t v - C s v ∂μ) =
          ∫ v in Ioi (s : WithTop ℝ≥0),
            (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)).indicator (fun _ ↦ (1 : ℝ)) v ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        have hn : ¬v ≤ (s : WithTop ℝ≥0) := not_le_of_gt hv
        dsimp only [C]
        rw [if_neg hn, sub_zero]
        by_cases ht : v ≤ (t : WithTop ℝ≥0)
        · rw [if_pos ht, Set.indicator_of_mem (show v ∈ Ioc _ _ from ⟨hv, ht⟩)]
        · rw [if_neg ht, Set.indicator_of_notMem
            (show v ∉ Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) from fun h ↦ ht h.2)]
      _ = μ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
        rw [setIntegral_indicator measurableSet_Ioc,
          inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const, smul_eq_mul, mul_one]
  have hsurvDiff : (∫ v in Ioi (s : WithTop ℝ≥0), M t v - M s v ∂μ) = 0 := by
    calc
      (∫ v in Ioi (s : WithTop ℝ≥0), M t v - M s v ∂μ) =
          ∫ v in Ioi (s : WithTop ℝ≥0), (C t v - C s v) - (A t v - A s v) ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        dsimp only [M]
        ring
      _ = (∫ v in Ioi (s : WithTop ℝ≥0), C t v - C s v ∂μ) -
          ∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ :=
        integral_sub ((hiC t).sub (hiC s)).integrableOn ((hiA t).sub (hiA s)).integrableOn
      _ = 0 := by rw [hcount, setIntegral_hazard_sub_unrestricted μ hst, sub_self]
  have hsurv : (∫ v in Ioi (s : WithTop ℝ≥0), M s v ∂μ) =
      ∫ v in Ioi (s : WithTop ℝ≥0), M t v ∂μ := by
    rw [integral_sub (hiM t).integrableOn (hiM s).integrableOn] at hsurvDiff
    exact (sub_eq_zero.mp hsurvDiff).symm
  obtain ⟨B, hB, hBs, he⟩ :=
    (measurableSet_natural_singleJumpCount_iff measurable_id s E).mp hE
  have hrevealed : (∫ v in id ⁻¹' B, M s v ∂μ) = ∫ v in id ⁻¹' B, M t v ∂μ := by
    apply setIntegral_congr_fun (measurable_id hB)
    intro v hv
    exact (hstopped v (hBs hv)).symm
  rcases he with rfl | rfl
  · exact hrevealed
  · have hd : Disjoint (id ⁻¹' B) (Ioi (s : WithTop ℝ≥0)) := by
      apply Set.disjoint_left.mpr
      intro v hv hs
      exact not_lt_of_ge (show v ≤ (s : WithTop ℝ≥0) from hBs hv)
        (show (s : WithTop ℝ≥0) < v from hs)
    change (∫ v in id ⁻¹' B ∪ Ioi (s : WithTop ℝ≥0), M s v ∂μ) =
      ∫ v in id ⁻¹' B ∪ Ioi (s : WithTop ℝ≥0), M t v ∂μ
    rw [setIntegral_union hd measurableSet_Ioi (hiM s).integrableOn (hiM s).integrableOn,
      setIntegral_union hd measurableSet_Ioi (hiM t).integrableOn (hiM t).integrableOn,
      hrevealed, hsurv]

end ProbabilityTheory

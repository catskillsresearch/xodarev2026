/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardBalance
public import StochLean.Probability.Process.Counting.SingleJumpInformation
public import Mathlib.Probability.Martingale.Basic
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # The actual compensated single-jump count on a finite horizon

On the canonical lifetime space, the closed count minus its actual
stopped cumulative hazard is a true uniformly integrable martingale
after a deterministic finite cap. The filtration is the original natural
filtration of the full, uncapped Nat-valued closed count.

The martingale identity is derived from the actual natural-information
event decomposition. On the revealed-lifetime part the process has
already stopped; on the strict survival event the count and hazard
increment integrals cancel. No martingale or conditional-expectation
certificate is assumed.

An initial atom is allowed. The process at zero is `1_{v = 0}`, not
necessarily zero. Infinite lifetimes never activate the finite count.
Only the existing hazard and stopped-process owners are used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0))

private theorem stronglyMeasurable_singleJump_sub_hazard_of_le {q t : ℝ≥0}
    (hqt : q ≤ t) :
    StronglyMeasurable[(Filtration.natural
      (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount measurable_id)) t]
      (fun v ↦ (if v ≤ (q : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess
          (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id q v) := by
  classical
  let N : ℝ≥0 → WithTop ℝ≥0 → ℕ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount measurable_id)
  let R := restrictedStoppingTime id {v | v ≤ (t : WithTop ℝ≥0)}
  have hR : Measurable[ℱ t] R := by
    apply measurable_iff_comap_le.mpr
    exact (natural_singleJumpCount_eq_comap_restricted measurable_id t).symm.le
  have hRq (v : WithTop ℝ≥0) : R v ≤ (q : WithTop ℝ≥0) ↔ v ≤ (q : WithTop ℝ≥0) := by
    by_cases hv : v ≤ (t : WithTop ℝ≥0)
    · have hr : R v = v := restrictedStoppingTime_of_mem id hv
      rw [hr]
    · have hr : R v = ⊤ := restrictedStoppingTime_of_notMem id hv
      rw [hr]
      exact iff_of_false (WithTop.not_top_le_coe q)
        (fun h ↦ hv (h.trans (WithTop.coe_le_coe.mpr hqt)))
  have hmin (v : WithTop ℝ≥0) : min (q : WithTop ℝ≥0) (R v) = min (q : WithTop ℝ≥0) v := by
    by_cases hv : v ≤ (t : WithTop ℝ≥0)
    · have hr : R v = v := restrictedStoppingTime_of_mem id hv
      rw [hr]
    · have hr : R v = ⊤ := restrictedStoppingTime_of_notMem id hv
      rw [hr, min_eq_left le_top,
        min_eq_left ((WithTop.coe_le_coe.mpr hqt).trans (le_of_not_ge hv))]
  have hset : MeasurableSet[ℱ t] {v | v ≤ (q : WithTop ℝ≥0)} := by
    have he : {v | v ≤ (q : WithTop ℝ≥0)} = {v | R v ≤ (q : WithTop ℝ≥0)} := by
      ext v
      exact (hRq v).symm
    rw [he]
    exact measurableSet_le hR measurable_const
  have hC : Measurable[ℱ t]
      (fun v ↦ if v ≤ (q : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  have hclock : Measurable[ℱ t]
      (fun v : WithTop ℝ≥0 ↦ (min (q : WithTop ℝ≥0) v).untopA) := by
    have hm : Measurable[ℱ t]
        (fun v ↦ (min (q : WithTop ℝ≥0) (R v)).untopA) :=
      (measurable_const.min hR).untopA
    simpa only [hmin] using hm
  have hA : Measurable[ℱ t] (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id q) :=
    (measurable_eCumulativeHazard μ).ennreal_toReal.comp hclock
  exact (hC.sub hA).stronglyMeasurable

private theorem norm_singleJump_sub_hazard_le [IsFiniteMeasure μ] {q T : ℝ≥0}
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) (hq : q ≤ T) (v : WithTop ℝ≥0) :
    ‖(if v ≤ (q : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id q v‖ ≤
      1 + (eCumulativeHazard μ T).toReal := by
  classical
  let a := (min (q : WithTop ℝ≥0) v).untopA
  have ha : a ≤ T := (WithTop.untopA_le (min_le_left (q : WithTop ℝ≥0) v)).trans hq
  have hAf : eCumulativeHazard μ a ≠ ∞ := eCumulativeHazard_ne_top_of_le μ hT ha
  have hTf : eCumulativeHazard μ T ≠ ∞ := eCumulativeHazard_ne_top_of_le μ hT le_rfl
  have hA : (eCumulativeHazard μ a).toReal ≤ (eCumulativeHazard μ T).toReal :=
    (ENNReal.toReal_le_toReal hAf hTf).mpr (monotone_eCumulativeHazard μ ha)
  have hC : ‖if v ≤ (q : WithTop ℝ≥0) then (1 : ℝ) else 0‖ ≤ 1 := by
    by_cases hv : v ≤ (q : WithTop ℝ≥0)
    · simp only [if_pos hv, norm_one, le_refl]
    · simp only [if_neg hv, norm_zero, zero_le_one]
  change ‖(if v ≤ (q : WithTop ℝ≥0) then (1 : ℝ) else 0) -
    (eCumulativeHazard μ a).toReal‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add hC ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hA

/-- The actual finite-horizon compensated closed count is a martingale in
the original natural filtration of the full closed count. -/
theorem martingale_capped_singleJump_sub_hazard [IsProbabilityMeasure μ]
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) :
    Martingale (fun t v ↦
      (if v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal)
        id (min t T) v)
      (Filtration.natural
        (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount measurable_id)) μ := by
  classical
  let N : ℝ≥0 → WithTop ℝ≥0 → ℕ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount measurable_id)
  let C : ℝ≥0 → WithTop ℝ≥0 → ℝ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id
  let M : ℝ≥0 → WithTop ℝ≥0 → ℝ := fun t v ↦ C (min t T) v - A (min t T) v
  have hm : StronglyAdapted ℱ M := fun t ↦
    stronglyMeasurable_singleJump_sub_hazard_of_le μ (min_le_left t T)
  have hiC (u : ℝ≥0) : Integrable (C u) μ := by
    have hmC : Measurable (C u) :=
      Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const
    refine (integrable_const (1 : ℝ)).mono' hmC.aestronglyMeasurable
      (Eventually.of_forall ?_)
    intro v
    change ‖if v ≤ (u : WithTop ℝ≥0) then (1 : ℝ) else 0‖ ≤ 1
    by_cases hv : v ≤ (u : WithTop ℝ≥0)
    · simp only [if_pos hv, norm_one, le_refl]
    · simp only [if_neg hv, norm_zero, zero_le_one]
  have hiA (u : ℝ≥0) (hu : u ≤ T) : Integrable (A u) μ :=
    (integrable_stoppedProcess_eCumulativeHazard_toReal_and_integral μ hT hu).1
  have hiM (u : ℝ≥0) : Integrable (M u) μ :=
    (hiC (min u T)).sub (hiA (min u T) (min_le_right u T))
  change Martingale M ℱ μ
  refine ⟨hm, fun s t hst ↦ ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hiM t)
    (fun _ _ _ ↦ (hiM s).integrableOn) ?_ (hm s).aestronglyMeasurable
  intro E hE _
  by_cases hTs : T ≤ s
  · apply setIntegral_congr_fun (ℱ.le s E hE)
    intro v _
    simp only [M, min_eq_right hTs, min_eq_right (hTs.trans hst)]
  have hsT : s ≤ T := (lt_of_not_ge hTs).le
  let q := min t T
  have hsq : s ≤ q := le_min hst hsT
  have hqT : q ≤ T := min_le_right t T
  have hstopped (v : WithTop ℝ≥0) (hv : v ≤ (s : WithTop ℝ≥0)) : M t v = M s v := by
    have hvq : v ≤ (q : WithTop ℝ≥0) := hv.trans (WithTop.coe_le_coe.mpr hsq)
    change C q v - A q v = C (min s T) v - A (min s T) v
    rw [min_eq_left hsT]
    dsimp only [C, A]
    rw [if_pos hvq, if_pos hv, stoppedProcess_eq_of_ge hvq, stoppedProcess_eq_of_ge hv]
  have hcount : (∫ v in Ioi (s : WithTop ℝ≥0), C q v - C s v ∂μ) =
      μ.real (Ioc (s : WithTop ℝ≥0) (q : WithTop ℝ≥0)) := by
    calc
      (∫ v in Ioi (s : WithTop ℝ≥0), C q v - C s v ∂μ) =
          ∫ v in Ioi (s : WithTop ℝ≥0),
            (Ioc (s : WithTop ℝ≥0) (q : WithTop ℝ≥0)).indicator (fun _ ↦ (1 : ℝ)) v ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        have hn : ¬v ≤ (s : WithTop ℝ≥0) := not_le_of_gt hv
        dsimp only [C]
        rw [if_neg hn, sub_zero]
        by_cases hq : v ≤ (q : WithTop ℝ≥0)
        · rw [if_pos hq, Set.indicator_of_mem (show v ∈ Ioc _ _ from ⟨hv, hq⟩)]
        · have hnot : v ∉ Ioc (s : WithTop ℝ≥0) (q : WithTop ℝ≥0) := fun h ↦ hq h.2
          rw [if_neg hq, Set.indicator_of_notMem hnot]
      _ = μ.real (Ioc (s : WithTop ℝ≥0) (q : WithTop ℝ≥0)) := by
        rw [setIntegral_indicator measurableSet_Ioc,
          inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const, smul_eq_mul, mul_one]
  have hsurvDiff : (∫ v in Ioi (s : WithTop ℝ≥0), M t v - M s v ∂μ) = 0 := by
    calc
      (∫ v in Ioi (s : WithTop ℝ≥0), M t v - M s v ∂μ) =
          ∫ v in Ioi (s : WithTop ℝ≥0),
            (C q v - C s v) - (A q v - A s v) ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        change (C q v - A q v) - (C (min s T) v - A (min s T) v) = _
        rw [min_eq_left hsT]
        ring
      _ = (∫ v in Ioi (s : WithTop ℝ≥0), C q v - C s v ∂μ) -
          ∫ v in Ioi (s : WithTop ℝ≥0), A q v - A s v ∂μ :=
        integral_sub ((hiC q).sub (hiC s)).integrableOn
          ((hiA q hqT).sub (hiA s hsT)).integrableOn
      _ = 0 := by
        rw [hcount, setIntegral_stoppedProcess_eCumulativeHazard_toReal_sub μ hT hsq hqT,
          sub_self]
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

/-- The actual finite-horizon compensated count is uniformly integrable,
by its common bound `1 + (eCumulativeHazard μ T).toReal`. -/
theorem uniformIntegrable_capped_singleJump_sub_hazard [IsProbabilityMeasure μ]
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) :
    UniformIntegrable (fun t v ↦
      (if v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal)
        id (min t T) v) 1 μ := by
  let K : ℝ := 1 + (eCumulativeHazard μ T).toReal
  have hM := martingale_capped_singleJump_sub_hazard μ T hT
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ fun _ : WithTop ℝ≥0 ↦ K) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_const K)
  apply hu.mono_norm
  · intro t
    exact (hM.integrable t).aestronglyMeasurable
  · intro t
    apply Eventually.of_forall
    intro v
    exact (norm_singleJump_sub_hazard_le μ hT (min_le_right t T) v).trans (le_abs_self K)

end ProbabilityTheory

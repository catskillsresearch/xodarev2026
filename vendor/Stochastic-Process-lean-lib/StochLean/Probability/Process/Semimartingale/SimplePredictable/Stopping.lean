/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Refinement
public import StochLean.Probability.Process.Stopping.Integrand

/-! # Stopping the full source simple predictable class

The cutoff is `H 1_[0,τ]`, not the frozen stopped process `H^τ`. The source initial
coefficient is retained, including when the stopping time is zero. No boundedness
of coefficients or deterministic bound on the finite partition endpoints is imposed.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

/-- Cut off on a common partition containing the finite stopping endpoint. -/
noncomputable def cutoffFinite (H : SimplePredictableRep F) (σ : FiniteStoppingTime F) :
    SimplePredictableRep F :=
  let ρ := H.partition.splitAt σ
  let R := H.repartition ρ
  { partition := ρ
    initial := H.initial
    measurable_initial := H.measurable_initial
    coefficient := fun i ω ↦ if ρ.point i.castSucc ω < σ ω then R.coefficient i ω else 0
    measurable_coefficient := fun i ↦ by
      have hs : MeasurableSet[(ρ.point i.castSucc).measurableSpace]
          {ω | ρ.point i.castSucc ω < σ ω} := by
        simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using
          (σ.isStoppingTime.measurableSet_stopping_time_le
            (ρ.point i.castSucc).isStoppingTime).compl
      exact Measurable.ite hs (R.measurable_coefficient i) measurable_const }

theorem toProcess_cutoffFinite (H : SimplePredictableRep F) (σ : FiniteStoppingTime F) :
    (H.cutoffFinite σ).toProcess = cutoffIntegrand H.toProcess σ.withTop := by
  let ρ := H.partition.splitAt σ
  have hρ : ρ.Refines H.partition := H.partition.splitAt_refines σ
  have heq := H.toProcess_repartition hρ
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [toProcess_zero, cutoffIntegrand_zero]
    rfl
  by_cases hterm : t ≤ ρ.terminal ω
  · have hcell : ∃ i : Fin ρ.size, ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω :=
      (ρ.path ω).exists_cell ⟨lt_of_le_of_ne bot_le (Ne.symm ht), hterm⟩
    obtain ⟨i, hi⟩ := hcell
    have hj : ∃ j, ρ.point j ω = σ ω := H.partition.splitAt_contains σ ω
    obtain ⟨j, hj⟩ := hj
    have hσ : t ≤ σ ω ↔ ρ.point i.castSucc ω < σ ω := by
      simpa only [hj] using (StoppingTimePartition.Refines.refl ρ).le_point_iff_left_lt hi j
    rw [(H.cutoffFinite σ).toProcess_eq_coefficient_of_mem_cell (i := i) hi]
    change (if ρ.point i.castSucc ω < σ ω then (H.repartition ρ).coefficient i ω else 0) = _
    rw [cutoffIntegrand]
    simp only [FiniteStoppingTime.withTop, WithTop.coe_le_coe]
    rw [← heq, (H.repartition ρ).toProcess_eq_coefficient_of_mem_cell (i := i) hi]
    simp only [hσ]
  · have hρt : ρ.terminal ω < t := lt_of_not_ge hterm
    rw [(H.cutoffFinite σ).toProcess_eq_zero_of_terminal_lt hρt,
      cutoffIntegrand, H.toProcess_eq_zero_of_terminal_lt ((hρ.terminal_le ω).trans_lt hρt)]
    simp only [ite_self]

/-- Cutoff at an arbitrary stopping time, including infinity. Capping at this
representation's finite terminal time changes nothing on its support. -/
theorem isSimplePredictable_cutoff (H : SimplePredictableRep F)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsSimplePredictable (cutoffIntegrand H.toProcess τ) F := by
  let σ := FiniteStoppingTime.ofNotTop (H.partition.terminal.isStoppingTime.min hτ)
    (fun ω ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))
  refine ⟨H.cutoffFinite σ, (H.toProcess_cutoffFinite σ).trans ?_⟩
  have hσ : σ.withTop = fun ω ↦ min (H.partition.terminal ω : WithTop ℝ≥0) (τ ω) :=
    FiniteStoppingTime.withTop_ofNotTop _ _
  rw [hσ]
  funext t ω
  by_cases ht : t ≤ H.partition.terminal ω
  · simp only [cutoffIntegrand, le_min_iff, WithTop.coe_le_coe, ht, true_and]
  · rw [cutoffIntegrand, cutoffIntegrand,
      H.toProcess_eq_zero_of_terminal_lt (lt_of_not_ge ht)]
    simp only [ite_self]

/-- A pathwise finite cutoff identity for an arbitrary integrator. The process
equality is needed only at the sample under consideration. -/
theorem integral_eq_stopped_of_cutoff_path (H K : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hHK : ∀ t, K.toProcess t ω = if t ≤ T then H.toProcess t ω else 0) :
    K.integral X ω = H.integral (fun t v ↦ X (min t T) v) ω := by
  have hinit : K.initial ω = H.initial ω := by
    simpa using hHK 0
  have hsum := StochLean.sum_intervalIncrement_congr
    (fun i : Fin K.partition.size ↦ K.partition.point i.castSucc ω)
    (fun i : Fin K.partition.size ↦ K.partition.point i.succ ω)
    (fun i : Fin K.partition.size ↦ K.coefficient i ω)
    (fun i : Fin H.partition.size ↦ min (H.partition.point i.castSucc ω) T)
    (fun i : Fin H.partition.size ↦ min (H.partition.point i.succ ω) T)
    (fun i : Fin H.partition.size ↦ H.coefficient i ω)
    (fun i ↦ (K.partition.path ω).left_le_right i)
    (fun i ↦ min_le_min_right T ((H.partition.path ω).left_le_right i))
    (fun t ht ↦ by
      have heq := hHK t
      simp only [toProcess, ne_of_gt ht, if_false] at heq
      by_cases hT : t ≤ T
      · simpa only [min_lt_iff, le_min_iff, not_lt_of_ge hT, or_false, hT,
          and_true, if_true] using heq
      · simpa only [le_min_iff, hT, and_false, if_false, sum_const_zero] using heq)
    (fun t ↦ X t ω)
  change K.initial ω * X 0 ω + _ = H.initial ω * X (min 0 T) ω + _
  have hzero : min (0 : ℝ≥0) T = 0 := by simp
  rw [hinit, hzero, hsum]

/-- The elementary stopping identity is algebraic and does not assume that the
integrator is a semimartingale, finite variation, or even measurable. -/
theorem integral_eq_stopped_of_cutoff (H K : SimplePredictableRep F)
    (τ : Ω → WithTop ℝ≥0) (hHK : K.toProcess = cutoffIntegrand H.toProcess τ)
    (X : ℝ≥0 → Ω → ℝ) : K.integral X = H.integral (stoppedProcess X τ) := by
  funext ω
  have heq (t) := congrFun (congrFun hHK t) ω
  cases hτω : τ ω with
  | top =>
    have hpath (t) : K.toProcess t ω =
        if t ≤ H.partition.terminal ω then H.toProcess t ω else 0 := by
      have h := heq t
      simp only [cutoffIntegrand, hτω, le_top, if_true] at h
      by_cases ht : t ≤ H.partition.terminal ω
      · simpa only [if_pos ht] using h
      · simpa only [if_neg ht, H.toProcess_eq_zero_of_terminal_lt (lt_of_not_ge ht)] using h
    have h := H.integral_eq_stopped_of_cutoff_path K X ω (H.partition.terminal ω) hpath
    have hpoint (i : Fin (H.partition.size + 1)) :
        min (H.partition.point i ω) (H.partition.terminal ω) = H.partition.point i ω :=
      min_eq_left (H.partition.monotone_point ω (Fin.le_last i))
    have hstop (t : ℝ≥0) : stoppedProcess X τ t ω = X t ω :=
      stoppedProcess_eq_of_le (by rw [hτω]; exact le_top)
    exact h.trans (by simp only [integral, hpoint, hstop]; simp)
  | coe T =>
    have hpath (t) : K.toProcess t ω = if t ≤ T then H.toProcess t ω else 0 := by
      simpa only [cutoffIntegrand, hτω, WithTop.coe_le_coe] using heq t
    have h := H.integral_eq_stopped_of_cutoff_path K X ω T hpath
    have hstop (t : ℝ≥0) : stoppedProcess X τ t ω = X (min t T) ω := by
      change X (min (t : WithTop ℝ≥0) (τ ω)).untopA ω = _
      rw [hτω, ← WithTop.coe_min]
      rfl
    exact h.trans (by simp only [integral, hstop])

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem cutoff (hH : IsSimplePredictable H F) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) : IsSimplePredictable (cutoffIntegrand H τ) F := by
  simpa only [hH.choose_spec] using hH.choose.isSimplePredictable_cutoff hτ

theorem elementaryIntegral_cutoff (hH : IsSimplePredictable H F)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (X : ℝ≥0 → Ω → ℝ) :
    (hH.cutoff hτ).elementaryIntegral X = hH.elementaryIntegral (stoppedProcess X τ) := by
  apply hH.choose.integral_eq_stopped_of_cutoff (hH.cutoff hτ).choose τ
  rw [(hH.cutoff hτ).choose_spec, hH.choose_spec]

end IsSimplePredictable
end ProbabilityTheory

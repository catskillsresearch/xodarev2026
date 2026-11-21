/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ClosedRegion
public import StochLean.Probability.Process.Path.StoppingConstancy

/-! # First departure from the value at a deterministic time

The stopping time is Mathlib's hitting time of a stopped-increment process.
This avoids a random target set or an unadapted future initial value. A
continuous path retains its starting value at the finite departure endpoint.
Countably many such exits control every closed interval simultaneously.
-/

@[expose] public section

open ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

noncomputable def constancyExit (X : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  hittingAfter (fun t ω ↦ X t ω - X (min t r) ω) {0}ᶜ r

theorem le_constancyExit (X : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) :
    (r : WithTop ℝ≥0) ≤ constancyExit X r ω := le_hittingAfter ω

theorem stoppedProcess_constancyExit_of_continuous
    (hc : Continuous (X · ω)) (r : ℝ≥0) (t : ℝ≥0) :
    stoppedProcess X (constancyExit X r) t ω = stoppedProcess X (fun _ ↦ r) t ω := by
  apply stoppedProcess_eq_of_eq_on_stopping_interval (le_constancyExit X r ω)
  intro s u hrs hs hru hu
  have he (v : ℝ≥0) (hrv : (r : WithTop ℝ≥0) ≤ v)
      (hv : (v : WithTop ℝ≥0) ≤ constancyExit X r ω) : X v ω = X r ω := by
    have h := mem_of_le_hittingAfter_compl_of_continuous_from
      (X := fun t ω ↦ X t ω - X (min t r) ω) (ω := ω)
      (hc.sub (hc.comp (continuous_id.min continuous_const))) isClosed_singleton
      (by simp : X r ω - X (min r r) ω ∈ ({0} : Set ℝ))
      (WithTop.coe_le_coe.mp hrv) hv
    simpa only [mem_singleton_iff, min_eq_right (WithTop.coe_le_coe.mp hrv),
      sub_eq_zero] using h
  exact (he s hrs hs).trans (he u hru hu).symm

theorem le_constancyExit_of_eqOn {r t : ℝ≥0}
    (he : EqOn (X · ω) (fun _ ↦ X r ω) (Icc r t)) :
    (t : WithTop ℝ≥0) ≤ constancyExit X r ω := by
  apply le_of_not_gt
  intro h
  obtain ⟨u, hu, hne⟩ := hittingAfter_lt_iff.mp h
  have hu0 : X u ω - X (min u r) ω = 0 := by
    rw [min_eq_right hu.1]
    exact sub_eq_zero.mpr (he ⟨hu.1, hu.2.le⟩)
  exact hne (mem_singleton_iff.mpr hu0)

theorem Adapted.isStoppingTime_constancyExit
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) (r : ℝ≥0) :
    IsStoppingTime F (constancyExit X r) := by
  have had : Adapted F (fun t ω ↦ X t ω - X (min t r) ω) := fun t ↦
    (ha t).sub ((ha (min t r)).mono (F.mono (min_le_left t r)) le_rfl)
  have hcd : HasContinuousPaths (fun t ω ↦ X t ω - X (min t r) ω) P :=
    hc.mono fun _ hω ↦ hω.sub (hω.comp (continuous_id.min continuous_const))
  exact had.isStoppingTime_hittingAfter_isOpen_of_usual hF hcd.hasRightContinuousPaths
    isClosed_singleton.isOpen_compl r

/-- A single countable family of stopped equalities controls all intervals,
including intervals with zero left endpoint. -/
theorem eqOn_Icc_of_stopped_constancyExit
    (hc : Continuous (Y · ω))
    (he : ∀ n t, stoppedProcess Y (constancyExit X (denseSeq ℝ≥0 n)) t ω =
      stoppedProcess Y (fun _ ↦ denseSeq ℝ≥0 n) t ω)
    {s t : ℝ≥0} (hst : s ≤ t) (hX : EqOn (X · ω) (fun _ ↦ X s ω) (Icc s t)) :
    EqOn (Y · ω) (fun _ ↦ Y s ω) (Icc s t) := by
  obtain rfl | hst := hst.eq_or_lt
  · intro u hu
    rw [Icc_self, mem_singleton_iff] at hu
    simp only [hu]
  have hi : EqOn (Y · ω) (fun _ ↦ Y t ω) (Ioo s t) := by
    intro u hu
    have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
    obtain ⟨r, hr, n, rfl⟩ :=
      hD.inter_open_nonempty (Ioo s u) isOpen_Ioo
        (nonempty_Ioo.mpr hu.1)
    have hrt : denseSeq ℝ≥0 n ≤ t := hr.2.le.trans hu.2.le
    have htτ : (t : WithTop ℝ≥0) ≤ constancyExit X (denseSeq ℝ≥0 n) ω := by
      apply le_constancyExit_of_eqOn
      intro v hv
      exact (hX ⟨hr.1.le.trans hv.1, hv.2⟩).trans (hX ⟨hr.1.le, hrt⟩).symm
    have hv (v : ℝ≥0) (hrv : denseSeq ℝ≥0 n ≤ v) (hvt : v ≤ t) :
        Y v ω = Y (denseSeq ℝ≥0 n) ω := by
      have h := he n v
      rw [stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr hvt).trans htτ)] at h
      simpa only [stoppedProcess, min_eq_right (WithTop.coe_le_coe.mpr hrv),
        WithTop.untopA, WithTop.untopD_coe] using h
    exact (hv u hr.2.le hu.2.le).trans (hv t hrt le_rfl).symm
  have hclosed := hi.closure hc continuous_const
  rw [closure_Ioo hst.ne] at hclosed
  exact fun u hu ↦ (hclosed hu).trans (hclosed ⟨le_rfl, hst.le⟩).symm

end MeasureTheory

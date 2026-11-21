/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.RightContinuousHitting
public import StochLean.Probability.Process.Path.Continuous
public import Mathlib.Probability.Process.LocalProperty

/-! # Continuous paths stopped at exits from closed regions

The owner is Mathlib's first hitting time of the open complement. Continuity
retains membership at a finite stopping endpoint. Compact-horizon coverage
gives actual localizing sequences, including initial exit times equal to zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}
  {K : Set E} {ω : Ω}

theorem mem_of_le_hittingAfter_compl_of_continuous_from
    (hc : Continuous (X · ω)) (hK : IsClosed K) {r t : ℝ≥0}
    (hr : X r ω ∈ K) (hrt : r ≤ t)
    (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X Kᶜ r ω) : X t ω ∈ K := by
  obtain rfl | hrt := hrt.eq_or_lt
  · exact hr
  have hcl : t ∈ closure (Ico r t) := by
    rw [closure_Ico hrt.ne]
    exact ⟨hrt.le, le_rfl⟩
  apply closure_minimal (s := Ico r t) (t := (X · ω) ⁻¹' K) ?_ (hK.preimage hc) hcl
  intro u hu
  exact not_not.mp (notMem_of_lt_hittingAfter (u := X) (s := Kᶜ)
    ((WithTop.coe_lt_coe.mpr hu.2).trans_le ht) hu.1)

theorem mem_of_le_hittingAfter_compl_of_continuous
    (hc : Continuous (X · ω)) (hK : IsClosed K) (h0 : X 0 ω ∈ K)
    {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X Kᶜ 0 ω) : X t ω ∈ K :=
  mem_of_le_hittingAfter_compl_of_continuous_from hc hK h0 bot_le ht

theorem stoppedProcess_mem_closedRegion_of_continuous
    (hc : Continuous (X · ω)) (hK : IsClosed K) (h0 : X 0 ω ∈ K) (t : ℝ≥0) :
    stoppedProcess X (hittingAfter X Kᶜ 0) t ω ∈ K := by
  apply mem_of_le_hittingAfter_compl_of_continuous hc hK h0
  have hne : min (t : WithTop ℝ≥0) (hittingAfter X Kᶜ 0 ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  exact min_le_right _ _

theorem stoppedProcess_mem_closedRegion_of_pos
    (hc : Continuous (X · ω)) (hK : IsClosed K)
    (hp : 0 < hittingAfter X Kᶜ 0 ω) (t : ℝ≥0) :
    stoppedProcess X (hittingAfter X Kᶜ 0) t ω ∈ K := by
  apply stoppedProcess_mem_closedRegion_of_continuous hc hK _ t
  exact not_not.mp (notMem_of_lt_hittingAfter (u := X) (s := Kᶜ)
    (show ((0 : ℝ≥0) : WithTop ℝ≥0) < hittingAfter X Kᶜ 0 ω from hp) le_rfl)

omit [TopologicalSpace E] in
theorem tendsto_hittingAfter_compl_of_covers {K : ℕ → Set E}
    (hK : ∀ T : ℝ≥0, ∃ N, ∀ n ≥ N, ∀ t ≤ T, X t ω ∈ K n) :
    Tendsto (fun n ↦ hittingAfter X (K n)ᶜ 0 ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨N, hN⟩ := hK (T + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle : ((T + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ hittingAfter X (K n)ᶜ 0 ω := by
    apply le_of_not_gt
    intro h
    obtain ⟨t, ht, hnot⟩ := hittingAfter_lt_iff.mp h
    exact hnot (hN n hn t ht.2.le)
  exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hle

theorem Adapted.isLocalizingSequence_closedRegion_exits
    {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
    {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {K : ℕ → Set E}
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (hK : ∀ n, IsClosed (K n)) (hm : Monotone K)
    (hcover : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ N, ∀ n ≥ N, ∀ t ≤ T, X t ω ∈ K n) :
    IsLocalizingSequence F (fun n ↦ hittingAfter X (K n)ᶜ 0) P where
  isStoppingTime n := ha.isStoppingTime_hittingAfter_isOpen_of_usual hF
    hc.hasRightContinuousPaths (hK n).isOpen_compl 0
  tendsto_top := hcover.mono fun _ hω ↦ tendsto_hittingAfter_compl_of_covers hω
  mono := Eventually.of_forall fun ω _ _ hnm ↦
    hittingAfter_anti X 0 (compl_subset_compl.mpr (hm hnm)) ω

end MeasureTheory

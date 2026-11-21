/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.QuadraticVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousConstancyIntervals

/-! # The discontinuous counterexample after Protter II.27, Corollary 5

A unit-rate compensated count cannot be constant on a nondegenerate interval.
Its actual raw bracket is the count, which has a nontrivial constant right
neighborhood at every time, on one full-measure event. Together with the
proved martingale property this exhibits why continuity is essential.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem natCast_sub_time_not_eqOn_Icc (n : ℝ≥0 → ℕ) {a b : ℝ≥0} (hab : a < b) :
    ¬ EqOn (fun t ↦ (n t : ℝ) - t) (fun _ ↦ (n a : ℝ) - a) (Icc a b) := by
  intro he
  let c : ℝ≥0 := min b (a + 1 / 2)
  have hac : a < c := lt_min hab (by norm_num)
  have hcb : c ≤ b := min_le_left _ _
  have hca : (c : ℝ) ≤ (a : ℝ) + 1 / 2 := by
    exact_mod_cast (min_le_right b (a + 1 / 2))
  have hc := he ⟨hac.le, hcb⟩
  have hacR : (a : ℝ) < c := NNReal.coe_lt_coe.mpr hac
  have hnc : n a < n c := by
    exact_mod_cast (show (n a : ℝ) < n c by linarith)
  have hncR : (n a : ℝ) + 1 ≤ n c := by exact_mod_cast Nat.succ_le_of_lt hnc
  linarith

theorem natCast_sub_time_not_constant_on_interval (n : ℝ≥0 → ℕ) {I : Set ℝ≥0}
    (hI : I.OrdConnected) (hne : I.Nontrivial) :
    ¬ ∀ s ∈ I, ∀ t ∈ I, (n s : ℝ) - s = (n t : ℝ) - t := by
  intro he
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  have hpair {s t : ℝ≥0} (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) : False := by
    apply natCast_sub_time_not_eqOn_Icc n hst
    intro u hu
    exact he u (hI.out hs ht hu) s hs
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact hpair ha hb hab
  · exact hpair hb ha hba

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem IsPoissonProcess.ae_exists_constant_right_interval
    (hN : IsPoissonProcess N rate P) :
    ∀ᵐ ω ∂P, ∀ a : ℝ≥0, ∃ b, a < b ∧ EqOn (N · ω) (fun _ ↦ N a ω) (Icc a b) := by
  filter_upwards [hN.rightContinuousPaths] with ω hr a
  have hnear : {s : ℝ≥0 | N s ω = N a ω} ∈ 𝓝[≥] a := by
    exact (hr a) ((isOpen_discrete ({N a ω} : Set ℕ)).mem_nhds (mem_singleton _))
  obtain ⟨b, hab, hb⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hnear
  exact ⟨b, hab, fun _ ht ↦ hb ht⟩

theorem IsPoissonProcess.ae_compensated_bracket_constancy_counterexample
    (hN : IsPoissonProcess N 1 P) (hF : F.IsUsual P) (ha : Adapted F N) :
    ∀ᵐ ω ∂P, ∀ a : ℝ≥0, ∃ b, a < b ∧
      EqOn ((hN.isSemimartingale_compensated hF ha).quadraticVariation hF · ω)
        (fun _ ↦ (hN.isSemimartingale_compensated hF ha).quadraticVariation hF a ω)
        (Icc a b) ∧
      ¬ EqOn (fun t ↦ (N t ω : ℝ) - t) (fun _ ↦ (N a ω : ℝ) - a) (Icc a b) := by
  filter_upwards [hN.ae_exists_constant_right_interval, hN.quadraticVariation_compensated_eq hF ha]
    with ω hc hq a
  obtain ⟨b, hab, hb⟩ := hc a
  refine ⟨b, hab, ?_, natCast_sub_time_not_eqOn_Icc (N · ω) hab⟩
  intro t ht
  change (hN.isSemimartingale_compensated hF ha).quadraticVariation hF t ω =
    (hN.isSemimartingale_compensated hF ha).quadraticVariation hF a ω
  rw [hq t, hq a]
  exact_mod_cast hb ht

theorem IsPoissonProcess.not_isContinuousLocalMartingale_compensated
    (hN : IsPoissonProcess N 1 P) (hF : F.IsUsual P) (ha : Adapted F N) :
    ¬ IsContinuousLocalMartingale (fun t ω ↦ (N t ω : ℝ) - (1 : ℝ≥0) * t) F P := by
  intro hM
  obtain ⟨ω, he, hc⟩ := ((hM.ae_eqOn_Icc_iff_quadraticVariation hF).and
    (hN.ae_compensated_bracket_constancy_counterexample hF ha)).exists
  obtain ⟨b, hb, hq, hn⟩ := hc 0
  apply hn
  simpa only [NNReal.coe_one, one_mul] using (he 0 b hb.le).mpr hq

end ProbabilityTheory

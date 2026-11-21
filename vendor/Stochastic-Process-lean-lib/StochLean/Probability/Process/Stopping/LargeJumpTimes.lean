/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpEvents
public import StochLean.Probability.Process.Path.CadlagLargeJumps
public import Mathlib.Probability.Process.Stopping

/-! # The next actual large jump after a stopping time

The owner `nextLargeJump` is the extended infimum of actual strict large-jump candidates strictly
after the supplied time. The starting time may be infinite, in which case the result is infinite.
For cadlag paths and a positive threshold, local finiteness guarantees that a finite value is an
actual large jump strictly after the starting time, rather than merely a limiting candidate.

Open sublevel events are expressed with a countable dense intermediary between the starting time
and the candidate jump. The existing deterministic open-interval jump event then supplies their
measurability; right continuity of the filtration gives the stopping-time property.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The first strict large-jump candidate strictly after an extended starting time. The initial
source jump is excluded automatically, and an empty set of candidates gives infinity. -/
noncomputable def nextLargeJump (X : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (σ : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t : ℝ≥0, ⨅ (_ : σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖),
    (t : WithTop ℝ≥0)

variable {X : ℝ≥0 → Ω → ℝ} {b : ℝ} {σ η : Ω → WithTop ℝ≥0} {ω : Ω}

theorem nextLargeJump_lt_iff {t : ℝ≥0} :
    nextLargeJump X b σ ω < (t : WithTop ℝ≥0) ↔
      ∃ u : ℝ≥0, σ ω < (u : WithTop ℝ≥0) ∧ u < t ∧ b < ‖jumpProcess X u ω‖ := by
  simp only [nextLargeJump, iInf_lt_iff, WithTop.coe_lt_coe]
  constructor
  · rintro ⟨u, hu, hut⟩
    exact ⟨u, hu.1, hut, hu.2⟩
  · rintro ⟨u, hσu, hut, hu⟩
    exact ⟨u, ⟨hσu, hu⟩, hut⟩

theorem nextLargeJump_eq_top_iff :
    nextLargeJump X b σ ω = ⊤ ↔
      ∀ t : ℝ≥0, ¬ (σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖) := by
  simp only [nextLargeJump, iInf_eq_top, WithTop.coe_ne_top, imp_false]

theorem nextLargeJump_ne_top_iff :
    nextLargeJump X b σ ω ≠ ⊤ ↔
      ∃ t : ℝ≥0, σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖ := by
  rw [ne_eq, nextLargeJump_eq_top_iff]
  simp only [not_forall, not_not]

/-- An infinite starting time has no finite successor jump. -/
theorem nextLargeJump_of_eq_top (hσ : σ ω = ⊤) : nextLargeJump X b σ ω = ⊤ := by
  apply nextLargeJump_eq_top_iff.mpr
  intro t ht
  exact not_top_lt (hσ ▸ ht.1)

/-- The next candidate never precedes the starting time, without regularity assumptions. -/
theorem le_nextLargeJump : σ ω ≤ nextLargeJump X b σ ω := by
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  exact ht.1.le

theorem nextLargeJump_le_of_jump {t : ℝ≥0}
    (hσt : σ ω < (t : WithTop ℝ≥0)) (ht : b < ‖jumpProcess X t ω‖) :
    nextLargeJump X b σ ω ≤ (t : WithTop ℝ≥0) :=
  iInf_le_of_le t (iInf_le_of_le ⟨hσt, ht⟩ le_rfl)

/-- Moving the starting time forward cannot advance the next large jump. -/
theorem nextLargeJump_mono (hση : σ ω ≤ η ω) :
    nextLargeJump X b σ ω ≤ nextLargeJump X b η ω := by
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  exact nextLargeJump_le_of_jump (hση.trans_lt ht.1) ht.2

theorem nextLargeJump_eq_coe_of_first {t : ℝ≥0}
    (hσt : σ ω < (t : WithTop ℝ≥0)) (ht : b < ‖jumpProcess X t ω‖)
    (hfirst : ∀ u : ℝ≥0, σ ω < (u : WithTop ℝ≥0) →
      b < ‖jumpProcess X u ω‖ → t ≤ u) : nextLargeJump X b σ ω = (t : WithTop ℝ≥0) := by
  apply le_antisymm (nextLargeJump_le_of_jump hσt ht)
  apply le_iInf
  intro u
  apply le_iInf
  intro hu
  exact WithTop.coe_le_coe.mpr (hfirst u hu.1 hu.2)

/-- A finite value is attained at the actual first large jump, by local finiteness of cadlag
large jumps. No finite replacement for an infinite time is evaluated. -/
theorem IsCadlagPath.nextLargeJump_spec (hX : IsCadlagPath (X · ω)) (hb : 0 < b)
    (hne : nextLargeJump X b σ ω ≠ ⊤) :
    ∃ t : ℝ≥0, nextLargeJump X b σ ω = (t : WithTop ℝ≥0) ∧
      σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖ ∧
        ∀ u : ℝ≥0, σ ω < (u : WithTop ℝ≥0) → b < ‖jumpProcess X u ω‖ → t ≤ u := by
  obtain ⟨u, hσu, hu⟩ := nextLargeJump_ne_top_iff.mp hne
  cases hσ : σ ω with
  | top => exact (not_top_lt (hσ ▸ hσu)).elim
  | coe s =>
    have hsu : s < u := WithTop.coe_lt_coe.mp (hσ ▸ hσu)
    obtain ⟨t, hst, ht, hfirst⟩ := hX.exists_first_large_jump_after s hb ⟨u, hsu, hu⟩
    have hσt : σ ω < (t : WithTop ℝ≥0) := by
      rw [hσ]
      exact WithTop.coe_lt_coe.mpr hst
    have hf : ∀ v : ℝ≥0, σ ω < (v : WithTop ℝ≥0) →
        b < ‖jumpProcess X v ω‖ → t ≤ v := by
      intro v hσv hv
      exact hfirst v (WithTop.coe_lt_coe.mp (hσ ▸ hσv)) hv
    refine ⟨t, nextLargeJump_eq_coe_of_first hσt ht hf,
      WithTop.coe_lt_coe.mpr hst, ht, ?_⟩
    intro v hsv hv
    exact hfirst v (WithTop.coe_lt_coe.mp hsv) hv

theorem IsCadlagPath.nextLargeJump_mem_of_eq_coe (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {t : ℝ≥0} (ht : nextLargeJump X b σ ω = (t : WithTop ℝ≥0)) :
    σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖ := by
  have hne : nextLargeJump X b σ ω ≠ ⊤ :=
    fun htop ↦ WithTop.coe_ne_top (ht.symm.trans htop)
  obtain ⟨u, hu, hσu, hj, _⟩ := hX.nextLargeJump_spec hb hne
  have hut : u = t := WithTop.coe_injective (hu.symm.trans ht)
  simpa only [hut] using And.intro hσu hj

/-- Strict progress is a conclusion on the finite-result domain, not a claim about infinity. -/
theorem IsCadlagPath.lt_nextLargeJump_of_ne_top (hX : IsCadlagPath (X · ω)) (hb : 0 < b)
    (hne : nextLargeJump X b σ ω ≠ ⊤) : σ ω < nextLargeJump X b σ ω := by
  obtain ⟨t, ht, hσt, _, _⟩ := hX.nextLargeJump_spec hb hne
  rw [ht]
  exact hσt

/-- A dense intermediary separates the random starting time from an actual candidate jump.
Only the intermediary is countably selected; the candidate remains an actual jump. -/
theorem nextLargeJump_lt_iff_dense_interval {t : ℝ≥0} :
    nextLargeJump X b σ ω < (t : WithTop ℝ≥0) ↔
      ∃ n : ℕ, denseSeq ℝ≥0 n < t ∧ σ ω < (denseSeq ℝ≥0 n : WithTop ℝ≥0) ∧
        ∃ u : ℝ≥0, denseSeq ℝ≥0 n < u ∧ u < t ∧ b < ‖jumpProcess X u ω‖ := by
  rw [nextLargeJump_lt_iff]
  constructor
  · rintro ⟨u, hσu, hut, hu⟩
    cases hσ : σ ω with
    | top => exact (not_top_lt (hσ ▸ hσu)).elim
    | coe s =>
      have hsu : s < u := WithTop.coe_lt_coe.mp (hσ ▸ hσu)
      obtain ⟨p, ⟨n, rfl⟩, hsp, hpu⟩ := (denseRange_denseSeq ℝ≥0).exists_between hsu
      refine ⟨n, hpu.trans hut, ?_, u, hpu, hut, hu⟩
      exact WithTop.coe_lt_coe.mpr hsp
  · rintro ⟨n, _, hσn, u, hnu, hut, hu⟩
    exact ⟨u, hσn.trans (WithTop.coe_lt_coe.mpr hnu), hut, hu⟩

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

/-- Open sublevels are measurable using only adaptedness, everywhere cadlag paths and the
stopping-time property of the starting time. Filtration right continuity is not yet needed. -/
theorem Adapted.measurableSet_nextLargeJump_lt (hX : Adapted F X)
    (hc : ∀ ω, ProbabilityTheory.IsCadlagPath (X · ω)) (hb : 0 < b)
    (hσ : IsStoppingTime F σ) (t : ℝ≥0) :
    MeasurableSet[F t] {ω | ProbabilityTheory.nextLargeJump X b σ ω < (t : WithTop ℝ≥0)} := by
  have he : {ω | ProbabilityTheory.nextLargeJump X b σ ω < (t : WithTop ℝ≥0)} =
      ⋃ n : ℕ, ⋃ (_ : denseSeq ℝ≥0 n < t),
        {ω | σ ω < (denseSeq ℝ≥0 n : WithTop ℝ≥0)} ∩
          {ω | ∃ u : ℝ≥0, denseSeq ℝ≥0 n < u ∧ u < t ∧
            b < ‖ProbabilityTheory.jumpProcess X u ω‖} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff,
      ProbabilityTheory.nextLargeJump_lt_iff_dense_interval, exists_prop]
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact (F.mono hn.le _ (hσ.measurableSet_lt (denseSeq ℝ≥0 n))).inter
    (hX.measurableSet_exists_large_jump_Ioo hc (denseSeq ℝ≥0 n) t hb)

/-- The next actual large jump after a stopping time is a stopping time for an everywhere
cadlag adapted process in a right-continuous filtration. -/
theorem Adapted.isStoppingTime_nextLargeJump [F.IsRightContinuous] (hX : Adapted F X)
    (hc : ∀ ω, ProbabilityTheory.IsCadlagPath (X · ω)) (hb : 0 < b)
    (hσ : IsStoppingTime F σ) : IsStoppingTime F (ProbabilityTheory.nextLargeJump X b σ) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    (hX.measurableSet_nextLargeJump_lt hc hb hσ)

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpTimes
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps

/-! # Enumeration of actual positive-time large jumps

The sequence starts at the first large jump strictly after zero, not at a zero sentinel. Every
finite entry is an actual positive-time jump larger than the threshold; finite entries never
repeat. Once infinity occurs it may repeat. Compact local finiteness forces the sequence to
escape each finite horizon, and the minimality of `nextLargeJump` proves that no large jump is
skipped. Thus an everywhere cadlag adapted process has an actual stopping-time enumeration,
with totally inaccessible entries whenever its positive jumps have that source property.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The actual strict large jumps in increasing order, with infinity after exhaustion.
Index zero is already the first positive-time jump, not an initial-value sentinel. -/
noncomputable def largeJumpSequence (X : ℝ≥0 → Ω → ℝ) (b : ℝ) : ℕ → Ω → WithTop ℝ≥0
  | 0 => nextLargeJump X b (fun _ ↦ 0)
  | n + 1 => nextLargeJump X b (largeJumpSequence X b n)

@[simp] theorem largeJumpSequence_zero (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    largeJumpSequence X b 0 = nextLargeJump X b (fun _ ↦ 0) := rfl

@[simp] theorem largeJumpSequence_succ (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (n : ℕ) :
    largeJumpSequence X b (n + 1) = nextLargeJump X b (largeJumpSequence X b n) := rfl

variable {X : ℝ≥0 → Ω → ℝ} {b : ℝ} {ω : Ω}

theorem monotone_largeJumpSequence (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (ω : Ω) :
    Monotone (fun n ↦ largeJumpSequence X b n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_nextLargeJump

/-- Infinity persists after the actual large jumps have been exhausted. -/
theorem largeJumpSequence_eq_top_of_le {n m : ℕ} (hnm : n ≤ m)
    (hn : largeJumpSequence X b n ω = ⊤) : largeJumpSequence X b m ω = ⊤ := by
  apply top_unique
  rw [← hn]
  exact monotone_largeJumpSequence X b ω hnm

/-- Each finite indexed lifetime is an actual positive-time strict large jump. -/
theorem IsCadlagPath.largeJumpSequence_mem_of_eq_coe (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {n : ℕ} {t : ℝ≥0}
    (hn : largeJumpSequence X b n ω = (t : WithTop ℝ≥0)) :
    0 < t ∧ b < ‖jumpProcess X t ω‖ := by
  cases n with
  | zero =>
    have h := hX.nextLargeJump_mem_of_eq_coe hb hn
    exact ⟨WithTop.coe_lt_coe.mp h.1, h.2⟩
  | succ n =>
    have h := hX.nextLargeJump_mem_of_eq_coe hb hn
    have ht : ((0 : ℝ≥0) : WithTop ℝ≥0) < t := lt_of_le_of_lt bot_le h.1
    exact ⟨WithTop.coe_lt_coe.mp ht, h.2⟩

/-- A finite later entry is strictly greater than every earlier entry. Repeated infinity is
allowed and therefore excluded from the hypothesis. -/
theorem IsCadlagPath.largeJumpSequence_lt_of_lt_of_ne_top (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {n m : ℕ} (hnm : n < m) (hm : largeJumpSequence X b m ω ≠ ⊤) :
    largeJumpSequence X b n ω < largeJumpSequence X b m ω := by
  cases m with
  | zero => exact (Nat.not_lt_zero n hnm).elim
  | succ m =>
    have hstrict : largeJumpSequence X b m ω < largeJumpSequence X b (m + 1) ω :=
      hX.lt_nextLargeJump_of_ne_top hb hm
    exact (monotone_largeJumpSequence X b ω (Nat.le_of_lt_succ hnm)).trans_lt hstrict

/-- Equal finite lifetimes have equal indices; only infinity can be repeated. -/
theorem IsCadlagPath.largeJumpSequence_eq_iff_of_ne_top (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {n m : ℕ} (hm : largeJumpSequence X b m ω ≠ ⊤) :
    largeJumpSequence X b n ω = largeJumpSequence X b m ω ↔ n = m := by
  constructor
  · intro he
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · exact ((hX.largeJumpSequence_lt_of_lt_of_ne_top hb hnm hm).ne he).elim
    · exact hnm
    · have hn : largeJumpSequence X b n ω ≠ ⊤ := fun htop ↦ hm (he.symm.trans htop)
      exact ((hX.largeJumpSequence_lt_of_lt_of_ne_top hb hmn hn).ne he.symm).elim
  · rintro rfl
    rfl

/-- Some sequence entry lies strictly beyond each finite horizon. Otherwise its distinct
finite entries would inject the naturals into the finite set of actual large jumps
by that horizon. -/
theorem IsCadlagPath.exists_gt_largeJumpSequence (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (T : ℝ≥0) : ∃ n : ℕ, (T : WithTop ℝ≥0) < largeJumpSequence X b n ω := by
  by_contra hnone
  push Not at hnone
  have hfin (n : ℕ) : largeJumpSequence X b n ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hnone n)
  have hinj : Function.Injective (fun n ↦ largeJumpSequence X b n ω) := by
    intro n m hnm
    exact (hX.largeJumpSequence_eq_iff_of_ne_top hb (hfin m)).mp hnm
  have hB : (((↑) : ℝ≥0 → WithTop ℝ≥0) ''
      {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ b < ‖jumpProcess X t ω‖}).Finite :=
    (hX.finite_large_jumps_Ioc T hb).image _
  have hfinite : (range (fun n ↦ largeJumpSequence X b n ω)).Finite := by
    apply hB.subset
    rintro z ⟨n, rfl⟩
    cases hn : largeJumpSequence X b n ω with
    | top => exact (hfin n hn).elim
    | coe t =>
      have ht := hX.largeJumpSequence_mem_of_eq_coe hb hn
      refine ⟨t, ⟨ht.1, ?_, ht.2⟩, hn.symm⟩
      exact WithTop.coe_le_coe.mp (hn ▸ hnone n)
  exact (infinite_range_of_injective hinj) hfinite

/-- After finitely many indices, all remaining lifetimes lie beyond any fixed finite horizon. -/
theorem IsCadlagPath.eventually_gt_largeJumpSequence (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (T : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, (T : WithTop ℝ≥0) < largeJumpSequence X b n ω := by
  obtain ⟨N, hN⟩ := hX.exists_gt_largeJumpSequence hb T
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans_le (monotone_largeJumpSequence X b ω hn)

theorem IsCadlagPath.tendsto_largeJumpSequence_top (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) : Tendsto (fun n ↦ largeJumpSequence X b n ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  exact hX.eventually_gt_largeJumpSequence hb

/-- Every positive-time jump strictly larger than the threshold occurs in the sequence.
If a candidate were skipped, minimality of the next jump would keep all entries below it,
contradicting escape from compact intervals. -/
theorem IsCadlagPath.exists_largeJumpSequence_eq (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {t : ℝ≥0} (ht : 0 < t) (hj : b < ‖jumpProcess X t ω‖) :
    ∃ n : ℕ, largeJumpSequence X b n ω = (t : WithTop ℝ≥0) := by
  by_contra hnone
  push Not at hnone
  have hbound : ∀ n : ℕ, largeJumpSequence X b n ω ≤ (t : WithTop ℝ≥0) := by
    intro n
    induction n with
    | zero => exact nextLargeJump_le_of_jump (WithTop.coe_lt_coe.mpr ht) hj
    | succ n ih =>
      exact nextLargeJump_le_of_jump (lt_of_le_of_ne ih (hnone n)) hj
  obtain ⟨n, hn⟩ := hX.exists_gt_largeJumpSequence hb t
  exact (not_le_of_gt hn) (hbound n)

/-- Once entry `N` is past `T`, all large jumps by `T` appear among indices strictly below `N`. -/
theorem IsCadlagPath.largeJumpSequence_covers_Ioc_of_lt (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {N : ℕ} {T : ℝ≥0} (hN : (T : WithTop ℝ≥0) < largeJumpSequence X b N ω) :
    ∀ t : ℝ≥0, 0 < t → t ≤ T → b < ‖jumpProcess X t ω‖ →
      ∃ n : ℕ, n < N ∧ largeJumpSequence X b n ω = (t : WithTop ℝ≥0) := by
  intro t ht htT hj
  obtain ⟨n, hn⟩ := hX.exists_largeJumpSequence_eq hb ht hj
  refine ⟨n, ?_, hn⟩
  by_contra hnot
  have hle : largeJumpSequence X b N ω ≤ largeJumpSequence X b n ω :=
    monotone_largeJumpSequence X b ω (le_of_not_gt hnot)
  rw [hn] at hle
  exact (not_le_of_gt hN) (hle.trans (WithTop.coe_le_coe.mpr htT))

/-- The complete coverage event on a fixed compact interval eventually holds pointwise.
This is the pathwise finite-prefix statement needed before passing to tail probabilities. -/
theorem IsCadlagPath.eventually_largeJumpSequence_covers_Ioc (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (T : ℝ≥0) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ≥0, 0 < t → t ≤ T → b < ‖jumpProcess X t ω‖ →
      ∃ n : ℕ, n < N ∧ largeJumpSequence X b n ω = (t : WithTop ℝ≥0) :=
  (hX.eventually_gt_largeJumpSequence hb T).mono fun _ hN ↦
    hX.largeJumpSequence_covers_Ioc_of_lt hb hN

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- Every indexed actual large-jump lifetime is a stopping time. -/
theorem Adapted.isStoppingTime_largeJumpSequence [F.IsRightContinuous] (hX : Adapted F X)
    (hc : ∀ ω, ProbabilityTheory.IsCadlagPath (X · ω)) (hb : 0 < b) (n : ℕ) :
    IsStoppingTime F (ProbabilityTheory.largeJumpSequence X b n) := by
  induction n with
  | zero => exact hX.isStoppingTime_nextLargeJump hc hb (isStoppingTime_const F 0)
  | succ n ih => exact hX.isStoppingTime_nextLargeJump hc hb ih

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {b : ℝ}

/-- Under the source totally-inaccessible-jump hypothesis, every actual large-jump lifetime in
the constructed enumeration is totally inaccessible. -/
theorem HasTotallyInaccessibleJumps.isTotallyInaccessibleStoppingTime_largeJumpSequence
    [F.IsRightContinuous] (hJ : HasTotallyInaccessibleJumps F X P) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (n : ℕ) :
    IsTotallyInaccessibleStoppingTime F (largeJumpSequence X b n) P := by
  apply hJ.isTotallyInaccessibleStoppingTime_of_norm_jump_ge
    (hX.isStoppingTime_largeJumpSequence hc hb n) hb
  apply Eventually.of_forall
  intro ω hfin
  cases hn : largeJumpSequence X b n ω with
  | top => exact (hfin hn).elim
  | coe t =>
    have ht := (hc ω).largeJumpSequence_mem_of_eq_coe hb hn
    exact ⟨t, ht.1, rfl, ht.2.le⟩

end ProbabilityTheory

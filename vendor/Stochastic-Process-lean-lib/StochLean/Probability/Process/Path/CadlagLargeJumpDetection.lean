/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagShortWindow
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Instances.Rat

/-! # Detecting an actual cadlag jump on a countable grid

A strict large jump in an open time interval is equivalent to arbitrarily
short large increments on one compact internal interval. Both compact
endpoints and the increment samples can be taken from the fixed countable
dense grid; the increment threshold is rational and strictly above the
requested jump threshold. Compact short-window control proves the converse.

In particular this does not treat the generally discontinuous jump process
as a right-continuous process, and makes no stopping-time claim by itself.
-/

@[expose] public section

open Filter Set Metric TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

/-- Countably many short-increment tests on a fixed compact interval. -/
def HasArbitrarilyShortDenseIncrements (x : ℝ≥0 → ℝ) (a d : ℝ≥0) (c : ℝ) : Prop :=
  ∀ n : ℕ, ∃ i j : ℕ,
    a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧ denseSeq ℝ≥0 j ≤ d ∧
      dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ) ∧
        c < ‖x (denseSeq ℝ≥0 j) - x (denseSeq ℝ≥0 i)‖

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- Approximate both sides of a genuine positive-time jump on the dense grid. -/
theorem IsCadlagPath.exists_dense_increment_of_jump_gt (hX : IsCadlagPath (X · ω))
    {a u d : ℝ≥0} (hau : a < u) (hud : u < d) {c ε : ℝ}
    (hc : c < ‖jumpProcess X u ω‖) (hε : 0 < ε) :
    ∃ i j : ℕ,
      a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧ denseSeq ℝ≥0 j ≤ d ∧
        dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < ε ∧
          c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖ := by
  have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
  obtain ⟨l, _, hl, hlt⟩ := hD.exists_seq_strictMono_tendsto_of_lt hau
  obtain ⟨r, _, hr, hrt⟩ := hD.exists_seq_strictAnti_tendsto_of_lt hud
  have hlw : Tendsto l atTop (𝓝[<] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlt, Eventually.of_forall fun n ↦ (hl n).1.2⟩
  have hrw : Tendsto r atTop (𝓝[≥] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrt, Eventually.of_forall fun n ↦ (hr n).1.1.le⟩
  have hlX := (hX.tendsto_leftLimitProcess (ne_of_gt (lt_of_le_of_lt bot_le hau))).comp hlw
  have hrX := (hX.1 u).tendsto.comp hrw
  have hj : Tendsto (fun n ↦ ‖X (r n) ω - X (l n) ω‖) atTop
      (𝓝 ‖jumpProcess X u ω‖) := (hrX.sub hlX).norm
  have hd : Tendsto (fun n ↦ dist (l n) (r n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using hlt.dist hrt
  obtain ⟨n, hn, hn'⟩ := ((hj.eventually (Ioi_mem_nhds hc)).and
    (hd.eventually (Iio_mem_nhds hε))).exists
  obtain ⟨i, hi⟩ := (hl n).2
  obtain ⟨j, hj'⟩ := (hr n).2
  refine ⟨i, j, ?_⟩
  rw [hi, hj']
  exact ⟨(hl n).1.1.le, ((hl n).1.2.trans (hr n).1.1).le,
    (hr n).1.2.le, hn', hn⟩

/-- A countable characterization of a strict large jump in an open interval. -/
theorem IsCadlagPath.exists_large_jump_Ioo_iff_dense_increments
    (hX : IsCadlagPath (X · ω)) (s t : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    (∃ u : ℝ≥0, s < u ∧ u < t ∧ b < ‖jumpProcess X u ω‖) ↔
      ∃ c : ℚ, b < (c : ℝ) ∧ ∃ i j : ℕ,
        s < denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 j < t ∧
          HasArbitrarilyShortDenseIncrements (X · ω)
            (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) c := by
  constructor
  · rintro ⟨u, hsu, hut, hbu⟩
    obtain ⟨c, hbc, hcu⟩ := exists_rat_btwn hbu
    have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
    obtain ⟨a, haD, hsa, hau⟩ := hD.exists_between hsu
    obtain ⟨d, hdD, hud, hdt⟩ := hD.exists_between hut
    obtain ⟨i, rfl⟩ := haD
    obtain ⟨j, rfl⟩ := hdD
    refine ⟨c, hbc, i, j, hsa, hdt, fun n ↦ ?_⟩
    exact hX.exists_dense_increment_of_jump_gt hau hud hcu (by positivity)
  · rintro ⟨c, hbc, i, j, hsi, hjt, hshort⟩
    by_contra hno
    have hbound : ∀ u ∈ Icc (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j),
        0 < u → dist (X u ω) (Function.leftLim (X · ω) u) ≤ b := by
      intro u hu hu0
      have hjump : ‖jumpProcess X u ω‖ ≤ b := le_of_not_gt fun h ↦
        hno ⟨u, hsi.trans_le hu.1, hu.2.trans_lt hjt, h⟩
      simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg hu0.ne', dist_eq_norm]
        using hjump
    obtain ⟨δ, hδ, hmod⟩ := hX.exists_uniform_dist_lt_on_Icc_of_jump_bound
      (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) hb.le (sub_pos.mpr hbc) hbound
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨k, l, hik, hkl, hlj, hdist, hinc⟩ := hshort n
    have hsmall := hmod (denseSeq ℝ≥0 k) ⟨hik, hkl.trans hlj⟩
      (denseSeq ℝ≥0 l) ⟨hik.trans hkl, hlj⟩ (hdist.trans hn)
    have he : b + ((c : ℝ) - b) = c := by ring
    rw [he, dist_comm, dist_eq_norm] at hsmall
    exact (not_lt_of_ge hsmall.le) hinc

end ProbabilityTheory

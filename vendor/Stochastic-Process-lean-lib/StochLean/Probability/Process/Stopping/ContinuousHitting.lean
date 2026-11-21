/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Topology.Order.Compact
public import StochLean.Probability.Process.Path.Supremum

/-! # Continuous-path hitting times

These results use Mathlib's `hittingAfter`, not a second hitting-time definition.
Closed targets are attained when the hitting time is finite. For real processes,
compact maxima and a countable dense grid give measurable closed-level hitting times.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E]

theorem hittingAfter_mem_of_continuous {X : ℝ≥0 → Ω → E} {s : Set E}
    {a : ℝ≥0} {ω : Ω} (hX : Continuous (X · ω)) (hs : IsClosed s)
    (hne : hittingAfter X s a ω ≠ ⊤) :
    X (hittingAfter X s a ω).untopA ω ∈ s := by
  classical
  have hex : ∃ t, a ≤ t ∧ X t ω ∈ s := by
    simpa only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not, exists_prop] using hne
  have hc : IsClosed {t : ℝ≥0 | a ≤ t ∧ X t ω ∈ s} :=
    isClosed_Ici.inter (hs.preimage hX)
  have hm := hc.csInf_mem hex (bddBelow_Ici.inter_of_left)
  rw [hittingAfter, if_pos hex]
  exact hm.2

theorem hittingAfter_le_iff_of_continuous {X : ℝ≥0 → Ω → E} {s : Set E}
    {a T : ℝ≥0} {ω : Ω} (hX : Continuous (X · ω)) (hs : IsClosed s) :
    hittingAfter X s a ω ≤ T ↔ ∃ t ∈ Icc a T, X t ω ∈ s := by
  constructor
  · intro h
    have hne : hittingAfter X s a ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
    have hlow := le_hittingAfter (u := X) (s := s) (n := a) ω
    have hm := hittingAfter_mem_of_continuous hX hs hne
    refine ⟨(hittingAfter X s a ω).untopA, ⟨?_, WithTop.untopA_le h⟩, hm⟩
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_le_coe.mp ((WithTop.coe_untop _ hne).symm ▸ hlow)
  · rintro ⟨t, ht, hm⟩
    exact (hittingAfter_le_of_mem ht.1 hm).trans (WithTop.coe_le_coe.mpr ht.2)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

/-- The countable supremum of a continuous nonnegative path is its attained compact maximum.
This non-strict bridge is needed for hitting a closed level, including level zero. -/
theorem le_denseRunningSupremum_iff_exists_of_continuous
    {T : ℝ≥0} {a : ℝ} {ω : Ω} (hX : Continuous (X · ω))
    (hpos : ∀ t, 0 ≤ X t ω) :
    ENNReal.ofReal a ≤ denseRunningSupremum X T ω ↔ ∃ t ≤ T, a ≤ X t ω := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ T)) hX.continuousOn
  have heq : denseRunningSupremum X T ω = ENNReal.ofReal (X t ω) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (hmax ⟨bot_le, min_le_left _ _⟩)
    · exact ofReal_le_denseRunningSupremum_of_rightContinuous ht.2
        (fun _ ↦ hX.continuousWithinAt)
  rw [heq]
  constructor
  · intro h
    exact ⟨t, ht.2, (ENNReal.ofReal_le_ofReal_iff (hpos t)).mp h⟩
  · rintro ⟨u, hu, ha⟩
    exact ENNReal.ofReal_le_ofReal (ha.trans (hmax ⟨bot_le, hu⟩))

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

/-- Continuous adapted paths have stopping times at closed absolute-value thresholds. -/
theorem Adapted.isStoppingTime_hittingAfter_abs (hX : Adapted F X)
    (hc : ∀ ω, Continuous (X · ω)) (a : ℝ) :
    IsStoppingTime F (hittingAfter X {x | a ≤ |x|} 0) := by
  intro T
  have hs : IsClosed {x : ℝ | a ≤ |x|} := isClosed_le continuous_const continuous_abs
  have heq : {ω | hittingAfter X {x | a ≤ |x|} 0 ω ≤ T} =
      {ω | ENNReal.ofReal a ≤
        ProbabilityTheory.denseRunningSupremum (fun t ω ↦ |X t ω|) T ω} := by
    ext ω
    rw [mem_ofPred_eq, hittingAfter_le_iff_of_continuous (hc ω) hs,
      mem_ofPred_eq, ProbabilityTheory.le_denseRunningSupremum_iff_exists_of_continuous
        (hc ω).abs (fun t ↦ abs_nonneg (X t ω))]
    simp only [mem_Icc, mem_ofPred_eq, zero_le, true_and]
  rw [heq]
  apply measurableSet_le measurable_const
  apply Measurable.iSup
  intro n
  exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    ((hX (ProbabilityTheory.denseTimeUpTo T n)).mono (F.mono (min_le_left _ _)) le_rfl))

/-- Continuity prevents overshoot at first passage, provided the initial value is in the bound. -/
theorem abs_le_of_le_hittingAfter {a : ℝ} {ω : Ω} (hc : Continuous (X · ω))
    (hzero : |X 0 ω| ≤ a) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X {x | a ≤ |x|} 0 ω) : |X t ω| ≤ a := by
  by_cases hz : t = 0
  · simpa only [hz] using hzero
  have hpos : 0 < t := bot_lt_iff_ne_bot.mpr hz
  have hcl : t ∈ closure (Iio t) := by
    rw [closure_Iio' (a := t) ⟨(0 : ℝ≥0), hpos⟩]
    exact mem_Iic.mpr (le_refl t)
  apply closure_minimal (s := Iio t) (t := {u | |X u ω| ≤ a}) ?_
    (isClosed_le hc.abs continuous_const) hcl
  intro u hu
  change |X u ω| ≤ a
  exact (lt_of_not_ge (notMem_of_lt_hittingAfter (u := X) (s := {x | a ≤ |x|})
    ((WithTop.coe_lt_coe.mpr hu).trans_le ht) bot_le)).le

theorem abs_stoppedProcess_hittingAfter_le {a : ℝ} {ω : Ω}
    (hc : Continuous (X · ω)) (hzero : |X 0 ω| ≤ a) (t : ℝ≥0) :
    |stoppedProcess X (hittingAfter X {x | a ≤ |x|} 0) t ω| ≤ a := by
  apply abs_le_of_le_hittingAfter hc hzero
  have hne : min (t : WithTop ℝ≥0) (hittingAfter X {x | a ≤ |x|} 0 ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  exact min_le_right _ _

/-- Increasing the threshold delays first passage. -/
theorem hittingAfter_abs_mono {ω : Ω} (hc : Continuous (X · ω)) :
    Monotone (fun a : ℝ ↦ hittingAfter X {x | a ≤ |x|} 0 ω) := by
  intro a b hab
  change hittingAfter X {x | a ≤ |x|} 0 ω ≤ hittingAfter X {x | b ≤ |x|} 0 ω
  by_cases hb : hittingAfter X {x | b ≤ |x|} 0 ω = ⊤
  · rw [hb]
    exact le_top
  have hm := hittingAfter_mem_of_continuous hc
    (isClosed_le continuous_const continuous_abs) hb
  have hle := hittingAfter_le_of_mem (u := X) (s := {x | a ≤ |x|}) bot_le (hab.trans hm)
  rwa [WithTop.untopA_eq_untop hb, WithTop.coe_untop] at hle

/-- A continuous path is bounded on every compact interval, so its integer-level hitting
times tend to infinity. No uniform bound in the sample point is assumed. -/
theorem tendsto_hittingAfter_abs_nat {ω : Ω} (hc : Continuous (X · ω)) :
    Tendsto (fun n : ℕ ↦ hittingAfter X {x | (n : ℝ) ≤ |x|} 0 ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨t, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ T)) hc.abs.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt |X t ω|
  filter_upwards [eventually_ge_atTop N] with n hn
  apply lt_of_not_ge
  intro hle
  obtain ⟨u, hu, hm⟩ := (hittingAfter_le_iff_of_continuous hc
    (isClosed_le continuous_const continuous_abs)).mp hle
  exact (not_le.mpr hN) ((Nat.cast_le.mpr hn).trans (hm.trans (hmax hu)))

end MeasureTheory

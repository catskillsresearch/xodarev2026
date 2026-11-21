/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Delay

/-! # Positive delays are predictable

A deterministic strictly positive delay of any stopping time has an explicit
announcing sequence. Capping the original time at each integer is essential
at infinity: simply adding smaller delays to infinity would not announce it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem isAnnouncingSequence_add_const (hτ : IsStoppingTime F τ) (P : Measure Ω)
    {c : ℝ≥0} (hc : 0 < c) :
    IsAnnouncingSequence F P (fun ω ↦ τ ω + (c : WithTop ℝ≥0))
      (fun n ω ↦ min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) +
        ((c - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : WithTop ℝ≥0)) := by
  refine ⟨fun n ↦ (hτ.min (isStoppingTime_const F (n : ℝ≥0))).add_const_nnreal _,
    fun ω i j hij ↦ ?_, fun n ω _ ↦ ?_, Eventually.of_forall fun ω ↦ ?_⟩
  · exact add_le_add (min_le_min le_rfl (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hij)))
      ((isAnnouncingSequence_const F P c).monotone ω hij)
  · cases ht : τ ω with
    | top =>
      rw [min_top_left, WithTop.top_add, ← WithTop.coe_add]
      exact WithTop.coe_lt_top _
    | coe s =>
      rw [← WithTop.coe_min, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe]
      exact add_lt_add_of_le_of_lt (min_le_left _ _) (tsub_lt_self hc (by positivity))
  · have hn : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) atTop (𝓝 ⊤) :=
      WithTop.tendsto_coe_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
    have hg : Tendsto (fun n : ℕ ↦ c - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 c) := by
      simpa only [tsub_zero] using
        tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    cases ht : τ ω with
    | top =>
      rw [WithTop.top_add]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hn tendsto_const_nhds
      · intro n
        change ((n : ℝ≥0) : WithTop ℝ≥0) ≤ min ⊤ ((n : ℝ≥0) : WithTop ℝ≥0) +
          ((c - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : WithTop ℝ≥0)
        rw [min_top_left]
        exact le_add_of_nonneg_right bot_le
      · exact fun _ ↦ le_top
    | coe s =>
      rw [← WithTop.coe_add]
      have hsum := WithTop.continuous_coe.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := s)).add hg)
      apply hsum.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually
        (eventually_ge_atTop s)] with n hn
      rw [min_eq_left (WithTop.coe_le_coe.mpr hn), ← WithTop.coe_add]
      rfl

theorem isPredictableStoppingTime_add_const (hτ : IsStoppingTime F τ) (P : Measure Ω)
    {c : ℝ≥0} (hc : 0 < c) :
    IsPredictableStoppingTime F (fun ω ↦ τ ω + (c : WithTop ℝ≥0)) P :=
  (hτ.isAnnouncingSequence_add_const P hc).predictable (hτ.add_const_nnreal c)

end MeasureTheory.IsStoppingTime

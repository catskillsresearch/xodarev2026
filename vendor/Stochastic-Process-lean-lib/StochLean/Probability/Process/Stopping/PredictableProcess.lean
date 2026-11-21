/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PredictableValue
public import StochLean.Probability.Process.Measurability.Predictable

/-! # Stopping preserves the original predictable process

The map (t, omega) to (t minimum tau(omega), omega) is measurable for the
existing predictable sigma field on both sides. Its generator inverse images
use information available at the deterministic generator time. In particular,
the stopping time need not itself be predictable.

Composition therefore preserves strong predictability exactly, without path
regularity, a measure, usual conditions, integrability or an exceptional-set
replacement. The clock is always finite because it is bounded by t, including
when the stopping lifetime is infinite. At lifetime zero the original initial
value is retained. No implicit infinite-time value is introduced.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

/-- The actual finite stopping map preserves the predictable sigma field.
An arbitrary stopping time, not a predictable stopping time, suffices. -/
theorem IsStoppingTime.measurable_predictable_stopping_pair (hτ : IsStoppingTime F τ) :
    @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) F.predictable F.predictable
      (fun p ↦ ((min (p.1 : WithTop ℝ≥0) (τ p.2)).untopA, p.2)) := by
  classical
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) _
    (MeasurableSpace.generateFrom _) _
  apply measurable_generateFrom
  rintro _ (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
  · have hm0 : MeasurableSet[F 0] {ω | τ ω = 0} := by
      convert hτ 0 using 1
      ext ω
      exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h bot_le⟩
    have hAI : MeasurableSet[F 0] (A ∩ {ω | τ ω = 0}) := hA.inter hm0
    have hu : MeasurableSet[F.predictable]
        ((univ : Set ℝ≥0) ×ˢ (A ∩ {ω | τ ω = 0})) := by
      have hconst : Adapted F (fun _ : ℝ≥0 ↦ (A ∩ {ω | τ ω = 0}).indicator
          (fun _ : Ω ↦ (1 : ℝ))) := fun t ↦
        measurable_const.indicator (F.mono bot_le _ hAI)
      have hp := hconst.isStronglyPredictable_of_leftContinuous
        (fun _ _ ↦ continuousWithinAt_const)
      convert (hp.measurable (measurableSet_singleton (1 : ℝ))) using 1
      ext ⟨t, ω⟩
      simp only [mem_prod, mem_univ, true_and, mem_preimage, mem_singleton_iff]
      by_cases h : ω ∈ A ∩ {ω | τ ω = 0} <;> simp [Function.uncurry, h]
    convert (measurableSet_predictable_singleton_bot_prod hA).union hu using 1
    ext ⟨t, ω⟩
    simp only [mem_preimage, mem_prod, mem_singleton_iff, NNReal.bot_eq_zero,
      mem_union, mem_univ, true_and, mem_inter_iff, mem_ofPred_eq]
    have hfin : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have he : (min (t : WithTop ℝ≥0) (τ ω)).untopA = 0 ↔ t = 0 ∨ τ ω = 0 := by
      rw [← le_zero_iff, WithTop.untopA_le_iff hfin, min_le_iff]
      change ((t : WithTop ℝ≥0) ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) ∨ τ ω ≤ 0) ↔
        t = 0 ∨ τ ω = 0
      rw [WithTop.coe_le_coe, le_zero_iff, le_zero_iff]
    rw [he]
    tauto
  · have hm : MeasurableSet[F s] (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}) :=
      hA.inter (by simpa only [compl_ofPred, not_le] using (hτ s).compl)
    convert measurableSet_predictable_Ioi_prod (𝓕 := F) hm using 1
    ext ⟨t, ω⟩
    simp only [mem_preimage, mem_prod, mem_Ioi, mem_inter_iff, mem_ofPred_eq]
    have hfin : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    rw [WithTop.lt_untopA_iff hfin, lt_min_iff, WithTop.coe_lt_coe]
    tauto

/-- Strong predictability is preserved by actual stopping, including zero
and infinite lifetimes, with no regularity or measure assumptions. -/
theorem IsStronglyPredictable.stoppedProcess {E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} (hX : IsStronglyPredictable F X) (hτ : IsStoppingTime F τ) :
    IsStronglyPredictable F (stoppedProcess X τ) :=
  hX.comp_measurable hτ.measurable_predictable_stopping_pair

end MeasureTheory

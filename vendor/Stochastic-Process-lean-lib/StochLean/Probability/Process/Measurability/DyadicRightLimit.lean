/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.DyadicRightLimit
public import StochLean.Probability.Process.Filtration.Usual
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Adaptedness of the actual dyadic right-limit extension

Limits along skeleton sequences inside (t,u) are measurable in every F_u.
Filtration right continuity yields F_t measurability. Under usual conditions,
the common exceptional path event can be reset and then restored by completion.
No modification identity or expectation continuity is assumed.
-/

@[expose] public section

open StochLean MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem Adapted.dyadicRightLimitProcess_of_rightLimits [F.IsRightContinuous]
    (ha : Adapted F X)
    (hr : ∀ ω t, ∃ z : ℝ,
      Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) :
    Adapted F (ProbabilityTheory.dyadicRightLimitProcess X) := by
  intro t
  have hu (u : ℝ≥0) (htu : t < u) :
      Measurable[F u] (ProbabilityTheory.dyadicRightLimitProcess X t) := by
    obtain ⟨v, _, hv, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto_of_lt htu
    have hvlim : Tendsto v atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hl, Eventually.of_forall fun n ↦ ⟨(hv n).2, (hv n).1.1⟩⟩
    let : MeasurableSpace Ω := F u
    change Measurable (fun ω ↦ ProbabilityTheory.dyadicRightLimitProcess X t ω)
    exact measurable_of_tendsto_metrizable
      (fun n ↦ (ha (v n)).mono (F.mono (hv n).1.2.le) le_rfl)
      (tendsto_pi_nhds.mpr fun ω ↦ (tendsto_dyadicRightLimitProcess (hr ω t)).comp hvlim)
  intro s hs
  apply Filtration.IsRightContinuous.measurableSet (𝓕 := F)
  rw [F.rightCont_eq]
  exact MeasurableSpace.measurableSet_iInf.mpr fun u ↦
    MeasurableSpace.measurableSet_iInf.mpr fun htu ↦ hu u htu hs

theorem Adapted.dyadicRightLimitProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hr : ∀ᵐ ω ∂P, ∀ t, ∃ z : ℝ,
      Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) :
    Adapted F (ProbabilityTheory.dyadicRightLimitProcess X) := by
  classical
  let bad := {ω | ¬ ∀ t, ∃ z : ℝ,
    Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hr)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hYr (ω) (t) : ∃ z : ℝ,
      Tendsto (fun s ↦ Y s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z) := by
    by_cases hb : ω ∈ bad
    · exact ⟨0, by simpa only [Y, if_pos hb] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 ↦ (0 : ℝ))
          (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 0))⟩
    · simpa only [Y, if_neg hb] using (not_not.mp hb : ∀ t, ∃ z : ℝ,
        Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) t
  have hXY : Indistinguishable X Y P := by
    filter_upwards [hr] with ω hω t
    exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm
  let : F.IsRightContinuous := hF.rightContinuous
  have hYad := hYa.dyadicRightLimitProcess_of_rightLimits hYr
  intro t
  have hc : IsCompleteSubMeasurableSpace P (F t) :=
    fun A hA ↦ F.mono bot_le A (hF.complete_initial A hA)
  exact hc.measurable_congr_ae (hYad t)
    ((hXY.dyadicRightLimitProcess.symm).mono fun _ hω ↦ hω t)

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightLimit
public import StochLean.Probability.Process.Filtration.Usual
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Order.IsLUB

/-! # Adaptedness of a caglad process's right-limit process

The right limit at `t` is measurable in every `F_u`, `u > t`, by actual sequences
inside `(t,u)`. Right continuity of the filtration then gives `F_t` measurability.
Usual completeness transports the statement on one common exceptional path event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem Adapted.rightLimitProcess_of_rightLimits [F.IsRightContinuous]
    (ha : Adapted F X)
    (hr : ∀ ω t, ∃ y : ℝ, Tendsto (X · ω) (𝓝[>] t) (𝓝 y)) :
    Adapted F (ProbabilityTheory.rightLimitProcess X) := by
  intro t
  have hu (u : ℝ≥0) (htu : t < u) : Measurable[F u] (ProbabilityTheory.rightLimitProcess X t) := by
    obtain ⟨v, _, hv, hlim⟩ := exists_seq_strictAnti_tendsto' htu
    have hvlim : Tendsto v atTop (𝓝[>] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n ↦ (hv n).1⟩
    let : MeasurableSpace Ω := F u
    change Measurable (fun ω ↦ ProbabilityTheory.rightLimitProcess X t ω)
    exact measurable_of_tendsto_metrizable
      (fun n ↦ (ha (v n)).mono (F.mono (hv n).2.le) le_rfl)
      (tendsto_pi_nhds.mpr fun ω ↦ (tendsto_rightLim_of_tendsto (hr ω t)).comp hvlim)
  intro s hs
  apply Filtration.IsRightContinuous.measurableSet (𝓕 := F)
  rw [F.rightCont_eq]
  exact MeasurableSpace.measurableSet_iInf.mpr fun u ↦
    MeasurableSpace.measurableSet_iInf.mpr fun htu ↦ hu u htu hs

theorem Adapted.rightLimitProcess_of_caglad [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCagladPath (X · ω)) :
    Adapted F (ProbabilityTheory.rightLimitProcess X) :=
  ha.rightLimitProcess_of_rightLimits fun ω ↦ (hc ω).2

theorem Adapted.rightLimitProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCagladPaths X P) : Adapted F (ProbabilityTheory.rightLimitProcess X) := by
  classical
  let bad := {ω | ¬ IsCagladPath (X · ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hYc : ∀ ω, IsCagladPath (Y · ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using
        (IsContinuousPath.isCagladPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
    · simpa only [Y, if_neg hb] using (not_not.mp hb : IsCagladPath (X · ω))
  have hXY : Indistinguishable X Y P := by
    filter_upwards [hc] with ω hω t
    exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm
  let : F.IsRightContinuous := hF.rightContinuous
  have hright := hYa.rightLimitProcess_of_caglad hYc
  intro t
  have hcomplete : IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hcomplete.measurable_congr_ae (hright t)
    ((hXY.rightLimitProcess.symm).mono (fun _ hω ↦ hω t))

end MeasureTheory

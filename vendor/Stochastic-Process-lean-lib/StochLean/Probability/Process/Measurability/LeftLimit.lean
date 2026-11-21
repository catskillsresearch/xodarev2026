/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.Probability.Process.Measurability.Progressive
public import Mathlib.Topology.Order.IsLUB

/-! # Adaptedness of the source left-limit and jump processes -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Only source times strictly below the target time are used for the limit. -/
theorem Adapted.leftLimitProcess_of_cadlag (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.leftLimitProcess X) := by
  intro t
  by_cases ht : t = 0
  · subst t
    rw [leftLimitProcess_zero]
    exact measurable_const
  obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr ht)
  have hlu : Tendsto u atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n ↦ (hu n).2)⟩
  let : MeasurableSpace Ω := F t
  change Measurable (fun ω ↦ ProbabilityTheory.leftLimitProcess X t ω)
  exact measurable_of_tendsto_metrizable
    (fun n ↦ (ha (u n)).mono (F.mono (hu n).2.le) le_rfl)
    (tendsto_pi_nhds.mpr (fun ω ↦ ((hc ω).tendsto_leftLimitProcess ht).comp hlu))

/-- A single exceptional path event is removed at time zero and then restored by
relative completeness. No uncountable intersection of coordinatewise events is used. -/
theorem Adapted.leftLimitProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.leftLimitProcess X) := by
  classical
  let bad := {ω | ¬ IsCadlagPath (fun t ↦ X t ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hYc : ∀ ω, IsCadlagPath (fun t ↦ Y t ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using
        (IsContinuousPath.isCadlagPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
    · simpa only [Y, if_neg hb] using (not_not.mp hb : IsCadlagPath (fun t ↦ X t ω))
  have hXY : Indistinguishable X Y P := by
    filter_upwards [hc] with ω hω t
    exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm
  have hleft := hYa.leftLimitProcess_of_cadlag hYc
  intro t
  have hcomplete : IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hcomplete.measurable_congr_ae (hleft t)
    ((hXY.leftLimitProcess.symm).mono (fun _ hω ↦ hω t))

theorem Adapted.jumpProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.jumpProcess X) := by
  intro t
  exact (ha t).sub (ha.leftLimitProcess_of_usual hF hc t)

end MeasureTheory

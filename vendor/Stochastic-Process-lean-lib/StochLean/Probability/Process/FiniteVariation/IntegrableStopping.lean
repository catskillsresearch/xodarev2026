/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integrable
public import StochLean.Probability.Process.FiniteVariation.TerminalStopping
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual

/-! # Stopping and masking integrable variation

Stopping retains the endpoint and does not increase actual total variation.
Usual cadlag adaptedness supplies measurability of the stopped path's total
variation; domination alone would not supply it. The local-property mask at
zero does not affect variation, because a process stopped at zero is constant.
This last statement does not require the initial value to vanish or be integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem HasIntegrableVariation.stoppedProcess (hX : HasIntegrableVariation X P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    HasIntegrableVariation (stoppedProcess X τ) P := by
  have hs : Adapted F (MeasureTheory.stoppedProcess X τ) :=
    (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hτ).adapted
  refine ⟨hX.1.stoppedProcess τ, hX.2.mono' ?_ ?_⟩
  · exact ((hs.measurable_eVariationOn_univ_of_usual hF
      (hc.stoppedProcess τ)).ennreal_toReal).aestronglyMeasurable
  · filter_upwards [hX.1] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hω (eVariationOn_univ_stoppedProcess_le X τ ω)

/-- A measurable sample event can mask a process without losing integrable variation. -/
theorem HasIntegrableVariation.indicator (hX : HasIntegrableVariation X P)
    {s : Set Ω} (hs : MeasurableSet s) :
    HasIntegrableVariation (fun t ↦ s.indicator (X t)) P := by
  classical
  have he : (fun ω ↦ eVariationOn (fun t ↦ s.indicator (X t) ω) univ) =
      s.indicator (fun ω ↦ eVariationOn (X · ω) univ) := by
    funext ω
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω]
      exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self 0
  constructor
  · filter_upwards [hX.1] with ω hω
    change eVariationOn (fun t ↦ s.indicator (X t) ω) univ ≠ ∞
    rw [congrFun he ω]
    by_cases hmem : ω ∈ s
    · simpa only [BoundedVariationOn, Set.indicator_of_mem hmem] using hω
    · rw [Set.indicator_of_notMem hmem]
      exact ENNReal.zero_ne_top
  · apply (hX.2.indicator hs).congr
    exact Filter.Eventually.of_forall fun ω ↦ by
      change s.indicator (fun ω ↦ (eVariationOn (X · ω) univ).toReal) ω =
        (eVariationOn (fun t ↦ s.indicator (X t) ω) univ).toReal
      rw [congrFun he ω]
      by_cases hω : ω ∈ s
      · simp only [Set.indicator_of_mem hω]
      · simp only [Set.indicator_of_notMem hω, ENNReal.toReal_zero]

/-- At a zero lifetime both paths are constant, so the local-property mask
does not change their extended variation. At every other lifetime it is absent. -/
theorem eVariationOn_univ_stoppedProcess_indicator_pos (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eVariationOn (fun t ↦ stoppedProcess
      (fun s ↦ {ω | 0 < τ ω}.indicator (X s)) τ t ω) univ =
      eVariationOn (fun t ↦ stoppedProcess X τ t ω) univ := by
  classical
  by_cases hpos : 0 < τ ω
  · have hmem : ω ∈ {ω | 0 < τ ω} := hpos
    simp only [MeasureTheory.stoppedProcess, Set.indicator_of_mem hmem]
  · have ht : τ ω = 0 := le_antisymm (le_of_not_gt hpos) bot_le
    have hconst (c : ℝ) : eVariationOn (fun _ : ℝ≥0 ↦ c) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self c
    have he (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
        stoppedProcess Y τ t ω = Y (τ ω).untopA ω :=
      stoppedProcess_eq_of_ge (u := Y) (τ := τ) (i := t) (ω := ω)
        (ht ▸ WithTop.coe_le_coe.mpr (bot_le : (0 : ℝ≥0) ≤ t))
    rw [eVariationOn.congr (fun t _ ↦ he (fun s ↦ {ω | 0 < τ ω}.indicator (X s)) t),
      eVariationOn.congr (fun t _ ↦ he X t), hconst, hconst]

theorem hasIntegrableVariation_stoppedProcess_indicator_pos_iff
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    HasIntegrableVariation (stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) P ↔
      HasIntegrableVariation (stoppedProcess X τ) P := by
  simp only [HasIntegrableVariation, HasFiniteTotalVariationPaths, BoundedVariationOn,
    eVariationOn_univ_stoppedProcess_indicator_pos]

end ProbabilityTheory

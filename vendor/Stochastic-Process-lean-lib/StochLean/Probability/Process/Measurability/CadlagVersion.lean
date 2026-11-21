/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.Progressive

/-! # Everywhere-cadlag indistinguishable versions under usual conditions -/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set TopologicalSpace
open scoped NNReal

namespace MeasureTheory

theorem StronglyAdapted.exists_cadlag_indistinguishable_of_usual
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (ha : StronglyAdapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, IsCadlagPath (fun t ↦ Y t ω) := by
  classical
  let bad := {ω | ¬ IsCadlagPath (fun t ↦ X t ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : StronglyAdapted F Y := fun t ↦
    StronglyMeasurable.ite (F.mono bot_le _ hbad) stronglyMeasurable_const (ha t)
  have hYc : ∀ ω, IsCadlagPath (fun t ↦ Y t ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simp only [Y, if_pos hb]
      exact IsContinuousPath.isCadlagPath continuous_const
    · simpa only [Y, if_neg hb] using (not_not.mp hb : IsCadlagPath (fun t ↦ X t ω))
  refine ⟨Y, ?_, hYa.isStronglyProgressive_of_rightContinuous (fun ω ↦ (hYc ω).1), hYc⟩
  filter_upwards [hc] with ω hω t
  exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm

end MeasureTheory

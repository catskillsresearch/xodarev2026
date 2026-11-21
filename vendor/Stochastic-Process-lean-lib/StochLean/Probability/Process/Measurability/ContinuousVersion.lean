/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.Progressive

/-! # Everywhere-continuous indistinguishable versions

Relative completeness makes the single exceptional path event measurable at time zero.
The constructed version is zero there; no joint regularity of the original exceptional paths
is claimed. This version permits continuous-path first-passage constructions.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set TopologicalSpace
open scoped NNReal

namespace MeasureTheory

theorem StronglyAdapted.exists_continuous_indistinguishable_of_usual
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, Continuous (Y · ω) := by
  classical
  let bad := {ω | ¬ Continuous (X · ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have ha : StronglyAdapted F Y := fun t ↦
    StronglyMeasurable.ite (F.mono bot_le bad hbad) stronglyMeasurable_const (hX t)
  have hY : ∀ ω, Continuous (Y · ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : E)))
    · have hcont : Continuous (X · ω) := not_not.mp hb
      simpa only [Y, if_neg hb] using hcont
  refine ⟨Y, ?_, ha.isStronglyProgressive_of_rightContinuous
    (fun ω _ ↦ (hY ω).continuousWithinAt), hY⟩
  filter_upwards [hc] with ω hω t
  exact (if_neg (show ω ∉ bad from fun h ↦ h hω)).symm

end MeasureTheory

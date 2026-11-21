/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Caglad
public import StochLean.Probability.Process.Filtration.Usual
public import Mathlib.Probability.Process.Adapted

/-! # Everywhere-caglad indistinguishable adapted versions

The single exceptional path event is reset at time zero using usual completeness.
The original initial value is retained on the common full-measure event.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

theorem Adapted.exists_caglad_indistinguishable_of_usual
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [MeasurableSpace E] [Zero E] {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : Adapted F X) (hF : F.IsUsual P) (hc : HasCagladPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, Indistinguishable X Y P ∧ Adapted F Y ∧
      ∀ ω, IsCagladPath (Y · ω) := by
  classical
  let bad := {ω | ¬ IsCagladPath (X · ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  refine ⟨Y, ?_, fun t ↦
    Measurable.ite (F.mono bot_le bad hbad) measurable_const (hX t), ?_⟩
  · filter_upwards [hc] with ω hω t
    exact (if_neg (show ω ∉ bad from fun h ↦ h hω)).symm
  · intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using
        (IsContinuousPath.isCagladPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : E))))
    · simpa only [Y, if_neg hb] using (not_not.mp hb : IsCagladPath (X · ω))

end MeasureTheory

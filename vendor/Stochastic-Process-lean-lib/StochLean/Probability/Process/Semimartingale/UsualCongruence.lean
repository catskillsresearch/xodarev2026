/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Localization
public import StochLean.Probability.Process.Semimartingale.Stability
public import StochLean.Probability.Process.Filtration.Usual

/-! # Indistinguishable versions under usual conditions

Relative completeness supplies adaptedness of the target version, even
when its exceptional null path set was not initially measurable.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.congr_of_usual
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hXY : Indistinguishable X Y P) :
    IsSemimartingale Y F P := by
  apply hX.congr_of_adapted hXY
  intro t
  have hc : IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hc.measurable_congr_ae (hX.adapted t) (hXY.mono (fun _ h ↦ h t))

end ProbabilityTheory

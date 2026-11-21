/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-! # Continuous real-linear maps preserve martingales -/

@[expose] public section

namespace MeasureTheory

theorem Martingale.continuousLinearMap {Ω ι E G : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ι mΩ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {X : ι → Ω → E} (hX : Martingale X F P) (L : E →L[ℝ] G) :
    Martingale (fun t ω ↦ L (X t ω)) F P := by
  refine ⟨fun t ↦ L.continuous.comp_stronglyMeasurable (hX.stronglyAdapted t), ?_⟩
  intro s t hst
  filter_upwards [L.comp_condExp_comm (m := F s) (hX.integrable t), hX.condExp_ae_eq hst]
    with ω hL hM
  exact hL.symm.trans (congrArg L hM)

end MeasureTheory

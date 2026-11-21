/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Complex

/-! # Real linear functionals commute with source complex left limits

Unlike arbitrary continuous transformations, a linear functional preserves
zero, so the equality includes time zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem IsCadlagPath.leftLimitProcess_realLinear_complex {Ω : Type*}
    {Z : ℝ≥0 → Ω → ℂ} {ω : Ω} (hZ : IsCadlagPath (Z · ω))
    (L : ℂ →L[ℝ] ℝ) (t : ℝ≥0) :
    leftLimitProcess (fun s v ↦ L (Z s v)) t ω = L (complexLeftLimitProcess Z t ω) := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLimitProcess_zero, complexLeftLimitProcess_zero, Pi.zero_apply, map_zero]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht,
      hZ.complexLeftLimitProcess_eq_leftLim (pos_iff_ne_zero.mpr ht)]
    exact leftLim_eq_of_tendsto (L.continuous.continuousAt.tendsto.comp
      (tendsto_leftLim_of_tendsto (hZ.2 t ht)))

theorem HasCadlagPaths.leftLimitProcess_realLinear_complex {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : ℝ≥0 → Ω → ℂ}
    (hZ : HasCadlagPaths Z P) (L : ℂ →L[ℝ] ℝ) :
    Indistinguishable (leftLimitProcess (fun t ω ↦ L (Z t ω)))
      (fun t ω ↦ L (complexLeftLimitProcess Z t ω)) P :=
  hZ.mono (fun _ hz t ↦ hz.leftLimitProcess_realLinear_complex L t)

end ProbabilityTheory

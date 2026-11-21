/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimitOperations
public import StochLean.Probability.Process.Path.Multiplication

/-! # Multiplication of source left limits

Both source left limits vanish at zero, so multiplication commutes with the
left-limit operation at every time, not only at positive times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.leftLimitProcess_mul (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    leftLimitProcess (X * Y) t ω = leftLimitProcess X t ω * leftLimitProcess Y t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, mul_zero]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto
      ((hX.tendsto_leftLimitProcess ht).mul (hY.tendsto_leftLimitProcess ht))

theorem HasCadlagPaths.leftLimitProcess_mul {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) :
    Indistinguishable (leftLimitProcess (X * Y))
      (leftLimitProcess X * leftLimitProcess Y) P := by
  filter_upwards [hX, hY] with ω hx hy t
  exact hx.leftLimitProcess_mul hy t

end ProbabilityTheory

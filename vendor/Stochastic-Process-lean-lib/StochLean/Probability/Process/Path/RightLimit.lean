/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.ForMathlib.Topology.Order.RightLimitLeft
public import Mathlib.Topology.Order.DenselyOrdered

/-! # The right-limit process of a caglad input

Mathlib owns the strict-right-limit selector. Its limit and reconstruction identities
are proved on the caglad path domain. In general `H_(0+)` differs from `H_0`, so this
transformation is not a modification and does not normalize or overwrite the source initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def rightLimitProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Function.rightLim (fun s ↦ X s ω) t

theorem IsCagladPath.tendsto_rightLimitProcess {ω : Ω} (hX : IsCagladPath (X · ω))
    (t : ℝ≥0) : Tendsto (X · ω) (𝓝[>] t) (𝓝 (rightLimitProcess X t ω)) :=
  tendsto_rightLim_of_tendsto (hX.2 t)

theorem IsCagladPath.tendsto_rightLimitProcess_nhdsLT {ω : Ω}
    (hX : IsCagladPath (X · ω)) (t : ℝ≥0) :
    Tendsto (rightLimitProcess X · ω) (𝓝[<] t) (𝓝 (X t ω)) :=
  (hX.1 t).tendsto_rightLim_nhdsLT

theorem IsCagladPath.isCadlagPath_rightLimitProcess {ω : Ω}
    (hX : IsCagladPath (X · ω)) : IsCadlagPath (rightLimitProcess X · ω) := by
  constructor
  · intro t
    exact continuousWithinAt_rightLim_Ici (hX.tendsto_rightLimitProcess t)
  · intro t _
    exact ⟨X t ω, hX.tendsto_rightLimitProcess_nhdsLT t⟩

theorem IsCagladPath.leftLimitProcess_rightLimitProcess {ω : Ω}
    (hX : IsCagladPath (X · ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    leftLimitProcess (rightLimitProcess X) t ω = X t ω := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
  simp only [leftLimitProcess, if_neg ht]
  exact leftLim_eq_of_tendsto (hX.tendsto_rightLimitProcess_nhdsLT t)

theorem IsCagladPath.reconstruct_from_rightLimit {ω : Ω}
    (hX : IsCagladPath (X · ω)) (t : ℝ≥0) :
    X t ω = if t = 0 then X 0 ω else leftLimitProcess (rightLimitProcess X) t ω := by
  by_cases ht : t = 0
  · simp only [ht, if_true]
  · rw [if_neg ht, hX.leftLimitProcess_rightLimitProcess ht]

theorem IsRightContinuousPath.rightLimitProcess_eq {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) (t : ℝ≥0) : rightLimitProcess X t ω = X t ω :=
  (hX t).rightLim_eq

theorem HasCagladPaths.hasCadlagPaths_rightLimitProcess (hX : HasCagladPaths X P) :
    HasCadlagPaths (rightLimitProcess X) P :=
  hX.mono fun _ hω ↦ hω.isCadlagPath_rightLimitProcess

theorem Indistinguishable.rightLimitProcess (hXY : Indistinguishable X Y P) :
    Indistinguishable (rightLimitProcess X) (rightLimitProcess Y) P := by
  filter_upwards [hXY] with ω hω t
  simp only [ProbabilityTheory.rightLimitProcess, hω]

end ProbabilityTheory

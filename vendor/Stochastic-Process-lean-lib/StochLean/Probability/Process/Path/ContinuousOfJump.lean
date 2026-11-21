/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit

/-! # A cadlag path is continuous exactly when its positive-time jumps vanish

The source jump at zero is the initial value, so it must not be included in
the zero-jump hypothesis. No initial normalization is imposed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.continuous_of_jumpProcess_eq_zero (hX : IsCadlagPath (X · ω))
    (hj : ∀ t : ℝ≥0, t ≠ 0 → jumpProcess X t ω = 0) : IsContinuousPath (X · ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    apply (hX.1 0).continuousAt
    rw [show Ici (0 : ℝ≥0) = univ from Ici_bot]
    exact Filter.univ_mem
  · apply continuousAt_iff_continuous_left'_right'.mpr
    refine ⟨?_, (hX.1 t).mono Ioi_subset_Ici_self⟩
    have heq : leftLimitProcess X t ω = X t ω := (sub_eq_zero.mp (hj t ht)).symm
    change Tendsto (X · ω) (𝓝[<] t) (𝓝 (X t ω))
    rw [← heq]
    exact hX.tendsto_leftLimitProcess ht

theorem IsCadlagPath.continuous_iff_jumpProcess_eq_zero (hX : IsCadlagPath (X · ω)) :
    IsContinuousPath (X · ω) ↔ ∀ t : ℝ≥0, t ≠ 0 → jumpProcess X t ω = 0 :=
  ⟨fun h _ ht ↦ h.jumpProcess_eq_zero ht, hX.continuous_of_jumpProcess_eq_zero⟩

theorem HasCadlagPaths.hasContinuousPaths_of_jumpProcess_eq_zero
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} (hX : HasCadlagPaths X P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 → jumpProcess X t ω = 0) :
    HasContinuousPaths X P := by
  filter_upwards [hX, hj] with ω hx hj
  exact hx.continuous_of_jumpProcess_eq_zero hj

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.CanonicalDecomposition
public import StochLean.Probability.Process.Semimartingale.BoundedJumpSpecial

/-! # Jump bounds for the actual canonical parts

The actual III.35 construction is identified with the canonical selectors by
predictable FV uniqueness. Its variation integrability and positive-time jump
bounds therefore hold for the canonical parts, not only an existential pair.
The canonical martingale retains the original initial value, whose jump at
zero is deliberately excluded from the bounds.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- The canonical predictable part has locally integrable variation and
inherits the source positive-jump bound; the canonical martingale's bound
is twice as large. No initial moment or proposed canonical property is used. -/
theorem IsSpecialSemimartingale.canonicalParts_of_jump_bound
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) (hC : 0 ≤ C)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C) :
    HasLocallyIntegrableVariation hX.canonicalFiniteVariationPart F P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
        ‖jumpProcess hX.canonicalFiniteVariationPart t ω‖ ≤ C ∧
        ‖jumpProcess hX.canonicalMartingalePart t ω‖ ≤ 2 * C := by
  obtain ⟨L, A, hL, hpA, _, _, hA0, hvA, he, hbound⟩ :=
    hX.isClassicalSemimartingale.exists_predictable_decomposition_of_jump_bound hF hC hj
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  have hI : IsContinuousLocalMartingale I F P :=
    isContinuousLocalMartingale_const_initial (hX.1 0)
  have hu := hX.canonicalDecomposition_unique hF (hI.1.add hL hF) hpA
    hvA.hasFiniteVariationPaths (Eventually.of_forall (fun ω ↦ congrFun hA0 ω))
    (Eventually.of_forall (fun ω t ↦ congrFun (congrFun he t) ω))
  refine ⟨hvA.congr hu.2.symm, ?_⟩
  filter_upwards [hu.1.jumpProcess, hu.2.jumpProcess, hL.2.1, hbound]
    with ω hm ha hcL hb t ht
  rw [hm t, ha t]
  have hcI : IsContinuousPath (I · ω) := continuous_const
  have hjI : jumpProcess I t ω = 0 := hcI.jumpProcess_eq_zero (ne_of_gt ht)
  rw [hcI.isCadlagPath.jumpProcess_add hcL t, hjI, zero_add]
  exact hb t ht

end ProbabilityTheory

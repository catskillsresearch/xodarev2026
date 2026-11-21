/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LargeJumpLocal
public import StochLean.Probability.Martingale.Doob.CompensatedJumpBoundLocal
public import StochLean.Probability.Process.LocalMartingale.BoundedJumpLocalization
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableAlgebra

/-! # Protter III.29: the actual fundamental decomposition

For a positive threshold, take the existing actual sum of the large
positive-time jumps and construct its predictable local compensator. Their
difference is a local martingale of locally integrable variation. Subtracting
that difference from the original local martingale leaves positive-time jumps
bounded by twice the threshold. The existing bounded-jump localization then
supplies the native locally square-integrable martingale property.

The decomposition is an exact equality of the constructed original processes,
not just an equality of selected versions. The finite-variation local martingale
starts at exactly zero; the bounded-jump component retains the arbitrary
original initial random value. Its square-integrable localization uses the
existing initial-event masks, not an unproved moment condition at time zero.

No semimartingale hypothesis, proposed decomposition, new localization
predicate, or compensator selector is introduced. Jumps of norm exactly equal
to the threshold remain in the small-jump part, as required by the strict
large-jump convention of the existing cumulative process.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- Every cadlag local martingale is the exact sum of a bounded-jump,
locally square-integrable local martingale and a zero-initial local martingale
of locally integrable variation. No initial moment is required. -/
theorem IsLocalMartingale.exists_fundamental_decomposition_of_pos
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) {β : ℝ} (hb : 0 < β) :
    ∃ N D : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale N F P ∧ IsLocalMartingale D F P ∧
      D 0 = 0 ∧ N 0 = M 0 ∧ HasLocallyIntegrableVariation D F P ∧
      M = N + D ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess N t ω‖ ≤ 2 * β) ∧
      Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F N P := by
  let A := largeJumpSumProcess M β
  have hvA : HasLocallyIntegrableVariation A F P :=
    (hM.hasLocallyIntegrableVariation_largeJumpSumProcesses hF hb).1
  have haA : Adapted F A :=
    (hM.1.stronglyAdapted_largeJumpSumProcesses_of_usual hF hM.2.1 hb).1.adapted
  have hcA : HasCadlagPaths A P :=
    (hM.2.1.largeJumpSumProcesses_properties hb).1
  have hA0 : A 0 = 0 := (largeJumpSumProcesses_initial M β).1
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (M - A) t ω‖ ≤ β :=
    hM.2.1.norm_jump_sub_largeJumpSumProcess_le hb
  obtain ⟨B, hpB, hcB, hB0, hvB, hD, hN, hj⟩ :=
    hM.exists_predictable_compensator_with_residual_jump_bound
      hF hvA haA hcA β hb.le hR
  let N := (M - A) + B
  let D := A - B
  have hvD : HasLocallyIntegrableVariation D F P :=
    hvA.sub hvB haA hpB.stronglyAdapted.adapted hF hcA (Eventually.of_forall hcB)
  have hD0 : D 0 = 0 := by
    change A 0 - B 0 = 0
    rw [hA0, hB0, sub_self]
  have hN0 : N 0 = M 0 := by
    change M 0 - A 0 + B 0 = M 0
    rw [hA0, hB0, sub_zero, add_zero]
  have he : M = N + D := by
    funext t ω
    change M t ω = (M t ω - A t ω + B t ω) + (A t ω - B t ω)
    ring
  have hjN : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess N t ω‖ ≤ 2 * β :=
    hj.mono fun _ hω t ht ↦ (hω t ht).2
  exact ⟨N, D, hN, hD, hD0, hN0, hvD, he, hjN,
    hN.locally_squareIntegrableMartingale_of_jump_bound hF (by positivity) hjN⟩

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousBounded
public import StochLean.Probability.Martingale.Doob.ContinuousUniqueness

/-! # Comparing actual continuous compensators

When the difference of two processes is itself a bounded cadlag
supermartingale with totally inaccessible positive-time jumps, the bounded
existence theorem constructs its continuous increasing compensator. Uniqueness
identifies that compensator with the difference of the two given continuous
compensators. Pointwise ordering of the original processes alone is not a
sufficient hypothesis and is not used as a substitute.

The expectation identity below separately requires integrability of both
summands. Integrability of their sum is not used to infer this incorrectly.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y A B : ℝ≥0 → Ω → ℝ} {N : ℝ}

section Comparison

variable [IsProbabilityMeasure P]

/-- A bounded supermartingale difference forces the difference of its two
continuous finite-variation compensators to be increasing. The compensator
of the difference is constructed by the bounded existence theorem. -/
theorem Supermartingale.hasMonotonePaths_sub_continuous_compensators
    (hD : Supermartingale (Y - X) F P) (hF : F.IsUsual P)
    (hcD : HasCadlagPaths (Y - X) P)
    (hJ : HasTotallyInaccessibleJumps F (Y - X) P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖(Y - X) t ω‖ ≤ N)
    (hMA : Martingale (X + A) F P) (hMB : Martingale (Y + B) F P)
    (hcA : HasContinuousPaths A P) (hcB : HasContinuousPaths B P)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0) :
    HasMonotonePaths (B - A) P := by
  obtain ⟨C, _, _, _, hcC, hC0, hmC, hvC, _, _, hMC, _, _, _, _⟩ :=
    hD.exists_continuous_doob_decomposition_of_bound hF hcD hJ hN hbound
  have he : (Y - X) + (B - A) = (Y + B) - (X + A) := by
    funext t ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hMD : Martingale ((Y - X) + (B - A)) F P := by
    rw [he]
    exact hMB.sub hMA
  have hcBA : HasContinuousPaths (B - A) P := by
    filter_upwards [hcB, hcA] with ω hb ha
    exact Continuous.sub hb ha
  have hvBA : HasFiniteVariationPaths (B - A) P := by
    filter_upwards [hvB, hvA] with ω hb ha
    exact locallyBoundedVariationOn_sub hb ha
  have hBA0 : (B - A) 0 =ᵐ[P] 0 := by
    filter_upwards [hB0, hA0] with ω hb ha
    change B 0 ω - A 0 ω = 0
    rw [hb, ha]
    exact sub_self _
  have hi : Indistinguishable C (B - A) P :=
    indistinguishable_of_continuous_finiteVariation_martingale_add_zero hF hMC hMD
      (Eventually.of_forall hcC) hcBA hvC hvBA
      (Eventually.of_forall fun ω ↦ congrFun hC0 ω) hBA0
  exact hmC.congr hi

/-- Zero initial compensators are ordered on one common full-measure event
under the supermartingale-difference hypothesis, not merely under `X ≤ Y`. -/
theorem Supermartingale.ae_forall_le_continuous_compensators
    (hD : Supermartingale (Y - X) F P) (hF : F.IsUsual P)
    (hcD : HasCadlagPaths (Y - X) P)
    (hJ : HasTotallyInaccessibleJumps F (Y - X) P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖(Y - X) t ω‖ ≤ N)
    (hMA : Martingale (X + A) F P) (hMB : Martingale (Y + B) F P)
    (hcA : HasContinuousPaths A P) (hcB : HasContinuousPaths B P)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ∀ t, A t ω ≤ B t ω := by
  have hm := hD.hasMonotonePaths_sub_continuous_compensators hF hcD hJ hN hbound
    hMA hMB hcA hcB hvA hvB hA0 hB0
  filter_upwards [hm, hA0, hB0] with ω hmω ha hb t
  have h := hmω (bot_le : (0 : ℝ≥0) ≤ t)
  change B 0 ω - A 0 ω ≤ B t ω - A t ω at h
  rw [ha, hb] at h
  linarith

end Comparison

section Expectation

variable [IsFiniteMeasure P]

/-- The compensator expectation follows from the true martingale identity
and separate integrability of the original value and compensator value.
Neither continuity nor monotonicity is needed for this algebraic identity. -/
theorem Martingale.integral_add_compensator_eq
    (hM : Martingale (X + A) F P) (hA0 : A 0 =ᵐ[P] 0) (t : ℝ≥0)
    (hXt : Integrable (X t) P) (hAt : Integrable (A t) P) :
    (∫ ω, A t ω ∂P) = (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P := by
  have he0 : X 0 + A 0 =ᵐ[P] X 0 := by
    filter_upwards [hA0] with ω hω
    change X 0 ω + A 0 ω = X 0 ω
    rw [hω]
    exact add_zero _
  have h := hM.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t)
    (@MeasurableSet.univ Ω (F 0))
  rw [setIntegral_univ, setIntegral_univ] at h
  change (∫ ω, (X 0 + A 0) ω ∂P) = ∫ ω, (X t + A t) ω ∂P at h
  rw [integral_congr_ae he0] at h
  change (∫ ω, X 0 ω ∂P) = ∫ ω, X t ω + A t ω ∂P at h
  rw [integral_add hXt hAt] at h
  linarith

end Expectation

end MeasureTheory

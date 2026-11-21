/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Yoeurp
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Constants

/-! # The original initial product cannot be declared integrable by Yoeurp

The first source is the genuine constant-one UI martingale. The second is
an arbitrary initial-field-measurable random constant, hence predictable
with actual variation zero. The new centered UI theorem applies with budget
zero, but the raw bracket cannot be UI if that random constant is not L1.
All brackets in this regression are the actual canonical raw process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace StochLean.SemimartingaleRegression

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ}

/-- Zero variation of the predictable source does not impose an L1
condition on the raw initial product. The centered conclusion remains UI. -/
theorem yoeurp_arbitrary_initial_constant (hF : F.IsUsual P) (hZ : Measurable[F 0] Z) :
    let hM := isSemimartingale_const_initial (F := F) (P := P)
      (measurable_const (a := (1 : ℝ)))
    let hA := isSemimartingale_const_initial (P := P) hZ
    IsLocalMartingale (hM.quadraticCovariation hA hF) F P ∧
      IsUIMartingale (hM.quadraticCovariation hA hF - fun _ ↦ Z) F P ∧
      Indistinguishable (hM.quadraticCovariation hA hF) (fun _ ↦ Z) P ∧
      (¬ Integrable Z P → ¬ IsUIMartingale (hM.quadraticCovariation hA hF) F P) := by
  let M : ℝ≥0 → Ω → ℝ := fun _ _ ↦ 1
  let A : ℝ≥0 → Ω → ℝ := fun _ ↦ Z
  have hM : IsUIMartingale M F P :=
    ⟨martingale_const F P 1,
      uniformIntegrable_const le_rfl (by simp) (memLp_const (1 : ℝ))⟩
  have hcM : HasCadlagPaths M P :=
    (show HasContinuousPaths M P from Eventually.of_forall fun _ ↦ continuous_const).hasCadlagPaths
  have hcA : HasCadlagPaths A P :=
    (show HasContinuousPaths A P from Eventually.of_forall fun _ ↦ continuous_const).hasCadlagPaths
  have haA : Adapted F A := fun _ ↦ hZ.mono (F.mono bot_le) le_rfl
  have hpA : IsStronglyPredictable F A :=
    haA.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  have hvA : HasFiniteVariationPaths A P := (hasIntegrableVariation_const Z).hasFiniteVariationPaths
  have hbA : ∀ᵐ ω ∂P, eVariationOn (A · ω) Set.univ ≤ ENNReal.ofReal 0 := by
    filter_upwards with ω
    rw [ENNReal.ofReal_zero]
    exact le_of_eq ((eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self (Z ω))
  have hraw := hpA.isLocalMartingale_quadraticCovariation hF hcA hvA (hM.isLocalMartingale hcM)
  have hcenter := hpA.isUIMartingale_centered_quadraticCovariation_of_variation_bound
    hF hcA hvA 0 le_rfl hbA hM hcM
  let hSM := isSemimartingale_const_initial (F := F) (P := P)
    (measurable_const (a := (1 : ℝ)))
  have he : Indistinguishable
      (hSM.quadraticCovariation (isSemimartingale_const_initial hZ) hF) (fun _ ↦ Z) P := by
    simpa only [one_mul] using hSM.quadraticCovariation_const_initial_right hZ hF
  refine ⟨hraw, ?_, he, ?_⟩
  · simpa only [M, one_mul] using hcenter
  · intro hn hu
    exact hn ((hu.1.integrable 0).congr (he.ae_eq 0))

end StochLean.SemimartingaleRegression

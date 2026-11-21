/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.CanonicalDecomposition
public import StochLean.Probability.Process.Semimartingale.ContinuousSpecial

/-! # Continuous canonical parts and the arbitrary-initial-value safeguard

The actual continuous predictable decomposition is identified with the existing
canonical parts by their proved uniqueness. The source canonical martingale
includes the original constant initial random value, which remains continuous
without any integrability assumption.

An arbitrary initially measurable random constant is constructed as a special
semimartingale through the existing actual local-martingale and continuous
decomposition theorems. Canonical uniqueness, not reduction of a selector,
identifies its canonical parts with the original constant and zero. A
nonintegrable initial value rules out a true UI canonical martingale.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

/-- The actual canonical parts of a continuous special semimartingale are
continuous on common full-measure path events, including the original initial value. -/
theorem IsSpecialSemimartingale.canonicalParts_hasContinuousPaths
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    HasContinuousPaths hX.canonicalMartingalePart P ∧
      HasContinuousPaths hX.canonicalFiniteVariationPart P := by
  obtain ⟨L, A, hL, hpA, hcontA, _, _, hA0, hvA, he⟩ :=
    hX.isClassicalSemimartingale.exists_continuous_predictable_decomposition hF hc
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  have hI : IsContinuousLocalMartingale I F P :=
    isContinuousLocalMartingale_const_initial (hX.1 0)
  have hcont : HasContinuousPaths (I + L) P := by
    filter_upwards [hI.2, hL.2] with ω hi hl
    exact hi.add hl
  have hu := hX.canonicalDecomposition_unique hF (hI.1.add hL.1 hF) hpA
    hvA.hasFiniteVariationPaths (Eventually.of_forall fun ω ↦ congrFun hA0 ω)
    (Eventually.of_forall fun ω t ↦ congrFun (congrFun he t) ω)
  exact ⟨HasContinuousPaths.congr hu.1.symm hcont,
    HasContinuousPaths.congr hu.2.symm hcontA⟩

/-- Actual canonical regression for an arbitrary initially measurable random
constant. Nonintegrability of that constant prevents its canonical local
martingale from being a true UI martingale; specialness still holds. -/
theorem exists_special_const_initial_canonicalParts (hF : F.IsUsual P)
    (hZ : Measurable[F 0] Z) :
    ∃ hX : IsSpecialSemimartingale (fun _ : ℝ≥0 ↦ Z) F P,
      Indistinguishable hX.canonicalMartingalePart (fun _ : ℝ≥0 ↦ Z) P ∧
      Indistinguishable hX.canonicalFiniteVariationPart 0 P ∧
      (¬ Integrable Z P → ¬ IsUIMartingale hX.canonicalMartingalePart F P) := by
  have hI : IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ Z) F P :=
    isContinuousLocalMartingale_const_initial hZ
  have hX : IsSpecialSemimartingale (fun _ : ℝ≥0 ↦ Z) F P :=
    (hI.1.isClassicalSemimartingale hF).isSpecialSemimartingale_of_continuous hF hI.2
  have hp0 : IsStronglyPredictable F (0 : ℝ≥0 → Ω → ℝ) := stronglyMeasurable_const
  have hz : (0 : ℝ≥0 → Ω → ℝ) 0 =ᵐ[P] 0 := Eventually.of_forall fun _ ↦ rfl
  have he : Indistinguishable (fun _ : ℝ≥0 ↦ Z) ((fun _ : ℝ≥0 ↦ Z) + 0) P := by
    filter_upwards with ω t
    simp only [Pi.add_apply, Pi.zero_apply, add_zero]
  have hu := hX.canonicalDecomposition_unique hF hI.1 hp0
    hasIntegrableVariation_zero.hasFiniteVariationPaths hz he
  refine ⟨hX, hu.1, hu.2, ?_⟩
  intro hn hUI
  exact hn ((hUI.1.integrable 0).congr (hu.1.mono fun _ hω ↦ hω 0))

end ProbabilityTheory

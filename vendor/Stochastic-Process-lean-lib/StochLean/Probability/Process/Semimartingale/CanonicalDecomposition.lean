/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Special

/-! # The canonical parts of a special semimartingale

These are the unique source canonical parts, selected only on the proved special
domain. The martingale part includes the original initial random value, as in
Protter's unnormalized canonical decomposition; the predictable FV part starts
at zero almost surely. Thus `X = M + A` up to indistinguishability, with
`M 0 = X 0`, even when the initial value has no first moment.

Uniqueness is proved against arbitrary predictable FV competitors, not only
other selected pairs. Indistinguishable inputs have indistinguishable parts.
There is no fallback outside the special domain, no second compensator owner,
and no change to the original good-integrator semimartingale predicate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The predictable part of the actual special decomposition. -/
noncomputable def IsSpecialSemimartingale.canonicalFiniteVariationPart
    (hX : IsSpecialSemimartingale X F P) : ℝ≥0 → Ω → ℝ :=
  hX.2.2.choose_spec.choose

/-- The source canonical local-martingale part retains the original initial
random value, rather than discarding it or assuming it integrable. -/
noncomputable def IsSpecialSemimartingale.canonicalMartingalePart
    (hX : IsSpecialSemimartingale X F P) : ℝ≥0 → Ω → ℝ :=
  (fun _ ↦ X 0) + hX.2.2.choose

variable [IsProbabilityMeasure P]

/-- All canonical properties refer to the selected raw processes; the
reconstruction and normalization use the source almost-sure semantics. -/
theorem IsSpecialSemimartingale.canonicalDecomposition_properties
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) :
    IsLocalMartingale hX.canonicalMartingalePart F P ∧
      IsStronglyPredictable F hX.canonicalFiniteVariationPart ∧
      HasCadlagPaths hX.canonicalFiniteVariationPart P ∧
      HasFiniteVariationPaths hX.canonicalFiniteVariationPart P ∧
      hX.canonicalMartingalePart 0 =ᵐ[P] X 0 ∧
      hX.canonicalFiniteVariationPart 0 =ᵐ[P] 0 ∧
      Indistinguishable X (hX.canonicalMartingalePart + hX.canonicalFiniteVariationPart) P := by
  obtain ⟨hM, hpA, hcA, hvA, hM0, hA0, he⟩ := hX.2.2.choose_spec.choose_spec
  have hI := (isContinuousLocalMartingale_const_initial (P := P) (hX.1 0)).1
  refine ⟨hI.add hM hF, hpA, hcA, hvA, ?_, hA0, he⟩
  filter_upwards [hM0] with ω hω
  change X 0 ω + hX.2.2.choose 0 ω = X 0 ω
  rw [hω, Pi.zero_apply, add_zero]

/-- Uniqueness against every source competitor. No integrable-variation,
cadlag, or martingale-initial-value premise is added for the competing pair. -/
theorem IsSpecialSemimartingale.canonicalDecomposition_unique
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P)
    {N B : ℝ≥0 → Ω → ℝ} (hN : IsLocalMartingale N F P)
    (hpB : IsStronglyPredictable F B) (hvB : HasFiniteVariationPaths B P)
    (hB0 : B 0 =ᵐ[P] 0) (he : Indistinguishable X (N + B) P) :
    Indistinguishable hX.canonicalMartingalePart N P ∧
      Indistinguishable hX.canonicalFiniteVariationPart B P := by
  obtain ⟨hM, hpA, _, hvA, _, hA0, heA⟩ := hX.canonicalDecomposition_properties hF
  have hu := indistinguishable_parts_of_predictable_finiteVariation_decomposition
    hF hM hN hpA hpB hvA hvB (hA0.trans hB0.symm) (heA.symm.trans he)
  exact ⟨hu.2, hu.1⟩

/-- Canonical parts depend only on the indistinguishability class, not on
which raw representative or specialness proof is used. -/
theorem IsSpecialSemimartingale.canonicalParts_congr
    (hX : IsSpecialSemimartingale X F P) (hY : IsSpecialSemimartingale Y F P)
    (hF : F.IsUsual P) (he : Indistinguishable X Y P) :
    Indistinguishable hX.canonicalMartingalePart hY.canonicalMartingalePart P ∧
      Indistinguishable hX.canonicalFiniteVariationPart hY.canonicalFiniteVariationPart P := by
  obtain ⟨hN, hpB, _, hvB, _, hB0, heB⟩ := hY.canonicalDecomposition_properties hF
  exact hX.canonicalDecomposition_unique hF hN hpB hvB hB0 (he.trans heB)

end ProbabilityTheory

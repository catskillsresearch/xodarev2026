/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.PredictableFiniteVariation
public import StochLean.Probability.Process.LocalMartingale.Congr
public import StochLean.ForMathlib.VariationAlgebra

/-! # Uniqueness of predictable FV local-martingale decompositions

The difference of two predictable finite-variation parts is a predictable FV
local martingale. The proved III.15 constancy theorem gives uniqueness once
their initial values agree. No existence theorem, local integrability of
variation, or integrability of initial values is assumed here.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M N A B X : ℝ≥0 → Ω → ℝ}

/-- Both parts of an actual predictable FV local-martingale decomposition
are unique up to indistinguishability when the FV initial values agree. -/
theorem indistinguishable_parts_of_predictable_finiteVariation_decomposition
    (hF : F.IsUsual P) (hM : IsLocalMartingale M F P) (hN : IsLocalMartingale N F P)
    (hpA : IsStronglyPredictable F A) (hpB : IsStronglyPredictable F B)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (h0 : A 0 =ᵐ[P] B 0) (he : Indistinguishable (M + A) (N + B) P) :
    Indistinguishable A B P ∧ Indistinguishable M N P := by
  have hdiff : Indistinguishable (M - N) (B - A) P := by
    filter_upwards [he] with ω hω t
    have ht := hω t
    simp only [Pi.add_apply] at ht
    change M t ω - N t ω = B t ω - A t ω
    linarith only [ht]
  have hp : IsStronglyPredictable F (B - A) := hpB.sub hpA
  have hlocal : IsLocalMartingale (B - A) F P :=
    (hM.sub hN hF).congr hF hp.stronglyAdapted.adapted hdiff
  have hv : HasFiniteVariationPaths (B - A) P := by
    filter_upwards [hvA, hvB] with ω ha hb
    exact locallyBoundedVariationOn_sub hb ha
  have hz : (B - A) 0 =ᵐ[P] 0 := by
    filter_upwards [h0] with ω hω
    exact sub_eq_zero.mpr hω.symm
  have hzero := hlocal.indistinguishable_zero_of_predictable_finiteVariation hF hp hv hz
  have hAB : Indistinguishable A B P := by
    filter_upwards [hzero] with ω hω t
    exact (sub_eq_zero.mp (hω t)).symm
  refine ⟨hAB, ?_⟩
  filter_upwards [he, hAB] with ω heω hABω t
  have ht := heω t
  simp only [Pi.add_apply, hABω t] at ht
  exact add_right_cancel ht

/-- Predictable FV compensating parts of the same local martingale problem
are unique. Continuity of the compensating parts is not a premise. -/
theorem indistinguishable_of_predictable_finiteVariation_localMartingale_add
    (hF : F.IsUsual P) (hMA : IsLocalMartingale (X + A) F P)
    (hMB : IsLocalMartingale (X + B) F P)
    (hpA : IsStronglyPredictable F A) (hpB : IsStronglyPredictable F B)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (h0 : A 0 =ᵐ[P] B 0) : Indistinguishable A B P := by
  have he : (X + A) - (X + B) = A - B := by
    funext t ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hlocal : IsLocalMartingale (A - B) F P := by
    rw [← he]
    exact hMA.sub hMB hF
  have hv : HasFiniteVariationPaths (A - B) P := by
    filter_upwards [hvA, hvB] with ω ha hb
    exact locallyBoundedVariationOn_sub ha hb
  have hz : (A - B) 0 =ᵐ[P] 0 := by
    filter_upwards [h0] with ω hω
    exact sub_eq_zero.mpr hω
  have hzero := hlocal.indistinguishable_zero_of_predictable_finiteVariation
    hF (hpA.sub hpB) hv hz
  filter_upwards [hzero] with ω hω t
  exact sub_eq_zero.mp (hω t)

end ProbabilityTheory

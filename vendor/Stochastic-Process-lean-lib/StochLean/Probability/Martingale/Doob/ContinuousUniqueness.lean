/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.ContinuousFiniteVariation
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import StochLean.ForMathlib.VariationAlgebra

/-! # Uniqueness of continuous finite-variation martingale compensators

If adding either of two continuous, locally finite-variation processes to the
same process produces a martingale, their difference is a continuous
finite-variation martingale. The existing local-martingale constancy theorem
therefore gives uniqueness whenever their initial values agree.

No boundedness, supermartingale hypothesis, or decomposition structure is used.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
  {X A B : ℝ≥0 → Ω → ℝ}

/-- Continuous finite-variation martingale compensators of the same process
are indistinguishable if their initial values agree almost surely. -/
theorem indistinguishable_of_continuous_finiteVariation_martingale_add
    (hF : F.IsUsual P) (hMA : Martingale (X + A) F P)
    (hMB : Martingale (X + B) F P)
    (hcA : HasContinuousPaths A P) (hcB : HasContinuousPaths B P)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (h0 : A 0 =ᵐ[P] B 0) : Indistinguishable A B P := by
  have he : (X + A) - (X + B) = A - B := by
    funext t ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hM : Martingale (A - B) F P := by
    rw [← he]
    exact hMA.sub hMB
  have hc : HasContinuousPaths (A - B) P := by
    filter_upwards [hcA, hcB] with ω ha hb
    exact Continuous.sub ha hb
  have hv : HasFiniteVariationPaths (A - B) P := by
    filter_upwards [hvA, hvB] with ω ha hb
    exact locallyBoundedVariationOn_sub ha hb
  have hz : (A - B) 0 =ᵐ[P] 0 := by
    filter_upwards [h0] with ω hω
    exact sub_eq_zero.mpr hω
  have hzero := (hM.isContinuousLocalMartingale hc).indistinguishable_zero_of_finiteVariation
    hF hv hz
  filter_upwards [hzero] with ω hω t
  exact sub_eq_zero.mp (hω t)

/-- In particular, zero-initial continuous finite-variation martingale
compensators are unique up to indistinguishability. -/
theorem indistinguishable_of_continuous_finiteVariation_martingale_add_zero
    (hF : F.IsUsual P) (hMA : Martingale (X + A) F P)
    (hMB : Martingale (X + B) F P)
    (hcA : HasContinuousPaths A P) (hcB : HasContinuousPaths B P)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0) :
    Indistinguishable A B P :=
  indistinguishable_of_continuous_finiteVariation_martingale_add
    hF hMA hMB hcA hcB hvA hvB (hA0.trans hB0.symm)

end ProbabilityTheory

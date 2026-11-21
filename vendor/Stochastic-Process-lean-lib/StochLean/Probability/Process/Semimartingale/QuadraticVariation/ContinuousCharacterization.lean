/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.ContinuousFiniteVariation
public import StochLean.Probability.Process.LocalMartingale.Congr
public import StochLean.ForMathlib.VariationAlgebra

/-! # Characterization of the canonical continuous local-martingale bracket

A continuous adapted finite-variation process with the correct initial square
and a local-martingale square residual equals the existing raw bracket. This
is a uniqueness theorem, not a second bracket construction.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.quadraticVariation_eq_of_sq_sub_localMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X A : ℝ≥0 → Ω → ℝ}
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F A) (hc : HasContinuousPaths A P) (hv : HasFiniteVariationPaths A P)
    (hM : IsLocalMartingale ((fun t ω ↦ X t ω ^ 2) - A) F P)
    (h0 : A 0 =ᵐ[P] fun ω ↦ X 0 ω ^ 2) :
    Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF) A P := by
  let hSM := hX.isSemimartingale hF
  let Q := hSM.quadraticVariation hF
  have he : Indistinguishable
      (((fun t ω ↦ X t ω ^ 2) - A) - ((fun t ω ↦ X t ω ^ 2) - Q)) (Q - A) P := by
    apply Filter.Eventually.of_forall
    intro ω t
    simp only [Pi.sub_apply]
    ring
  have hD : IsLocalMartingale (Q - A) F P :=
    (hM.sub (hX.isContinuousLocalMartingale_sq_sub_quadraticVariation hF).1 hF).congr
      hF (fun t ↦ (hSM.adapted_quadraticVariation hF t).sub (ha t)) he
  have hDc : HasContinuousPaths (Q - A) P := by
    filter_upwards [hX.hasContinuousPaths_quadraticVariation hF, hc] with ω hq haω
    exact hq.sub haω
  have hDv : HasFiniteVariationPaths (Q - A) P := by
    filter_upwards [hSM.hasFiniteVariationPaths_quadraticVariation hF, hv] with ω hq haω
    exact locallyBoundedVariationOn_sub hq haω
  have hD0 : (Q - A) 0 =ᵐ[P] 0 := by
    filter_upwards [hSM.quadraticVariation_zero_ae hF, h0] with ω hq haω
    exact sub_eq_zero.mpr (hq.trans haω.symm)
  have hz := IsContinuousLocalMartingale.indistinguishable_zero_of_finiteVariation
    ⟨hD, hDc⟩ hF hDv hD0
  filter_upwards [hz] with ω hω t
  exact sub_eq_zero.mp (hω t)

end ProbabilityTheory

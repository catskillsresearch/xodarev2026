/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousFiniteVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousLocalConstancy

/-! # Continuous finite-variation local martingales are constant

Protter II.27, Corollary 1, on the entire half-line. The proof uses the single
general raw bracket and retains an arbitrary, possibly nonintegrable, initial value.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.indistinguishable_initial_of_finiteVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) : Indistinguishable X (fun _ ↦ X 0) P :=
  hX.indistinguishable_initial_of_quadraticVariation_constant hF
    ((hX.isSemimartingale hF).quadraticVariation_of_continuous_finiteVariation hF hX.2 hv)

theorem IsContinuousLocalMartingale.indistinguishable_zero_of_finiteVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) (h0 : X 0 =ᵐ[P] 0) : Indistinguishable X 0 P := by
  filter_upwards [hX.indistinguishable_initial_of_finiteVariation hF hv, h0] with ω hc hz t
  exact (hc t).trans hz

end ProbabilityTheory

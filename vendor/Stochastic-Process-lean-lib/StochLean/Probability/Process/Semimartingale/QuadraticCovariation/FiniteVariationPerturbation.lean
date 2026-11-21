/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump

/-! # Finite-variation perturbations preserve continuous mixed brackets

Initial random constants are permitted. These are continuous-bracket
identities and do not assert the corresponding false raw initial identity.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y A B : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_add_finiteVariation_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hA : IsSemimartingale A F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths A P) :
    Indistinguishable ((hX.add hA).continuousQuadraticCovariation hY hF)
      (hX.continuousQuadraticCovariation hY hF) P := by
  filter_upwards [hX.continuousQuadraticCovariation_add_left hA hY hF,
    hA.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hY hF
      (hA.isQuadraticPureJump_of_finiteVariation hF hv)] with ω ha hz t
  simpa only [Pi.add_apply, hz t, Pi.zero_apply, add_zero] using ha t

theorem IsSemimartingale.continuousQuadraticCovariation_add_finiteVariation_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hA : IsSemimartingale A F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths A P) :
    Indistinguishable (hX.continuousQuadraticCovariation (hY.add hA) hF)
      (hX.continuousQuadraticCovariation hY hF) P :=
  (hX.continuousQuadraticCovariation_comm (hY.add hA) hF).trans
    ((hY.continuousQuadraticCovariation_add_finiteVariation_left hX hA hF hv).trans
      (hY.continuousQuadraticCovariation_comm hX hF))

theorem IsSemimartingale.continuousQuadraticCovariation_add_finiteVariation_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hA : IsSemimartingale A F P) (hB : IsSemimartingale B F P) (hF : F.IsUsual P)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P) :
    Indistinguishable ((hX.add hA).continuousQuadraticCovariation (hY.add hB) hF)
      (hX.continuousQuadraticCovariation hY hF) P :=
  (hX.continuousQuadraticCovariation_add_finiteVariation_left (hY.add hB) hA hF hvA).trans
    (hX.continuousQuadraticCovariation_add_finiteVariation_right hY hB hF hvB)

end ProbabilityTheory

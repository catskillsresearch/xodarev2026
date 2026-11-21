/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra
public import StochLean.Probability.Process.Partition.CrossSumsLinear

/-! # Raw mixed brackets with arbitrary measurable initial constants

Only positive-time increments vanish. The initial product is retained even
when the random constant has no finite moments.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_const_initial_left
    (hX : IsSemimartingale X F P) (hZ : Measurable[F 0] Z) (hF : F.IsUsual P) :
    Indistinguishable ((isSemimartingale_const_initial hZ).quadraticCovariation hX hF)
      (fun _ ω ↦ Z ω * X 0 ω) P := by
  apply (isSemimartingale_const_initial hZ).quadraticCovariation_indistinguishable_of_limits hX hF
  · intro π _
    simpa only [StoppingTimePartition.quadraticCovariationSumProcess_constant_left] using
      tendstoUCP_const atTop (fun (_ : ℝ≥0) ω ↦ Z ω * X 0 ω)
  · exact ae_of_all _ fun _ _ ↦ continuousWithinAt_const

theorem IsSemimartingale.quadraticCovariation_const_initial_right
    (hX : IsSemimartingale X F P) (hZ : Measurable[F 0] Z) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation (isSemimartingale_const_initial hZ) hF)
      (fun _ ω ↦ X 0 ω * Z ω) P := by
  filter_upwards [hX.quadraticCovariation_comm (isSemimartingale_const_initial hZ) hF,
    hX.quadraticCovariation_const_initial_left hZ hF] with ω hc hz t
  rw [hc t, hz t, mul_comm]

end ProbabilityTheory

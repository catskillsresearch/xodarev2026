/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Measurability
public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureAbsoluteContinuity

/-! # Protter II.2: absolutely continuous changes of measure

Only the target measure is required to be finite. No equivalence or bounded density is
assumed. The source usual filtration supplies measurability of elementary integrals;
usual completeness is not incorrectly transferred from the source to the target measure.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P Q : Measure Ω} [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ}

theorem IsGoodIntegrator.absolutelyContinuous (hX : IsGoodIntegrator X F P)
    (hQP : Q ≪ P) (ha : Adapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    IsGoodIntegrator X F Q := by
  intro H hH hu
  exact (hX H hH hu).absolutelyContinuous hQP
    (fun n ↦ ((hH n).measurable_elementaryIntegral ha hF hr).aestronglyMeasurable)

theorem IsTotalSemimartingale.absolutelyContinuous (hX : IsTotalSemimartingale X F P)
    (hQP : Q ≪ P) (hF : F.IsUsual P) : IsTotalSemimartingale X F Q :=
  ⟨hX.1, hQP.ae_le hX.2.1,
    hX.2.2.absolutelyContinuous hQP hX.1 hF hX.2.1.hasRightContinuousPaths⟩

theorem IsSemimartingale.absolutelyContinuous (hX : IsSemimartingale X F P)
    (hQP : Q ≪ P) (hF : F.IsUsual P) : IsSemimartingale X F Q :=
  fun T ↦ (hX T).absolutelyContinuous hQP hF

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Stability

/-! # Negation and subtraction of source semimartingales -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsGoodIntegrator.neg (hX : IsGoodIntegrator X F P) : IsGoodIntegrator (-X) F P := by
  change IsGoodIntegrator (fun t ω ↦ -X t ω) F P
  simpa only [neg_one_mul] using hX.const_mul (-1)

theorem IsGoodIntegrator.sub (hX : IsGoodIntegrator X F P) (hY : IsGoodIntegrator Y F P) :
    IsGoodIntegrator (X - Y) F P := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

theorem IsTotalSemimartingale.neg (hX : IsTotalSemimartingale X F P) :
    IsTotalSemimartingale (-X) F P := by
  change IsTotalSemimartingale (fun t ω ↦ -X t ω) F P
  simpa only [neg_one_mul] using hX.const_mul (-1)

theorem IsTotalSemimartingale.sub
    (hX : IsTotalSemimartingale X F P) (hY : IsTotalSemimartingale Y F P) :
    IsTotalSemimartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

theorem IsSemimartingale.neg (hX : IsSemimartingale X F P) : IsSemimartingale (-X) F P := by
  change IsSemimartingale (fun t ω ↦ -X t ω) F P
  simpa only [neg_one_mul] using hX.const_mul (-1)

theorem IsSemimartingale.sub (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) :
    IsSemimartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

end ProbabilityTheory

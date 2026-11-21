/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.StieltjesRealization

/-! # Actual positive-time atoms of a canonical raw-bracket realization

The Stieltjes measure is that of an indistinguishable increasing version
of the existing raw bracket. Its atom at each positive time is exactly
the squared jump of the original semimartingale, on one common event.
The separate source initial square is not made into a measure atom.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory.SemimartingaleBracketRealization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
  {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}

theorem left_singleton_eq_sq_jump (D : SemimartingaleBracketRealization hX hY hF) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (D.left ω).measure {t} = ENNReal.ofReal ((jumpProcess X t ω) ^ 2) := by
  filter_upwards [D.left_eq, hX.jumpProcess_quadraticVariation hF] with ω he hj t ht
  rw [StieltjesFunction.measure_singleton]
  apply congrArg ENNReal.ofReal
  have h := hj t
  simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg (ne_of_gt ht), he] using h

end ProbabilityTheory.SemimartingaleBracketRealization

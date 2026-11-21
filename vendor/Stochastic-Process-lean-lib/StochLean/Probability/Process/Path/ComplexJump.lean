/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Complex

/-! # Complex jumps and the source initial-value convention -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

noncomputable def complexJumpProcess {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  Z - complexLeftLimitProcess Z

@[simp] theorem complexJumpProcess_re {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) :
    (complexJumpProcess Z t ω).re = jumpProcess (fun u v ↦ (Z u v).re) t ω := rfl

@[simp] theorem complexJumpProcess_im {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) :
    (complexJumpProcess Z t ω).im = jumpProcess (fun u v ↦ (Z u v).im) t ω := rfl

@[simp] theorem complexJumpProcess_zero {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) :
    complexJumpProcess Z 0 = Z 0 := by
  simp only [complexJumpProcess, Pi.sub_apply, complexLeftLimitProcess_zero, sub_zero]

theorem IsContinuousPath.complexJumpProcess_eq_zero {Ω : Type*}
    {Z : ℝ≥0 → Ω → ℂ} {ω : Ω} (hZ : IsContinuousPath (Z · ω))
    {t : ℝ≥0} (ht : t ≠ 0) : complexJumpProcess Z t ω = 0 := by
  apply Complex.ext
  · exact IsContinuousPath.jumpProcess_eq_zero (X := fun u v ↦ (Z u v).re)
      (Complex.continuous_re.comp hZ) ht
  · exact IsContinuousPath.jumpProcess_eq_zero (X := fun u v ↦ (Z u v).im)
      (Complex.continuous_im.comp hZ) ht

end ProbabilityTheory

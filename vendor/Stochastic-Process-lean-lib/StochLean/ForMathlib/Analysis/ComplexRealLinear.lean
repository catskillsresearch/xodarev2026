/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-! # Real linear functionals on complex numbers in the basis (1, I) -/

@[expose] public section

namespace StochLean

theorem realLinearMap_complex_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = L 1 * z.re + L Complex.I * z.im := by
  have he : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [he]
  simp only [map_add, map_smul, smul_eq_mul]
  exact congrArg₂ (· + ·) (mul_comm _ _) (mul_comm _ _)

end StochLean

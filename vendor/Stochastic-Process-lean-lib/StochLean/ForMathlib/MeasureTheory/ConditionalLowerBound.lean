/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # First moments controlled by a conditional lower bound

The elementary real inequality `|x| ≤ x + 2 |y|` for `y ≤ x`, followed by
conditional L1 contraction, controls the full first moment. The sign of the
mean is retained; there is no nonnegativity premise on either variable.
-/

@[expose] public section

namespace MeasureTheory

theorem Integrable.integral_norm_le_of_condExp_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable f P) (hle : P[g | m] ≤ᵐ[P] f) :
    (∫ ω, ‖f ω‖ ∂P) ≤ (∫ ω, f ω ∂P) + 2 * (∫ ω, ‖g ω‖ ∂P) := by
  have hc : Integrable P[g | m] P := integrable_condExp
  calc
    _ ≤ ∫ ω, f ω + 2 * ‖P[g | m] ω‖ ∂P := by
      apply integral_mono_ae hf.norm (hf.add (hc.norm.const_mul 2))
      filter_upwards [hle] with ω hω
      change ‖f ω‖ ≤ f ω + 2 * ‖P[g | m] ω‖
      simp only [Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · linarith [neg_le_abs (P[g | m] ω)]
      · linarith [abs_nonneg (P[g | m] ω)]
    _ = (∫ ω, f ω ∂P) + 2 * (∫ ω, ‖P[g | m] ω‖ ∂P) := by
      rw [integral_add hf (hc.norm.const_mul 2), integral_const_mul]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (integral_norm_condExp_le (m := m) (μ := P) g)
        (by norm_num : (0 : ℝ) ≤ 2))

end MeasureTheory

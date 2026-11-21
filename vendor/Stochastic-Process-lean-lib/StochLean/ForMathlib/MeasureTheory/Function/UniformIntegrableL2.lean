/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.DeLaValleePoussin
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Bounded second moments imply uniform integrability

This is a specialization of the existing superlinear-envelope theorem with
the actual square envelope, not an assumption about a limiting family.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {f : ι → Ω → ℝ}

theorem uniformIntegrable_of_bounded_integral_sq (hf : ∀ i, MemLp (f i) 2 P)
    (C : ℝ≥0) (hb : ∀ i, ∫ ω, (f i ω) ^ 2 ∂P ≤ C) : UniformIntegrable f 1 P := by
  have hΦ : SuperlinearEnvelope (fun r : ℝ≥0 ↦ r ^ 2) := by
    have heq : (fun r : ℝ≥0 ↦ r ^ 2 / r) = id := by
      funext r
      by_cases hr : r = 0 <;> simp [pow_two, hr]
    rw [SuperlinearEnvelope, heq]
    exact tendsto_id
  apply uniformIntegrable_of_superlinearEnvelope hΦ (measurable_id.pow_const 2)
    (fun i ↦ (hf i).aestronglyMeasurable) C
  intro i
  have heq : (fun ω ↦ ((‖f i ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) =
      fun ω ↦ ENNReal.ofReal ((f i ω) ^ 2) := by
    funext ω
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp only [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hf i).integrable_sq
    (ae_of_all P (fun ω ↦ sq_nonneg (f i ω)))]
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hb i)

end MeasureTheory

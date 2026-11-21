/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.LocallyFiniteKernelIntegral
public import StochLean.ForMathlib.MeasurableStieltjesNNReal

/-! # Measurable weighted energies of random Stieltjes measures -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace StochLean

theorem measurable_stieltjesLIntegral
    {Ω : Type*} [MeasurableSpace Ω] {A : Ω → StieltjesFunction ℝ≥0}
    (hA : ∀ t, Measurable fun ω ↦ A ω t)
    {f : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂(A ω).measure := by
  let κ : Kernel Ω ℝ≥0 := ⟨fun ω ↦ (A ω).measure, measurable_stieltjesMeasure hA⟩
  apply measurable_lintegral_kernel_of_finite_exhaustion (κ := κ)
    (s := fun n : ℕ ↦ Iic (n : ℝ≥0)) (fun _ ↦ measurableSet_Iic)
    (fun n m h ↦ Iic_subset_Iic.mpr (Nat.cast_le.mpr h)) ?_ ?_ hf
  · ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil t, Nat.le_ceil t⟩
  · intro n ω
    refine ⟨?_⟩
    change ((A ω).measure.restrict (Iic (n : ℝ≥0))) univ < ∞
    rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
    exact ENNReal.ofReal_lt_top

end StochLean

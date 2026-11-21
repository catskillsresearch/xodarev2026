/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.PredictableMeasureExt
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Predictable kernel duality from expected rectangle masses

Equality of expected kernel masses on the actual predictable rectangles
implies equality of iterated lower integrals of every predictable function.
Only the first expected total mass needs to be finite. Both kernels are
explicitly s-finite, so the native composition-products are actual products
rather than the fallback used outside their defining hypotheses.

The proof uses native composition-products, coordinate swaps, and trims to
the existing predictable sigma-field. No new random measure, compensator,
or stochastic integral is defined or assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

private theorem map_swap_compProd_apply_prod (κ : Kernel Ω ℝ≥0) [IsSFiniteKernel κ]
    {S : Set ℝ≥0} (hS : MeasurableSet S) {E : Set Ω} (hE : MeasurableSet E) :
    ((P ⊗ₘ κ).map Prod.swap) (S ×ˢ E) = ∫⁻ ω in E, κ ω S ∂P := by
  rw [Measure.map_apply measurable_swap (hS.prod hE), preimage_swap_prod]
  exact Measure.compProd_apply_prod hE hS

/-- Actual predictable functions satisfy kernel duality once expected
initial and finite-interval rectangle masses agree. -/
theorem lintegral_lintegral_eq_of_predictable_rectangles
    (F : Filtration ℝ≥0 mΩ) {κ η : Kernel Ω ℝ≥0}
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hfin : (∫⁻ ω, κ ω univ ∂P) < ∞)
    (h0 : ∀ E, MeasurableSet[F 0] E →
      (∫⁻ ω in E, κ ω {0} ∂P) = ∫⁻ ω in E, η ω {0} ∂P)
    (hIoc : ∀ s t E, MeasurableSet[F s] E →
      (∫⁻ ω in E, κ ω (Ioc s t) ∂P) = ∫⁻ ω in E, η ω (Ioc s t) ∂P)
    {H : ℝ≥0 × Ω → ℝ≥0∞} (hH : Measurable[F.predictable] H) :
    (∫⁻ ω, ∫⁻ t, H (t, ω) ∂κ ω ∂P) = ∫⁻ ω, ∫⁻ t, H (t, ω) ∂η ω ∂P := by
  let μ : Measure (ℝ≥0 × Ω) := (P ⊗ₘ κ).map Prod.swap
  let ν : Measure (ℝ≥0 × Ω) := (P ⊗ₘ η).map Prod.swap
  have hμmass : μ univ = ∫⁻ ω, κ ω univ ∂P := by
    simpa only [univ_prod_univ, setLIntegral_univ] using
      (map_swap_compProd_apply_prod (P := P) κ MeasurableSet.univ MeasurableSet.univ)
  let : IsFiniteMeasure μ := ⟨hμmass.trans_lt hfin⟩
  have he : μ.trim F.predictable_le_prod = ν.trim F.predictable_le_prod := by
    apply Measure.trim_predictable_eq_of_Ioc F
    · intro E hE
      exact (map_swap_compProd_apply_prod κ (measurableSet_singleton 0) (F.le 0 E hE)).trans
        ((h0 E hE).trans
          (map_swap_compProd_apply_prod η (measurableSet_singleton 0) (F.le 0 E hE)).symm)
    · intro s t E hE
      exact (map_swap_compProd_apply_prod κ measurableSet_Ioc (F.le s E hE)).trans
        ((hIoc s t E hE).trans
          (map_swap_compProd_apply_prod η measurableSet_Ioc (F.le s E hE)).symm)
  have hHambient : Measurable H := hH.mono F.predictable_le_prod le_rfl
  have hlin : (∫⁻ p, H p ∂μ) = ∫⁻ p, H p ∂ν := by
    calc
      (∫⁻ p, H p ∂μ) = ∫⁻ p, H p ∂μ.trim F.predictable_le_prod :=
        (lintegral_trim F.predictable_le_prod hH).symm
      _ = ∫⁻ p, H p ∂ν.trim F.predictable_le_prod := by rw [he]
      _ = ∫⁻ p, H p ∂ν := lintegral_trim F.predictable_le_prod hH
  change (∫⁻ p, H p ∂(P ⊗ₘ κ).map Prod.swap) =
    ∫⁻ p, H p ∂(P ⊗ₘ η).map Prod.swap at hlin
  rw [MeasureTheory.lintegral_map hHambient measurable_swap,
    MeasureTheory.lintegral_map hHambient measurable_swap] at hlin
  exact (Measure.lintegral_compProd (μ := P) (κ := κ)
    (hHambient.comp measurable_swap)).symm.trans
      (hlin.trans (Measure.lintegral_compProd (μ := P) (κ := η)
        (hHambient.comp measurable_swap)))

end ProbabilityTheory.Kernel

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.MeasurablePointDiffusePart
public import StochLean.ForMathlib.MeasurableIntegralFiniteFibers
public import StochLean.ForMathlib.MeasureTheory.PointAtomicIntegral

/-! # Measurable point-atomic parts and their actual integral series

The atom locations may vary with the sample. Joint singleton mass gives
a measurable restriction without choosing an enumeration. Fiberwise
finite mass is sufficient; no deterministic bound on total mass is imposed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
  (hκ : ∀ ω, IsFiniteMeasure (κ ω))

include hκ

theorem measurable_pointAtomicPart_of_finite_fibers :
    Measurable fun ω ↦ pointAtomicPart (κ ω) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let S : Set (Ω × ℝ≥0) := {p | p.2 ∈ s ∧ κ p.1 {p.2} ≠ 0}
  have hS : MeasurableSet S :=
    (measurable_snd hs).inter
      (measurableSet_eq_fun (measurable_kernel_singleton_of_finite_fibers κ hκ)
        measurable_const).compl
  have h := measurable_lintegral_kernel_of_finite_fibers hκ
    (show Measurable (S.indicator (fun _ ↦ (1 : ℝ≥0∞))) from measurable_const.indicator hS)
  have he (ω : Ω) : (∫⁻ t, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ω, t) ∂κ ω) =
      pointAtomicPart (κ ω) s := by
    rw [lintegral_indicator_const_comp (f := Prod.mk ω) measurable_prodMk_left hS 1,
      one_mul, pointAtomicPart, Measure.restrict_apply hs]
    rfl
  simpa only [he] using h

theorem measurable_pointAtomicIntegral_of_finite_fibers
    {f : Ω → ℝ≥0 → ℝ} (hf : Measurable (uncurry f)) :
    Measurable fun ω ↦ ∫ t, f ω t ∂pointAtomicPart (κ ω) := by
  let η : Kernel Ω ℝ≥0 := ⟨fun ω ↦ pointAtomicPart (κ ω),
    measurable_pointAtomicPart_of_finite_fibers κ hκ⟩
  have hη (ω : Ω) : IsFiniteMeasure (η ω) := by
    let : IsFiniteMeasure (κ ω) := hκ ω
    change IsFiniteMeasure ((κ ω).restrict (pointAtomSet (κ ω)))
    infer_instance
  exact (stronglyMeasurable_integral_kernel_of_finite_fibers η hη
    hf.stronglyMeasurable).measurable

theorem measurable_tsum_kernel_atoms_of_integrable
    {f : Ω → ℝ≥0 → ℝ} (hf : Measurable (uncurry f))
    (hi : ∀ ω, Integrable (f ω) (pointAtomicPart (κ ω))) :
    Measurable fun ω ↦ ∑' t, (κ ω).real {t} * f ω t := by
  have he (ω : Ω) : (∫ t, f ω t ∂pointAtomicPart (κ ω)) =
      ∑' t, (κ ω).real {t} * f ω t := by
    let : IsFiniteMeasure (κ ω) := hκ ω
    exact integral_pointAtomicPart_eq_tsum (hi ω)
  simpa only [he] using measurable_pointAtomicIntegral_of_finite_fibers κ hκ hf

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.PointAtomicDecomposition
public import StochLean.ForMathlib.MeasureTheory.LocallyFiniteKernelIntegral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Measurable removal of the point atoms of a random finite measure

Joint singleton mass is the kernel integral of the measurable diagonal. The
zero-singleton-mass region is therefore jointly measurable, so its restriction
is again a measurable random measure. Only fiberwise finite mass is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
  (hκ : ∀ ω, IsFiniteMeasure (κ ω))

include hκ

theorem measurable_kernel_singleton_of_finite_fibers :
    Measurable fun p : Ω × ℝ≥0 ↦ κ p.1 {p.2} := by
  classical
  let η : Kernel (Ω × ℝ≥0) ℝ≥0 := ⟨fun p ↦ κ p.1, κ.measurable.comp measurable_fst⟩
  let f : (Ω × ℝ≥0) × ℝ≥0 → ℝ≥0∞ := fun p ↦ if p.1.2 = p.2 then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_eq_fun measurable_fst.snd measurable_snd) measurable_const measurable_const
  have h := measurable_lintegral_kernel_of_finite_fibers (κ := η) (fun p ↦ hκ p.1) hf
  have heq (p : Ω × ℝ≥0) : (∫⁻ t, f (p, t) ∂η p) = κ p.1 {p.2} := by
    change (∫⁻ t, (if p.2 = t then (1 : ℝ≥0∞) else 0) ∂κ p.1) = _
    simpa only [Set.indicator, mem_singleton_iff, Pi.one_apply,
      eq_comm] using (lintegral_indicator_one (μ := κ p.1) (measurableSet_singleton p.2))
  simpa only [heq] using h

theorem measurable_pointDiffusePart_of_finite_fibers :
    Measurable fun ω ↦ pointDiffusePart (κ ω) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let S : Set (Ω × ℝ≥0) := {p | p.2 ∈ s ∧ κ p.1 {p.2} = 0}
  have hS : MeasurableSet S :=
    (measurable_snd hs).inter
      (measurableSet_eq_fun (measurable_kernel_singleton_of_finite_fibers κ hκ) measurable_const)
  have h := measurable_lintegral_kernel_of_finite_fibers hκ
    (show Measurable (S.indicator (fun _ ↦ (1 : ℝ≥0∞))) from measurable_const.indicator hS)
  have heq (ω : Ω) : (∫⁻ t, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ω, t) ∂κ ω) =
      pointDiffusePart (κ ω) s := by
    rw [lintegral_indicator_const_comp (f := Prod.mk ω) measurable_prodMk_left hS 1, one_mul,
      pointDiffusePart, Measure.restrict_apply hs]
    congr 1
    ext t
    simp only [S, pointAtomSet, mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_compl_iff,
      not_not]
  simpa only [heq] using h

end StochLean

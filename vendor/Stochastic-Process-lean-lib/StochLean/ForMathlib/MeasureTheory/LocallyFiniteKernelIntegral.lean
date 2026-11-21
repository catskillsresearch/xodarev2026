/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Jointly measurable lower integrals with locally finite random measures

The finite-fiber argument uses Mathlib's measurable sections theorem and simple
function approximation. No uniform bound on the random total masses is needed.
An increasing finite-measure exhaustion then gives the half-line result.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace StochLean

theorem measurable_lintegral_kernel_of_finite_fibers
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {κ : Kernel Ω T}
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {f : Ω × T → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂κ ω := by
  let S : ℕ → SimpleFunc (Ω × T) ℝ≥0∞ := SimpleFunc.eapprox f
  have heq (ω : Ω) : (∫⁻ t, f (ω, t) ∂κ ω) = ⨆ n, ∫⁻ t, S n (ω, t) ∂κ ω := by
    conv_lhs => arg 2; ext t; rw [← SimpleFunc.iSup_eapprox_apply hf (ω, t)]
    exact lintegral_iSup (fun n ↦ (S n).measurable.comp measurable_prodMk_left)
      (fun i j hij t ↦ SimpleFunc.monotone_eapprox f hij (ω, t))
  simp_rw [heq]
  refine Measurable.iSup fun n ↦ ?_
  refine SimpleFunc.induction
    (motive := fun s ↦ Measurable fun ω ↦ ∫⁻ t, s (ω, t) ∂κ ω) ?_ ?_ (S n)
  · intro c s hs
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    change Measurable fun ω ↦ ∫⁻ t, s.indicator (Function.const (Ω × T) c) (ω, t) ∂κ ω
    have heq (ω : Ω) : (∫⁻ t, s.indicator (Function.const (Ω × T) c) (ω, t) ∂κ ω) =
        c * κ ω (Prod.mk ω ⁻¹' s) :=
      lintegral_indicator_const_comp (f := Prod.mk ω) measurable_prodMk_left hs c
    simp_rw [heq]
    exact (Kernel.measurable_kernel_prodMk_left_of_finite hs hκ).const_mul c
  · intro s t _ hs ht
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have heq : (fun ω ↦ ∫⁻ u, s (ω, u) + t (ω, u) ∂κ ω) =
        (fun ω ↦ ∫⁻ u, s (ω, u) ∂κ ω) + fun ω ↦ ∫⁻ u, t (ω, u) ∂κ ω := by
      funext ω
      exact lintegral_add_left ((s.measurable).comp measurable_prodMk_left) _
    rw [heq]
    exact hs.add ht

theorem measurable_lintegral_kernel_of_finite_exhaustion
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {κ : Kernel Ω T}
    {s : ℕ → Set T} (hs : ∀ n, MeasurableSet (s n)) (hm : Monotone s)
    (hu : (⋃ n, s n) = univ) (hκ : ∀ n ω, IsFiniteMeasure ((κ ω).restrict (s n)))
    {f : Ω × T → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂κ ω := by
  have heq (ω : Ω) : (∫⁻ t, f (ω, t) ∂κ ω) =
      ⨆ n, ∫⁻ t in s n, f (ω, t) ∂κ ω := by
    rw [← setLIntegral_univ, ← hu]
    exact setLIntegral_iUnion_of_directed _ hm.directed_le
  simp_rw [heq]
  exact Measurable.iSup fun n ↦
    measurable_lintegral_kernel_of_finite_fibers (κ := κ.restrict (hs n)) (hκ n) hf

end StochLean

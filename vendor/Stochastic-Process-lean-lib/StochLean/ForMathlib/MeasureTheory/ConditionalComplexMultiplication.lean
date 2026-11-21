/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Complex multiplication in conditional expectations

These are the real-bilinear pull-out theorems instantiated at complex
multiplication. No complex-linear conditional-expectation owner is created.
-/

@[expose] public section

namespace StochLean

open MeasureTheory

theorem condExp_complex_mul_of_stronglyMeasurable_left
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} {f g : Ω → ℂ}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun ω ↦ f ω * g ω) P)
    (hg : Integrable g P) :
    P[fun ω ↦ f ω * g ω | m] =ᵐ[P] fun ω ↦ f ω * P[g | m] ω :=
  condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ) hf hfg hg

theorem condExp_complex_mul_of_bound
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {f g : Ω → ℂ} (hm : m ≤ mΩ) (hf : StronglyMeasurable[m] f)
    (hg : Integrable g P) (C : ℝ) (hC : ∀ᵐ ω ∂P, ‖f ω‖ ≤ C) :
    P[fun ω ↦ f ω * g ω | m] =ᵐ[P] fun ω ↦ f ω * P[g | m] ω :=
  condExp_stronglyMeasurable_bilin_of_bound (.mul ℝ ℂ) hm hf hg C hC

end StochLean

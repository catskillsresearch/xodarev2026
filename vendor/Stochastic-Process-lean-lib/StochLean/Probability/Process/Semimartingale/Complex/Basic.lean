/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Complex
public import StochLean.Probability.Process.Semimartingale.Subtraction

/-! # Complex semimartingales are pairs of the existing real semimartingales

This is a coordinate predicate, not another good-integrator construction.
All stochastic integration and bracket owners remain the real ones.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {Z W : ℝ≥0 → Ω → ℂ}

def IsComplexSemimartingale (Z : ℝ≥0 → Ω → ℂ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsSemimartingale (fun t ω ↦ (Z t ω).re) F P ∧
    IsSemimartingale (fun t ω ↦ (Z t ω).im) F P

theorem IsSemimartingale.complex {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) :
    IsComplexSemimartingale (complexProcess X Y) F P := ⟨hX, hY⟩

theorem IsComplexSemimartingale.hasCadlagPaths (hZ : IsComplexSemimartingale Z F P) :
    HasCadlagPaths Z P := (hZ.1.hasCadlagPaths.complex hZ.2.hasCadlagPaths)

theorem IsComplexSemimartingale.adapted (hZ : IsComplexSemimartingale Z F P) :
    Adapted F Z := by
  intro t
  have h : Measurable[F t] (fun ω ↦ ((Z t ω).re : ℂ) + Complex.I * ((Z t ω).im : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (hZ.1.adapted t)).add
      ((Complex.continuous_ofReal.measurable.comp (hZ.2.adapted t)).const_mul Complex.I)
  convert h using 1
  funext ω
  apply Complex.ext <;> simp

theorem IsComplexSemimartingale.add (hZ : IsComplexSemimartingale Z F P)
    (hW : IsComplexSemimartingale W F P) : IsComplexSemimartingale (Z + W) F P := by
  constructor
  · simpa only [Pi.add_def, Complex.add_re] using hZ.1.add hW.1
  · simpa only [Pi.add_def, Complex.add_im] using hZ.2.add hW.2

theorem IsComplexSemimartingale.sub (hZ : IsComplexSemimartingale Z F P)
    (hW : IsComplexSemimartingale W F P) : IsComplexSemimartingale (Z - W) F P := by
  constructor
  · simpa only [Pi.sub_def, Complex.sub_re] using hZ.1.sub hW.1
  · simpa only [Pi.sub_def, Complex.sub_im] using hZ.2.sub hW.2

theorem IsComplexSemimartingale.const_mul (hZ : IsComplexSemimartingale Z F P) (c : ℂ) :
    IsComplexSemimartingale (fun t ω ↦ c * Z t ω) F P := by
  constructor
  · simpa only [Pi.sub_def, Complex.mul_re] using
      (hZ.1.const_mul c.re).sub (hZ.2.const_mul c.im)
  · simpa only [Pi.add_def, Complex.mul_im] using
      (hZ.2.const_mul c.re).add (hZ.1.const_mul c.im)

end ProbabilityTheory

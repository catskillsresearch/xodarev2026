/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Congr
public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import StochLean.Probability.Process.Path.Complex

/-! # Complex local martingales as pairs of the existing real predicates

The real and imaginary coordinates retain their genuine masked fundamental
sequences. This introduces no new integral or localization construction.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {Z W : ℝ≥0 → Ω → ℂ}

def IsComplexLocalMartingale (Z : ℝ≥0 → Ω → ℂ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsLocalMartingale (fun t ω ↦ (Z t ω).re) F P ∧
    IsLocalMartingale (fun t ω ↦ (Z t ω).im) F P

theorem IsComplexLocalMartingale.adapted (hZ : IsComplexLocalMartingale Z F P) :
    Adapted F Z := by
  intro t
  have h : Measurable[F t] (fun ω ↦ ((Z t ω).re : ℂ) + Complex.I * ((Z t ω).im : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (hZ.1.1 t)).add
      ((Complex.continuous_ofReal.measurable.comp (hZ.2.1 t)).const_mul Complex.I)
  convert h using 1
  funext ω
  apply Complex.ext <;> simp

theorem IsComplexLocalMartingale.hasCadlagPaths (hZ : IsComplexLocalMartingale Z F P) :
    HasCadlagPaths Z P := hZ.1.2.1.complex hZ.2.2.1

theorem IsComplexLocalMartingale.add [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    (hZ : IsComplexLocalMartingale Z F P) (hW : IsComplexLocalMartingale W F P)
    (hF : F.IsUsual P) : IsComplexLocalMartingale (Z + W) F P := by
  constructor
  · simpa only [Pi.add_def, Complex.add_re] using hZ.1.add hW.1 hF
  · simpa only [Pi.add_def, Complex.add_im] using hZ.2.add hW.2 hF

theorem IsComplexLocalMartingale.const_mul [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    (hZ : IsComplexLocalMartingale Z F P) (hF : F.IsUsual P) (c : ℂ) :
    IsComplexLocalMartingale (fun t ω ↦ c * Z t ω) F P := by
  constructor
  · simpa only [Pi.sub_def, Pi.smul_def, smul_eq_mul, Complex.mul_re] using
      (hZ.1.const_smul c.re).sub (hZ.2.const_smul c.im) hF
  · simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul, Complex.mul_im] using
      (hZ.2.const_smul c.re).add (hZ.1.const_smul c.im) hF

theorem IsComplexLocalMartingale.congr (hZ : IsComplexLocalMartingale Z F P)
    (hF : F.IsUsual P) (ha : Adapted F W) (he : Indistinguishable Z W P) :
    IsComplexLocalMartingale W F P :=
  ⟨hZ.1.congr hF (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
      (he.mono (fun _ h t ↦ congrArg Complex.re (h t))),
    hZ.2.congr hF (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (he.mono (fun _ h t ↦ congrArg Complex.im (h t)))⟩

theorem isComplexLocalMartingale_const_initial [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    {A : Ω → ℂ} (ha : Measurable[F 0] A) :
    IsComplexLocalMartingale (fun _ : ℝ≥0 ↦ A) F P :=
  ⟨(isContinuousLocalMartingale_const_initial
      (Complex.continuous_re.measurable.comp ha)).1,
    (isContinuousLocalMartingale_const_initial
      (Complex.continuous_im.measurable.comp ha)).1⟩

end ProbabilityTheory

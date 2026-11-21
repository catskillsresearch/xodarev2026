/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.LeftLimit
public import StochLean.Probability.Process.Path.Complex

/-! # Adapted complex left limits use the existing real-coordinate construction -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω → ℂ}

theorem Adapted.complex (hX : Adapted F X) (hY : Adapted F Y) :
    Adapted F (complexProcess X Y) := by
  intro t
  have h : Measurable[F t] (fun ω ↦ (X t ω : ℂ) + Complex.I * (Y t ω : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (hX t)).add
      ((Complex.continuous_ofReal.measurable.comp (hY t)).const_mul Complex.I)
  convert h using 1
  funext ω
  apply Complex.ext <;> simp [complexProcess]

theorem HasCadlagPaths.hasCagladPaths_complexLeftLimitProcess (hZ : HasCadlagPaths Z P) :
    HasCagladPaths (complexLeftLimitProcess Z) P :=
  (hZ.continuous_comp Complex.continuous_re).hasCagladPaths_leftLimitProcess.complex
    (hZ.continuous_comp Complex.continuous_im).hasCagladPaths_leftLimitProcess

theorem Adapted.complexLeftLimitProcess_of_usual [IsFiniteMeasure P]
    (ha : Adapted F Z) (hF : F.IsUsual P) (hr : HasCadlagPaths Z P) :
    Adapted F (complexLeftLimitProcess Z) := by
  have haR : Adapted F (fun t ω ↦ (Z t ω).re) :=
    fun t ↦ Complex.continuous_re.measurable.comp (ha t)
  have haI : Adapted F (fun t ω ↦ (Z t ω).im) :=
    fun t ↦ Complex.continuous_im.measurable.comp (ha t)
  exact Adapted.complex
    (haR.leftLimitProcess_of_usual hF (hr.continuous_comp Complex.continuous_re))
    (haI.leftLimitProcess_of_usual hF (hr.continuous_comp Complex.continuous_im))

end ProbabilityTheory

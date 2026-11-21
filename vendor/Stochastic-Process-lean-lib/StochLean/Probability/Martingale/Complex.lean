/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Probability.MartingaleLinearMap
public import StochLean.Probability.Process.Path.Complex

/-! # The usual complex martingale predicate agrees with its real coordinates -/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

theorem martingale_complex_iff {Ω ι : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ι mΩ}
    {Z : ι → Ω → ℂ} :
    Martingale Z F P ↔ Martingale (fun t ω ↦ (Z t ω).re) F P ∧
      Martingale (fun t ω ↦ (Z t ω).im) F P := by
  constructor
  · intro h
    exact ⟨h.continuousLinearMap Complex.reCLM, h.continuousLinearMap Complex.imCLM⟩
  · rintro ⟨hR, hI⟩
    have h := (hR.continuousLinearMap Complex.ofRealCLM).add
      (hI.continuousLinearMap (Complex.I • Complex.ofRealCLM))
    convert h using 1
    funext t ω
    apply Complex.ext <;> simp

end ProbabilityTheory

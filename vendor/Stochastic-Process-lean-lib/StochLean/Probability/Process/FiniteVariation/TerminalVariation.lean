/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TerminalVariation
public import StochLean.Probability.Process.FiniteVariation.Variation

/-! # Measurability of actual whole-half-line variation

The existing adapted extended-variation process and its integer horizons
make the original path's canonical `eVariationOn` measurable in the terminal
sigma-field and in the ambient sigma-field. Usual completeness already
handles the common exceptional path event in the compact-variation owner.

These are exact measurability statements for the original function, not
merely measurable versions. No finite-variation assumption, real-valued
conversion, terminal selector, or new stochastic-process predicate is used.
-/

@[expose] public section

open ProbabilityTheory StochLean Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The full extended path variation is measurable in the terminal field. -/
theorem Adapted.measurable_eVariationOn_univ_iSup_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Measurable[⨆ t, F t] (fun ω ↦ eVariationOn (X · ω) univ) := by
  have he : (fun ω ↦ eVariationOn (X · ω) univ) =
      fun ω ↦ ⨆ n : ℕ, eTotalVariationProcess X (n : ℝ≥0) ω :=
    funext fun ω ↦ eVariationOn_univ_eq_iSup_Icc_nat (X · ω)
  rw [he]
  let : MeasurableSpace Ω := ⨆ t, F t
  exact Measurable.iSup fun n ↦
    (ha.eTotalVariationProcess_of_usual hF hc (n : ℝ≥0)).mono
      (le_iSup F (n : ℝ≥0)) le_rfl

/-- Ambient measurability retains possibly infinite variation. -/
theorem Adapted.measurable_eVariationOn_univ_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Measurable (fun ω ↦ eVariationOn (X · ω) univ) :=
  (ha.measurable_eVariationOn_univ_iSup_of_usual hF hc).mono (iSup_le F.le) le_rfl

/-- Native strong measurability here concerns ENNReal, not a norm or an
unjustified real-valued conversion of the variation. -/
theorem Adapted.stronglyMeasurable_eVariationOn_univ_iSup_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    StronglyMeasurable[⨆ t, F t] (fun ω ↦ eVariationOn (X · ω) univ) :=
  (ha.measurable_eVariationOn_univ_iSup_of_usual hF hc).stronglyMeasurable

theorem Adapted.stronglyMeasurable_eVariationOn_univ_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    StronglyMeasurable (fun ω ↦ eVariationOn (X · ω) univ) :=
  (ha.measurable_eVariationOn_univ_of_usual hF hc).stronglyMeasurable

end MeasureTheory

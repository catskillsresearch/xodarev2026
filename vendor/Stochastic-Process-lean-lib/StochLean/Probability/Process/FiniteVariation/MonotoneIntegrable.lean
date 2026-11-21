/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integrable

/-! # Integrable variation from a monotone path envelope

A zero-initial increasing process bounded on one common path event by an
integrable random variable has integrable variation on the whole half-line.
The actual extended variation is bounded before converting it to a real
number, so infinite variation cannot be hidden by the conversion.

Adaptedness, usualness, and almost-sure cadlag regularity provide measurability
of the original whole-half-line variation. Continuity and everywhere zero
initial values are not required. There is no finite-measure hypothesis and
the envelope need not be an actual terminal limit of the process.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

/-- Monotonicity and an integrable common upper envelope bound the actual
total variation and its expectation. All path assumptions share an AE event. -/
theorem HasMonotonePaths.hasIntegrableVariation_of_integrable_bound
    (hm : HasMonotonePaths B P) (ha : Adapted F B) (hF : F.IsUsual P)
    (hc : HasCadlagPaths B P) (h0 : B 0 =ᵐ[P] 0) (hiZ : Integrable Z P)
    (hb : ∀ᵐ ω ∂P, ∀ t, 0 ≤ B t ω ∧ B t ω ≤ Z ω) :
    HasIntegrableVariation B P ∧
      (∫ ω, (eVariationOn (B · ω) univ).toReal ∂P) ≤ ∫ ω, Z ω ∂P := by
  have hvar : ∀ᵐ ω ∂P, eVariationOn (B · ω) univ ≤ ENNReal.ofReal (Z ω) := by
    filter_upwards [hm, hb, h0] with ω hmω hbω h0ω
    have hz : B 0 ω = 0 := h0ω
    rw [eVariationOn_univ_eq_iSup_Icc_nat]
    apply iSup_le
    intro n
    have he := (hmω.monotoneOn univ).eVariationOn_eq
      (mem_univ (0 : ℝ≥0)) (mem_univ (n : ℝ≥0))
    simp only [univ_inter, hz, sub_zero] at he
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hbω n).2
  have hfin : HasFiniteTotalVariationPaths B P :=
    hvar.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have hreal : ∀ᵐ ω ∂P, (eVariationOn (B · ω) univ).toReal ≤ Z ω := by
    filter_upwards [hvar, hb] with ω hvω hbω
    have hZ : 0 ≤ Z ω := (hbω 0).1.trans (hbω 0).2
    simpa only [ENNReal.toReal_ofReal hZ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvω
  have hiV : Integrable (fun ω ↦ (eVariationOn (B · ω) univ).toReal) P := by
    apply hiZ.mono'
      (ha.measurable_eVariationOn_univ_of_usual hF hc).ennreal_toReal.aestronglyMeasurable
    exact hreal.mono fun _ hω ↦ by
      simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg] using hω
  exact ⟨⟨hfin, hiV⟩, integral_mono_ae hiV hiZ hreal⟩

end ProbabilityTheory

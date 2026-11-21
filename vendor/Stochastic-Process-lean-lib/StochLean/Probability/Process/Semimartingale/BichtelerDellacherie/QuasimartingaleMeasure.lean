/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.IntegrableMeasure
public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.IntegrableUnitSet
public import StochLean.Probability.Process.Path.Stopping

/-! # From Yan bounds to a finite-horizon quasimartingale

This module is the measure-theoretic consumer of Yan separation.  A bounded
density over the auxiliary integrability law preserves the compact running
supremum.  A uniform one-sided expectation bound on the symmetric integrable
unit image then controls every deterministic conditional-variation sum.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ} {P R : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- Deterministic stopping at a finite horizon, kept as a raw process so the
BD argument does not introduce another stopped-process owner. -/
def deterministicStoppedProcess (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ X (min t T) ω

theorem adapted_deterministicStoppedProcess (ha : Adapted F X) :
    Adapted F (deterministicStoppedProcess X T) := by
  intro t
  exact (ha (min t T)).mono (F.mono (min_le_left t T)) le_rfl

theorem hasCadlagPaths_deterministicStoppedProcess
    (hc : HasCadlagPaths X R) :
    HasCadlagPaths (deterministicStoppedProcess X T) R := by
  filter_upwards [hc] with ω hω
  exact hω.min_const T

variable [IsProbabilityMeasure P] [IsProbabilityMeasure R]

/-- A finite density bound over the Lemma 2 law makes the stopped process a
quasimartingale once Yan supplies a uniform expectation bound on the
integrable unit elementary-integral image. -/
theorem EquivalentIntegrabilityMeasure.isQuasimartingale_deterministicStoppedProcess
    (J : EquivalentIntegrabilityMeasure X T P)
    (ha : Adapted F X) (hc : HasCadlagPaths X P)
    {D : ℝ≥0∞} (hD : D ≠ ∞) (hRJ : R ≤ D • J.measure)
    {C : ℝ}
    (hbound : ∀ Y ∈ integrableUnitElementaryIntegralSet
      (deterministicStoppedProcess X T) F J.measure,
      (∫ ω, Y ω ∂R) ≤ C) :
    IsQuasimartingale (deterministicStoppedProcess X T) F R := by
  letI : IsProbabilityMeasure J.measure := J.isProbabilityMeasure
  let Y := deterministicStoppedProcess X T
  have hRP : R ≪ P :=
    (Measure.absolutelyContinuous_of_le_smul hRJ).trans J.absolutelyContinuous
  have hiJ : ∀ t, Integrable (Y t) J.measure := by
    intro t
    exact J.integrable (min t T) (min_le_right t T)
  have hiR : ∀ t, Integrable (Y t) R := by
    intro t
    exact (hiJ t).of_measure_le_smul hD hRJ
  let S : Ω → ℝ := fun ω ↦
    (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal
  have hSintR : Integrable S R :=
    J.integrable_compactSup.of_measure_le_smul hD hRJ
  have hterminal (t : ℝ≥0) :
      (∫ ω, |Y t ω| ∂R) ≤ ∫ ω, S ω ∂R := by
    apply integral_mono_ae (hiR t).abs hSintR
    filter_upwards [hRP.ae_le hc] with ω hω
    change |X (min t T) ω| ≤
      (denseRunningSupremum (fun s v ↦ ‖X s v‖) T ω).toReal
    rw [← Real.norm_eq_abs]
    exact le_toReal_denseRunningSupremum_of_rightContinuous
      (X := fun s v ↦ ‖X s v‖) (ω := ω)
      (min_le_right t T)
      (fun s ↦ continuous_norm.continuousAt.comp_continuousWithinAt (hω.1 s))
      (hω.denseRunningSupremum_norm_ne_top T)
  have hC : 0 ≤ C := by
    have hz := hbound 0
      (zero_mem_integrableUnitElementaryIntegralSet
        (X := Y) (F := F) (Q := J.measure))
    simpa using hz
  have hpart {U : ℝ≥0} (π : StochLean.TimePartition U) :
      (∫ ω, conditionalVariationSum Y F R π ω ∂R) ≤
        C + ∫ ω, S ω ∂R := by
    rw [integral_conditionalVariationSum_eq_signRep_add_terminal
      (F := F) (Q := R) (X := Y) hiR π]
    apply add_le_add
    · apply hbound
      exact conditionalVariationSignRep_integral_mem_integrableUnitElementaryIntegralSet
        (F := F) (Q := J.measure) (R := R) (X := Y) hiJ π
    · exact hterminal U
  refine ⟨adapted_deterministicStoppedProcess (T := T) ha,
    hasCadlagPaths_deterministicStoppedProcess (T := T) (hRP.ae_le hc), hiR, ?_⟩
  unfold HasFiniteConditionalVariation eConditionalVariation
  have hfinite : eConditionalVariation Y F R ≤
      ENNReal.ofReal (C + ∫ ω, S ω ∂R) := by
    apply iSup_le
    intro U
    apply iSup_le
    intro π
    rw [eConditionalVariationOnPartition_eq_ofReal_integral hiR π]
    exact ENNReal.ofReal_le_ofReal (hpart π)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfinite

end ProbabilityTheory

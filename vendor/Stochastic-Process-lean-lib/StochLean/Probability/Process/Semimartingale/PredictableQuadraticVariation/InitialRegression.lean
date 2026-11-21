/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Centering

/-! # Initial-value regressions for the actual angle process

An arbitrary measurable initial random variable gives a genuine constant
semimartingale whose raw quadratic variation is its initial square and whose
actual selected predictable quadratic variation is zero. Neither existence
nor uniqueness requires an initial square moment. The square-minus-angle
process cannot be a true UI martingale when that square is not integrable.

The constant-one process makes the distinction non-vacuous: even for a
continuous process, raw and predictable quadratic variation do not agree
without initial normalization. All conclusions concern the existing selected
processes, not user-supplied bracket candidates.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace StochLean.SemimartingaleRegression

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ}

/-- Actual angle construction preserves arbitrary initial data and distinguishes
raw quadratic variation from its normalized compensator. -/
theorem predictableQuadraticVariation_arbitrary_initial_constant
    (hF : F.IsUsual P) (hZ : Measurable[F 0] Z) :
    let hX := isSemimartingale_const_initial (P := P) hZ
    ∃ hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P,
      Indistinguishable (hX.quadraticVariation hF) (fun _ ω ↦ (Z ω) ^ 2) P ∧
      Indistinguishable (hX.predictableQuadraticVariation hF hQ) 0 P ∧
      (¬ Integrable (fun ω ↦ (Z ω) ^ 2) P →
        ¬ IsUIMartingale (fun t ω ↦ (Z ω) ^ 2 -
          hX.predictableQuadraticVariation hF hQ t ω) F P) ∧
      (¬ (fun ω ↦ (Z ω) ^ 2) =ᵐ[P] 0 →
        ¬ Indistinguishable (hX.quadraticVariation hF)
          (hX.predictableQuadraticVariation hF hQ) P) := by
  let hX := isSemimartingale_const_initial (P := P) hZ
  have he := quadraticVariation_const_initial hZ hF
  have hIQ : HasIntegrableVariation (hX.quadraticVariation hF) P :=
    (hasIntegrableVariation_const (fun ω ↦ (Z ω) ^ 2)).congr he.symm
  have hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P :=
    hIQ.hasLocallyIntegrableVariation
  let A := hX.predictableQuadraticVariation hF hQ
  have hL : IsLocalMartingale (hX.quadraticVariation hF) F P :=
    (isContinuousLocalMartingale_const_initial (hZ.pow_const 2)).1.congr hF
      (hX.adapted_quadraticVariation hF) he.symm
  have ha0 : Adapted F (0 : ℝ≥0 → Ω → ℝ) := fun _ ↦ measurable_const
  have hp0 : IsStronglyPredictable F (0 : ℝ≥0 → Ω → ℝ) :=
    ha0.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  have heA : Indistinguishable A 0 P := hX.predictableQuadraticVariation_unique hF hQ
    hp0 (hasIntegrableVariation_const (0 : Ω → ℝ)).hasFiniteVariationPaths
    (Eventually.of_forall fun _ ↦ rfl) (by simpa only [sub_zero] using hL)
  have hA0 : A 0 = 0 := (hX.predictableQuadraticVariation_properties hF hQ).2.2.1
  refine ⟨hQ, he, heA, ?_, ?_⟩
  · intro hni hUI
    have hi := hUI.1.integrable 0
    have he0 : (fun ω ↦ (Z ω) ^ 2 - A 0 ω) = (fun ω ↦ (Z ω) ^ 2) := by
      funext ω
      rw [hA0]
      exact sub_zero _
    exact hni (he0 ▸ hi)
  · intro hn heQA
    apply hn
    filter_upwards [he, heA, heQA] with ω hQω hAω hQAω
    exact (hQω 0).symm.trans ((hQAω 0).trans (hAω 0))

/-- The constant-one process has unequal actual raw and predictable quadratic
variations, despite having everywhere continuous finite-variation paths. -/
theorem constant_one_raw_ne_predictableQuadraticVariation (hF : F.IsUsual P) :
    let hX := isSemimartingale_const_initial (F := F) (P := P)
      (measurable_const (a := (1 : ℝ)))
    ∃ hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P,
      Indistinguishable (hX.quadraticVariation hF) 1 P ∧
      Indistinguishable (hX.predictableQuadraticVariation hF hQ) 0 P ∧
      ¬ Indistinguishable (hX.quadraticVariation hF)
        (hX.predictableQuadraticVariation hF hQ) P := by
  obtain ⟨hQ, heQ, heA, _, hn⟩ := predictableQuadraticVariation_arbitrary_initial_constant
    hF (measurable_const (a := (1 : ℝ)))
  refine ⟨hQ, ?_, heA, hn ?_⟩
  · filter_upwards [heQ] with ω hω t
    simpa using hω t
  · intro hz
    have hf : ∀ᵐ ω ∂P, False := by
      filter_upwards [hz] with ω hω
      norm_num at hω
    exact (NeZero.ne P) (by simpa using hf)

end StochLean.SemimartingaleRegression

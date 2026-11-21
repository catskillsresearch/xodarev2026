/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.ComplexBounded
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUnbounded

/-! # Almost-surely finite optional sampling for bounded complex local martingales

The existing real-coordinate local martingales become genuinely UI under the
global norm bound. Real optional sampling and conditional-expectation
commutation then recover the actual complex conditional expectation. No
evaluation at an infinite terminal time is used to assert a terminal value.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}

theorem IsComplexLocalMartingale.isUIMartingale_re_im_of_bound
    (hZ : IsComplexLocalMartingale Z F P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ C) :
    IsUIMartingale (fun t ω ↦ (Z t ω).re) F P ∧
      IsUIMartingale (fun t ω ↦ (Z t ω).im) F P := by
  constructor
  · apply hZ.1.isUIMartingale_of_bound C
    filter_upwards [hb] with ω hω t
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (Z t ω)).trans (hω t)
  · apply hZ.2.isUIMartingale_of_bound C
    filter_upwards [hb] with ω hω t
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm (Z t ω)).trans (hω t)

theorem IsComplexLocalMartingale.integrable_stoppedValue_of_ae_finite_of_bound
    (hZ : IsComplexLocalMartingale Z F P) (hF : F.IsUsual P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ C) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Integrable (stoppedValue Z τ) P := by
  obtain ⟨hR, hI⟩ := hZ.isUIMartingale_re_im_of_bound C hb
  have hi {Y : ℝ≥0 → Ω → ℝ} (hY : IsUIMartingale Y F P)
      (hr : HasRightContinuousPaths Y P) : Integrable (stoppedValue Y τ) P :=
    memLp_one_iff_integrable.mp ((hY.1.uniformIntegrable_stoppedValue_of_ae_finite_usual
      hY.2 hF hr (ι := Unit) (fun _ ↦ hτ) (fun _ ↦ hfinite)).memLp ())
  exact Integrable.re_im_iff.mp ⟨hi hR hZ.1.2.1.hasRightContinuousPaths,
    hi hI hZ.2.2.1.hasRightContinuousPaths⟩

theorem IsComplexLocalMartingale.condExp_stoppedValue_of_ae_finite_of_bound
    (hZ : IsComplexLocalMartingale Z F P) (hF : F.IsUsual P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ C) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    P[stoppedValue Z τ | hσ.measurableSpace] =ᵐ[P] stoppedValue Z σ := by
  obtain ⟨hR, hI⟩ := hZ.isUIMartingale_re_im_of_bound C hb
  have hi := hZ.integrable_stoppedValue_of_ae_finite_of_bound hF C hb hτ hfinite
  filter_upwards [hR.1.stoppedValue_ae_eq_condExp_of_ae_finite_usual hR.2 hF
      hZ.1.2.1.hasRightContinuousPaths hσ hτ hle hfinite,
    hI.1.stoppedValue_ae_eq_condExp_of_ae_finite_usual hI.2 hF
      hZ.2.2.1.hasRightContinuousPaths hσ hτ hle hfinite,
    Complex.reCLM.comp_condExp_comm (m := hσ.measurableSpace) hi,
    Complex.imCLM.comp_condExp_comm (m := hσ.measurableSpace) hi] with ω hr him hcr hci
  exact Complex.ext (hcr.trans hr.symm) (hci.trans him.symm)

end ProbabilityTheory

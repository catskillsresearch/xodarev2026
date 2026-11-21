/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.MomentCriterion

/-! # Continuous normalized bracket moments with the initial correction

The existing continuous-part owner is used. On continuous paths it is the raw
bracket minus the initial square. Its moment criterion therefore explicitly
retains initial L2 integrability. Klenke's compensated square is a true
martingale for true finite-time L2 continuous martingales, without requiring
zero initial values or creating another quadratic-variation owner.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.integrable_continuousQuadraticVariation_of_squareIntegrable
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (hM : IsSquareIntegrableMartingale X F P) (T : ℝ≥0) :
    Integrable (hX.continuousQuadraticVariation hF T) P := by
  apply ((hX.integrable_quadraticVariation_and_integral_eq hF hM T).1.sub
    (hM.2 0).integrable_sq).congr
  exact ((hX.continuousQuadraticVariation_eq_of_continuous hF hc).ae_eq T).symm

theorem IsSemimartingale.integral_continuousQuadraticVariation_eq_sub_secondMoments
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (hM : IsSquareIntegrableMartingale X F P) (T : ℝ≥0) :
    (∫ ω, hX.continuousQuadraticVariation hF T ω ∂P) =
      (∫ ω, X T ω ^ 2 ∂P) - ∫ ω, X 0 ω ^ 2 ∂P := by
  rw [integral_congr_ae ((hX.continuousQuadraticVariation_eq_of_continuous hF hc).ae_eq T),
    integral_sub (hX.integrable_quadraticVariation_and_integral_eq hF hM T).1
      (hM.2 0).integrable_sq,
    (hX.integrable_quadraticVariation_and_integral_eq hF hM T).2]

/-- Klenke 21.70(ii) for the existing normalized continuous bracket. Its
initial compensated square is the original initial square, not zero. -/
theorem IsSemimartingale.martingale_sq_sub_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (hM : IsSquareIntegrableMartingale X F P) :
    Martingale (fun t ω ↦ X t ω ^ 2 - hX.continuousQuadraticVariation hF t ω) F P := by
  have hR := hX.martingale_sq_sub_quadraticVariation_of_squareIntegrable hF hM
  have hI : Martingale (fun (_ : ℝ≥0) ω ↦ X 0 ω ^ 2) F P :=
    martingale_const_fun F P ((hX.adapted 0).pow_const 2).stronglyMeasurable
      (hM.2 0).integrable_sq
  have ha : Adapted F (fun t ω ↦ X t ω ^ 2 - hX.continuousQuadraticVariation hF t ω) :=
    fun t ↦ ((hX.adapted t).pow_const 2).sub (hX.adapted_continuousQuadraticVariation hF t)
  apply (hR.add hI).congr ha.stronglyAdapted
  intro t
  filter_upwards [(hX.continuousQuadraticVariation_eq_of_continuous hF hc).ae_eq t] with ω hω
  simp only [Pi.add_apply, hω]
  ring

/-- The normalized bracket alone cannot control a non-L2 initial variable.
Both components of the finite-time L2 criterion are retained. -/
theorem IsContinuousLocalMartingale.squareIntegrable_iff_initial_and_continuousBracket_integrable
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsSquareIntegrableMartingale X F P ↔ MemLp (X 0) 2 P ∧
      ∀ T, Integrable ((hX.isSemimartingale hF).continuousQuadraticVariation hF T) P := by
  constructor
  · intro hM
    refine ⟨hM.2 0, fun T ↦ ?_⟩
    exact (hX.isSemimartingale hF).integrable_continuousQuadraticVariation_of_squareIntegrable
      hF hX.2 hM T
  · rintro ⟨h0, hC⟩
    apply (hX.squareIntegrableMartingale_iff_integrable_quadraticVariation hF).mpr
    intro T
    apply (h0.integrable_sq.add (hC T)).congr
    filter_upwards [((hX.isSemimartingale hF).continuousQuadraticVariation_eq_of_continuous
      hF hX.2).ae_eq T] with ω hω
    change X 0 ω ^ 2 + (hX.isSemimartingale hF).continuousQuadraticVariation hF T ω =
      (hX.isSemimartingale hF).quadraticVariation hF T ω
    rw [hω]
    ring

end ProbabilityTheory

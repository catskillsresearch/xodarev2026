/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousClosure
public import StochLean.Probability.Process.Stopping.TerminalValue

/-! # Constant expected stopping values characterize closed martingales

Protter I.21 tests every stopping time, including infinity. The existing
terminal-valued stopping owner supplies the explicit terminal variable.
Stopping at t on a past event and at infinity on its complement identifies
the conditional expectation. The proof needs adaptedness but no path
regularity. The terminal input is a closing variable; it is not asserted
to equal the actual path limit without the appropriate terminal projection.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

/-- Equal expectations for all stopped values, with integrability explicitly
required, recover the closing conditional expectations. The common mean need
not be zero, so arbitrary initial means are retained. -/
theorem integrable_closing_of_expected_stopping_eq (ha : StronglyAdapted F X)
    (h : ∀ (τ : Ω → WithTop ℝ≥0), IsStoppingTime F τ →
      Integrable (stoppedValueWithTerminal X Z τ) P ∧
        (∫ ω, stoppedValueWithTerminal X Z τ ω ∂P) = ∫ ω, Z ω ∂P) :
    Integrable Z P ∧ ∀ t, X t =ᵐ[P] P[Z | F t] := by
  classical
  have htop : IsStoppingTime F (fun _ : Ω ↦ (⊤ : WithTop ℝ≥0)) := by
    intro t
    simpa only [WithTop.not_top_le_coe, Set.ofPred_false] using
      (@MeasurableSet.empty Ω (F t))
  have hZ : Integrable Z P := by simpa only [stoppedValueWithTerminal_top] using (h _ htop).1
  refine ⟨hZ, fun t ↦ ?_⟩
  have ht : Integrable (X t) P := by
    simpa only [stoppedValueWithTerminal_coe] using (h _ (isStoppingTime_const F t)).1
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le t) hZ
    (fun _ _ _ ↦ ht.integrableOn) _ (ha t).aestronglyMeasurable
  intro A hA _
  let τ : Ω → WithTop ℝ≥0 := A.piecewise (fun _ ↦ t) (fun _ ↦ ⊤)
  have hτ : IsStoppingTime F τ :=
    (isStoppingTime_const F t).piecewise_of_le htop (fun _ ↦ le_rfl) (fun _ ↦ le_top) hA
  have he : stoppedValueWithTerminal X Z τ = A.piecewise (X t) Z := by
    funext ω
    by_cases hω : ω ∈ A
    · have hτw : τ ω = (t : WithTop ℝ≥0) := by simp only [τ, Set.piecewise, if_pos hω]
      simp only [Set.piecewise, if_pos hω]
      change (if τ ω = ⊤ then Z ω else X (τ ω).untopA ω) = X t ω
      rw [hτw]
      exact if_neg WithTop.coe_ne_top
    · simp only [Set.piecewise, if_neg hω]
      apply stoppedValueWithTerminal_of_top
      simp only [τ, Set.piecewise, if_neg hω]
  have hs := (h τ hτ).2
  rw [he, integral_piecewise (F.le t A hA) ht.integrableOn hZ.integrableOn] at hs
  have hz := integral_add_compl (F.le t A hA) hZ
  linarith

theorem martingale_uniformIntegrable_of_expected_stopping_eq (ha : Adapted F X)
    (h : ∀ (τ : Ω → WithTop ℝ≥0), IsStoppingTime F τ →
      Integrable (stoppedValueWithTerminal X Z τ) P ∧
        (∫ ω, stoppedValueWithTerminal X Z τ ω ∂P) = ∫ ω, Z ω ∂P) :
    Martingale X F P ∧ UniformIntegrable X 1 P := by
  have hsa : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  obtain ⟨hZ, hclose⟩ := integrable_closing_of_expected_stopping_eq hsa h
  exact ⟨(martingale_condExp Z F P).congr hsa (fun t ↦ (hclose t).symm),
    Martingale.uniformIntegrable_of_integrable_closing hZ hclose⟩

/-- Protter I.21. The assumption ranges over finite and infinite stopping
times and includes their integrability; it is not a bounded-stopping test. -/
theorem martingale_uniformIntegrable_of_zero_expected_stopping (ha : Adapted F X)
    (h : ∀ (τ : Ω → WithTop ℝ≥0), IsStoppingTime F τ →
      Integrable (stoppedValueWithTerminal X Z τ) P ∧
        (∫ ω, stoppedValueWithTerminal X Z τ ω ∂P) = 0) :
    Martingale X F P ∧ UniformIntegrable X 1 P := by
  have htop : IsStoppingTime F (fun _ : Ω ↦ (⊤ : WithTop ℝ≥0)) := by
    intro t
    simpa only [WithTop.not_top_le_coe, Set.ofPred_false] using
      (@MeasurableSet.empty Ω (F t))
  have hz : (∫ ω, Z ω ∂P) = 0 := by
    simpa only [stoppedValueWithTerminal_top] using (h _ htop).2
  apply martingale_uniformIntegrable_of_expected_stopping_eq (Z := Z) ha
  intro τ hτ
  exact ⟨(h τ hτ).1, (h τ hτ).2.trans hz.symm⟩

end MeasureTheory

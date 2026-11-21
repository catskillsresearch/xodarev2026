/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.ConditionalProjection
public import StochLean.Probability.Martingale.Convergence.Regularization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Cadlag versions of dominated monotone conditional projections

The input family need not be adapted. Right continuity and an integrable
dominating function imply right-continuous expectations, so Doob regularization
applies to its conditional projection. This is an existence theorem for a
consistent version, not a path-regularity assertion about arbitrary coordinate
representatives of conditional expectation.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

theorem isRightContinuousPath_integral_of_dominated
    (hm : ∀ t, AEStronglyMeasurable (X t) P) (hr : HasRightContinuousPaths X P)
    {g : Ω → ℝ} (hg : Integrable g P) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ g ω) :
    IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  intro t
  exact tendsto_integral_filter_of_dominated_convergence g
    (Eventually.of_forall hm) (Eventually.of_forall hb) hg
    (hr.mono fun _ hω ↦ hω t)

variable [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}

theorem exists_cadlag_condExp_of_ae_monotone
    (hF : F.IsUsual P) (hm : ∀ t, AEStronglyMeasurable (X t) P)
    (hr : HasRightContinuousPaths X P) {g : Ω → ℝ} (hg : Integrable g P)
    (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ g ω)
    (hmono : ∀ s t, s ≤ t → X s ≤ᵐ[P] X t) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Submartingale Y F P ∧ HasCadlagPaths Y P ∧
      IsModification (fun t ↦ P[X t | F t]) Y P := by
  have hi (t) : Integrable (X t) P := hg.mono' (hm t) (hb t)
  have hS := submartingale_condExp_of_ae_monotone (F := F) hi hmono
  have he : (fun t ↦ ∫ ω, P[X t | F t] ω ∂P) = fun t ↦ ∫ ω, X t ω ∂P := by
    funext t
    exact integral_condExp (F.le t)
  have hmean := isRightContinuousPath_integral_of_dominated hm hr hg hb
  rw [← he] at hmean
  obtain ⟨Y, hY, hc, hmod, _⟩ := hS.exists_cadlag_modification hF hmean
  exact ⟨Y, hY, hc, hmod⟩

theorem exists_cadlag_condExp_of_ae_antitone
    (hF : F.IsUsual P) (hm : ∀ t, AEStronglyMeasurable (X t) P)
    (hr : HasRightContinuousPaths X P) {g : Ω → ℝ} (hg : Integrable g P)
    (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ g ω)
    (hanti : ∀ s t, s ≤ t → X t ≤ᵐ[P] X s) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Supermartingale Y F P ∧ HasCadlagPaths Y P ∧
      IsModification (fun t ↦ P[X t | F t]) Y P := by
  have hi (t) : Integrable (X t) P := hg.mono' (hm t) (hb t)
  have hS := supermartingale_condExp_of_ae_antitone (F := F) hi hanti
  have he : (fun t ↦ ∫ ω, P[X t | F t] ω ∂P) = fun t ↦ ∫ ω, X t ω ∂P := by
    funext t
    exact integral_condExp (F.le t)
  have hmean := isRightContinuousPath_integral_of_dominated hm hr hg hb
  rw [← he] at hmean
  obtain ⟨Y, hY, hc, hmod, _⟩ := hS.exists_cadlag_modification hF hmean
  exact ⟨Y, hY, hc, hmod⟩

end MeasureTheory

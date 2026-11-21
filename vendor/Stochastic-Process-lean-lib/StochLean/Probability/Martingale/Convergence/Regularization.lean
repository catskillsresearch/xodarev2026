/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.RegularizationModification
public import StochLean.Probability.Martingale.Convergence.RegularizationNecessity

/-! # Doob regularization under usual conditions

For real submartingales and supermartingales, right-continuous expectations
are equivalent to existence of a cadlag modification. The constructed version
keeps the same one-sided martingale class and is unique up to indistinguishability.
True martingales always admit such a version; a right-continuous true martingale
already has cadlag paths. No L2, UI, global moment bound or initial normalization
is required.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.exists_cadlag_modification
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hmean : IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Supermartingale Y F P ∧ HasCadlagPaths Y P ∧
      IsModification X Y P ∧ ∀ Z : ℝ≥0 → Ω → ℝ,
        IsModification X Z P → HasRightContinuousPaths Z P → Indistinguishable Y Z P := by
  have hm := hX.isModification_dyadicRightLimitProcess hF hmean
  have hc := hX.hasCadlagPaths_dyadicRightLimitProcess
  refine ⟨dyadicRightLimitProcess X, hX.congr (hX.stronglyAdapted_dyadicRightLimitProcess hF) hm,
    hc, hm, fun Z hZ hrZ ↦ ?_⟩
  exact (hm.symm.trans hZ).indistinguishable_of_rightContinuous hc.hasRightContinuousPaths hrZ

theorem Submartingale.exists_cadlag_modification
    (hX : Submartingale X F P) (hF : F.IsUsual P)
    (hmean : IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Submartingale Y F P ∧ HasCadlagPaths Y P ∧
      IsModification X Y P ∧ ∀ Z : ℝ≥0 → Ω → ℝ,
        IsModification X Z P → HasRightContinuousPaths Z P → Indistinguishable Y Z P := by
  have hm := hX.isModification_dyadicRightLimitProcess hF hmean
  have hc := hX.hasCadlagPaths_dyadicRightLimitProcess
  refine ⟨dyadicRightLimitProcess X, hX.congr (hX.stronglyAdapted_dyadicRightLimitProcess hF) hm,
    hc, hm, fun Z hZ hrZ ↦ ?_⟩
  exact (hm.symm.trans hZ).indistinguishable_of_rightContinuous hc.hasRightContinuousPaths hrZ

theorem Supermartingale.exists_cadlag_modification_iff
    (hX : Supermartingale X F P) (hF : F.IsUsual P) :
    (∃ Y : ℝ≥0 → Ω → ℝ, IsModification X Y P ∧ HasCadlagPaths Y P) ↔
      IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  constructor
  · rintro ⟨Y, hm, hc⟩
    exact hX.isRightContinuousPath_integral_of_modification hF hm hc.hasRightContinuousPaths
  · intro hmean
    obtain ⟨Y, _, hc, hm, _⟩ := hX.exists_cadlag_modification hF hmean
    exact ⟨Y, hm, hc⟩

theorem Submartingale.exists_cadlag_modification_iff
    (hX : Submartingale X F P) (hF : F.IsUsual P) :
    (∃ Y : ℝ≥0 → Ω → ℝ, IsModification X Y P ∧ HasCadlagPaths Y P) ↔
      IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  constructor
  · rintro ⟨Y, hm, hc⟩
    exact hX.isRightContinuousPath_integral_of_modification hF hm hc.hasRightContinuousPaths
  · intro hmean
    obtain ⟨Y, _, hc, hm, _⟩ := hX.exists_cadlag_modification hF hmean
    exact ⟨Y, hm, hc⟩

theorem Martingale.isRightContinuousPath_integral (hX : Martingale X F P) :
    IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  have he : (fun t ↦ ∫ ω, X t ω ∂P) = fun _ ↦ ∫ ω, X 0 ω ∂P := by
    funext t
    simpa only [setIntegral_univ] using
      (hX.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) (@MeasurableSet.univ Ω (F 0))).symm
  rw [he]
  exact fun _ ↦ continuousWithinAt_const

theorem Martingale.exists_cadlag_modification (hX : Martingale X F P) (hF : F.IsUsual P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y F P ∧ HasCadlagPaths Y P ∧
      IsModification X Y P ∧ ∀ Z : ℝ≥0 → Ω → ℝ,
        IsModification X Z P → HasRightContinuousPaths Z P → Indistinguishable Y Z P := by
  have hm := hX.supermartingale.isModification_dyadicRightLimitProcess hF
    hX.isRightContinuousPath_integral
  have hc := hX.supermartingale.hasCadlagPaths_dyadicRightLimitProcess
  refine ⟨dyadicRightLimitProcess X,
    hX.congr (hX.supermartingale.stronglyAdapted_dyadicRightLimitProcess hF) hm,
    hc, hm, fun Z hZ hrZ ↦ ?_⟩
  exact (hm.symm.trans hZ).indistinguishable_of_rightContinuous hc.hasRightContinuousPaths hrZ

theorem Supermartingale.hasCadlagPaths_of_rightContinuous (hX : Supermartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) : HasCadlagPaths X P := by
  obtain ⟨Y, _, hc, hm, _⟩ := hX.exists_cadlag_modification hF
    (hX.isRightContinuousPath_integral hr)
  exact hc.congr (hm.indistinguishable_of_rightContinuous hr hc.hasRightContinuousPaths).symm

theorem Submartingale.hasCadlagPaths_of_rightContinuous (hX : Submartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) : HasCadlagPaths X P := by
  obtain ⟨Y, _, hc, hm, _⟩ := hX.exists_cadlag_modification hF
    (hX.isRightContinuousPath_integral hr)
  exact hc.congr (hm.indistinguishable_of_rightContinuous hr hc.hasRightContinuousPaths).symm

theorem Martingale.hasCadlagPaths_of_rightContinuous (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) : HasCadlagPaths X P :=
  hX.supermartingale.hasCadlagPaths_of_rightContinuous hF hr

end MeasureTheory

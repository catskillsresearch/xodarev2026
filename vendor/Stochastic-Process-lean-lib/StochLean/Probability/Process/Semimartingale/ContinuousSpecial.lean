/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.BoundedJumpSpecial
public import StochLean.Probability.Process.Path.ContinuousOfJump

/-! # Continuous classical semimartingales have continuous predictable parts

The actual bounded-jump predictable decomposition is applied with bound zero.
Its two parts have vanishing positive-time jumps, so their cadlag paths are
continuous on a common full-measure event. No claim about the initial jump is
needed: the original arbitrary initial value is retained separately, and both
constructed components start exactly at zero.

The reconstruction remains an exact equality of the constructed processes.
Continuity is almost sure, matching the source hypothesis; the predictable
part also retains the everywhere cadlag version supplied by the construction.
No initial moment, candidate decomposition, or new component selector is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The continuous case of Protter III.35: actual continuous local-martingale
and predictable locally IV parts, with exact normalization and reconstruction. -/
theorem IsClassicalSemimartingale.exists_continuous_predictable_decomposition
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    ∃ L A : ℝ≥0 → Ω → ℝ,
      IsContinuousLocalMartingale L F P ∧ IsStronglyPredictable F A ∧
      HasContinuousPaths A P ∧ (∀ ω, IsCadlagPath (A · ω)) ∧
      L 0 = 0 ∧ A 0 = 0 ∧ HasLocallyIntegrableVariation A F P ∧
      X = (fun _ ↦ X 0) + L + A := by
  have hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ (0 : ℝ) := by
    filter_upwards [hc] with ω hω t ht
    rw [hω.jumpProcess_eq_zero (ne_of_gt ht), norm_zero]
  obtain ⟨L, A, hL, hpA, hcA, hL0, hA0, hvA, he, hbound⟩ :=
    hX.exists_predictable_decomposition_of_jump_bound hF le_rfl hj
  have hzero : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 →
      jumpProcess A t ω = 0 ∧ jumpProcess L t ω = 0 := by
    filter_upwards [hbound] with ω hω t ht
    have ha := (hω t (pos_iff_ne_zero.mpr ht)).1
    have hl : ‖jumpProcess L t ω‖ ≤ 0 := by
      simpa only [mul_zero] using (hω t (pos_iff_ne_zero.mpr ht)).2
    exact ⟨norm_eq_zero.mp (le_antisymm ha (norm_nonneg _)),
      norm_eq_zero.mp (le_antisymm hl (norm_nonneg _))⟩
  have hcontA : HasContinuousPaths A P :=
    HasCadlagPaths.hasContinuousPaths_of_jumpProcess_eq_zero (Eventually.of_forall hcA)
      (hzero.mono fun _ hω t ht ↦ (hω t ht).1)
  have hcontL : HasContinuousPaths L P :=
    hL.2.1.hasContinuousPaths_of_jumpProcess_eq_zero
      (hzero.mono fun _ hω t ht ↦ (hω t ht).2)
  exact ⟨L, A, ⟨hL, hcontL⟩, hpA, hcontA, hcA, hL0, hA0, hvA, he⟩

/-- Continuous classical semimartingales are special, through the actual
continuous predictable decomposition and with no initial-integrability premise. -/
theorem IsClassicalSemimartingale.isSpecialSemimartingale_of_continuous
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) : IsSpecialSemimartingale X F P := by
  obtain ⟨L, A, hL, hpA, _, hcA, hL0, hA0, hvA, he⟩ :=
    hX.exists_continuous_predictable_decomposition hF hc
  exact ⟨hX.1, hX.2.1, L, A, hL.1, hpA, Eventually.of_forall hcA,
    hvA.hasFiniteVariationPaths, Eventually.of_forall (fun ω ↦ congrFun hL0 ω),
    Eventually.of_forall (fun ω ↦ congrFun hA0 ω),
    Eventually.of_forall (fun ω t ↦ congrFun (congrFun he t) ω)⟩

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Stability

/-! # Reducing times and initial-event masking: Protter I.48(a,c,d) -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
theorem IsUIMartingale.add (hX : IsUIMartingale X F P) (hY : IsUIMartingale Y F P) :
    IsUIMartingale (X + Y) F P := ⟨hX.1.add hY.1, hX.2.add hY.2 le_rfl⟩

theorem IsUIMartingale.neg (hX : IsUIMartingale X F P) : IsUIMartingale (-X) F P := by
  simpa only [neg_one_smul] using hX.const_smul (-1)

theorem IsUIMartingale.sub (hX : IsUIMartingale X F P) (hY : IsUIMartingale Y F P) :
    IsUIMartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

omit [IsFiniteMeasure P] in
theorem IsLocalMartingale.indicator_initial (hX : IsLocalMartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsLocalMartingale (fun t ↦ s.indicator (X t)) F P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨fun t ↦ (hX.1 t).indicator (F.mono bot_le s hs), hX.2.1.indicator s,
    τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  simpa only [stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm] using
    (hτ.2.2 n).indicator_initial hs

theorem IsLocalMartingale.masked_stoppedProcess (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsLocalMartingale (MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) F P := by
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using (hτ 0).compl
  exact (hX.indicator_initial hs).stoppedProcess hF hτ

/-- The source AE order is sufficient; no pointwise order replacement is assumed. -/
theorem IsReducingStoppingTime.of_ae_le (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) {σ τ : Ω → WithTop ℝ≥0}
    (hτ : IsReducingStoppingTime X F P τ) (hσ : IsStoppingTime F σ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) : IsReducingStoppingTime X F P σ := by
  have hstop := hτ.2.stoppedProcess_of_usual hF
    (hX.2.1.stoppedProcess τ).hasRightContinuousPaths hσ
  have heq (t : ℝ≥0) : stoppedProcess (stoppedProcess X τ) σ t =ᵐ[P] stoppedProcess X σ t := by
    filter_upwards [hle] with ω hω
    rw [stoppedProcess_stoppedProcess']
    simp only [stoppedProcess, min_eq_left hω]
  exact ⟨hσ, hstop.1.congr
    (hX.1.stronglyAdapted.stoppedProcess_of_usual hF hX.2.1.hasRightContinuousPaths hσ) heq,
    hstop.2.ae_eq heq⟩

omit [IsFiniteMeasure P] in
theorem stoppedProcess_max_eq_add_sub_min (σ τ : Ω → WithTop ℝ≥0) :
    stoppedProcess X (fun ω ↦ max (σ ω) (τ ω)) =
      stoppedProcess X σ + stoppedProcess X τ - stoppedProcess X (fun ω ↦ min (σ ω) (τ ω)) := by
  ext t ω
  simp only [Pi.sub_apply, Pi.add_apply, stoppedProcess]
  by_cases h : σ ω ≤ τ ω
  · rw [max_eq_right h, min_eq_left h]
    ring
  · have h' := le_of_not_ge h
    rw [max_eq_left h', min_eq_right h']
    ring

theorem IsReducingStoppingTime.max (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsReducingStoppingTime X F P σ) (hτ : IsReducingStoppingTime X F P τ) :
    IsReducingStoppingTime X F P (fun ω ↦ max (σ ω) (τ ω)) := by
  have hmin := hσ.of_ae_le hX hF (hσ.1.min hτ.1)
    (ae_of_all _ fun _ ↦ min_le_left _ _)
  refine ⟨hσ.1.max hτ.1, ?_⟩
  rw [stoppedProcess_max_eq_add_sub_min]
  exact (hσ.2.add hτ.2).sub hmin.2

end ProbabilityTheory

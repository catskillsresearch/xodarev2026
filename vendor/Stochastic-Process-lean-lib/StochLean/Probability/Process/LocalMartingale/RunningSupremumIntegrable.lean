/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.RunningSupremum

/-! # Integrable terminal bounds for stopped running suprema

The original running norm supremum, stopped along actual localizing times,
has an integrable bound on the whole half-line. Its countable extended
terminal supremum is proved finite before its real value is shown integrable.
All suprema use the existing `denseRunningSupremum` owner.

Arbitrary initial values require the native positive-lifetime masks. An
integrable initial value allows removal of these masks, with the initial
norm explicitly accounting for zero lifetimes. In particular this gives
the unmasked zero-initial form of Protter III.38.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

private theorem integer_runningSupremum_integrable_of_envelope
    {Y : ℝ≥0 → Ω → ℝ} {G : Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (Y t) P) (hG : Integrable G P)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω) :
    (∀ᵐ ω ∂P,
      (⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω) ≠ ∞) ∧
    Integrable (fun ω ↦
      (⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω).toReal) P := by
  let Z : Ω → ℝ≥0∞ := fun ω ↦
    ⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω
  have hmZ : AEMeasurable Z P := by
    dsimp only [Z, denseRunningSupremum]
    exact AEMeasurable.iSup fun k ↦ AEMeasurable.iSup fun j ↦
      (hm (denseTimeUpTo (k : ℝ≥0) j)).norm.aemeasurable.ennreal_ofReal
  have hbZ : ∀ᵐ ω ∂P, Z ω ≤ ENNReal.ofReal (G ω) := by
    filter_upwards [hb] with ω hω
    exact iSup_le fun _ ↦ denseRunningSupremum_le_of_le (fun t _ ↦ hω t)
  have hfZ : ∀ᵐ ω ∂P, Z ω ≠ ∞ :=
    hbZ.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  refine ⟨hfZ, hG.mono' hmZ.ennreal_toReal.aestronglyMeasurable ?_⟩
  filter_upwards [hb, hbZ, hfZ] with ω hω hle hf
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hG0 : 0 ≤ G ω := (norm_nonneg (Y 0 ω)).trans (hω 0)
  have ht := (ENNReal.toReal_le_toReal hf ENNReal.ofReal_ne_top).mpr hle
  simpa only [ENNReal.toReal_ofReal hG0] using ht

variable [IsProbabilityMeasure P]

private theorem aestronglyMeasurable_masked_stopped_runningSupremum
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (T : ℝ≥0) :
    AEStronglyMeasurable (MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator
        (fun ω ↦ (denseRunningSupremum (fun s v ↦ ‖M s v‖) t ω).toReal)) τ T) P := by
  let X := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (M t)) τ
  have haX : Adapted F X := (hM.masked_stoppedProcess hF hτ).1
  have hm : Measurable (denseRunningSupremum (fun t ω ↦ ‖X t ω‖) T) :=
    measurable_denseRunningSupremum
      (fun t ↦ ((haX t).mono (F.le t) le_rfl).norm) T
  apply hm.ennreal_toReal.aestronglyMeasurable.congr
  filter_upwards [hM.2.1] with ω hω
  exact denseRunningSupremum_norm_masked_stoppedProcess hω.1 τ T

/-- Native masked localizations of the original running norm supremum admit
whole-half-line integrable envelopes and finite integrable terminal suprema.
No moment assumption is imposed on the original initial value. -/
theorem IsLocalMartingale.exists_integrable_masked_stopped_runningSupremum
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) :
    let S : ℝ≥0 → Ω → ℝ := fun t ω ↦
      (denseRunningSupremum (fun s v ↦ ‖M s v‖) t ω).toReal
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧
      ∀ n,
        let Y := MeasureTheory.stoppedProcess
          (fun t ↦ {ω | 0 < τ n ω}.indicator (S t)) (τ n)
        ∃ G : Ω → ℝ, Integrable G P ∧
          (∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω) ∧
          (∀ᵐ ω ∂P,
            (⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω) ≠ ∞) ∧
          Integrable (fun ω ↦
            (⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω).toReal) P := by
  let S : ℝ≥0 → Ω → ℝ := fun t ω ↦
    (denseRunningSupremum (fun s v ↦ ‖M s v‖) t ω).toReal
  obtain ⟨τ, hτ, hG⟩ := hM.locally_integrable_envelope hF
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let X := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (M t)) (τ n)
  let Y := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (S t)) (τ n)
  obtain ⟨G, hiG, hb⟩ := hG n
  change ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ G ω at hb
  have hbY : ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω := by
    filter_upwards [hb, hM.2.1] with ω hω hc t
    have he := denseRunningSupremum_norm_masked_stoppedProcess hc.1 (τ n) t
    change (denseRunningSupremum (fun s v ↦ ‖X s v‖) t ω).toReal = Y t ω at he
    rw [← he, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact denseRunningSupremum_toReal_le
      ((norm_nonneg (X 0 ω)).trans (hω 0)) (fun s _ ↦ hω s)
  have hmY : ∀ t, AEStronglyMeasurable (Y t) P := fun t ↦
    aestronglyMeasurable_masked_stopped_runningSupremum hM hF (hτ.isStoppingTime n) t
  exact ⟨G, hiG, hbY, integer_runningSupremum_integrable_of_envelope hmY hiG hbY⟩

/-- With an integrable initial value, the original running norm supremum
has unmasked stopped whole-half-line integrable envelopes and terminal
suprema. The initial norm controls exactly the zero-lifetime contribution. -/
theorem IsLocalMartingale.exists_integrable_stopped_runningSupremum
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) (hi0 : Integrable (M 0) P) :
    let S : ℝ≥0 → Ω → ℝ := fun t ω ↦
      (denseRunningSupremum (fun s v ↦ ‖M s v‖) t ω).toReal
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧
      ∀ n,
        let Y := MeasureTheory.stoppedProcess S (τ n)
        ∃ G : Ω → ℝ, Integrable G P ∧
          (∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω) ∧
          (∀ᵐ ω ∂P,
            (⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω) ≠ ∞) ∧
          Integrable (fun ω ↦
            (⨆ k : ℕ, denseRunningSupremum (fun t v ↦ ‖Y t v‖) k ω).toReal) P := by
  let S : ℝ≥0 → Ω → ℝ := fun t ω ↦
    (denseRunningSupremum (fun s v ↦ ‖M s v‖) t ω).toReal
  have hS0 : S 0 = fun ω ↦ ‖M 0 ω‖ := by
    funext ω
    simp only [S, denseRunningSupremum, denseTimeUpTo, zero_min, iSup_const,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  obtain ⟨τ, hτ, hG⟩ := hM.exists_integrable_masked_stopped_runningSupremum hF
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let Y := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (S t)) (τ n)
  let Z := MeasureTheory.stoppedProcess S (τ n)
  let B : Ω → ℝ := {ω | τ n ω = 0}.indicator (S 0)
  obtain ⟨G, hiG, hb, _⟩ := hG n
  change ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω at hb
  have hiB : Integrable B P := by
    dsimp only [B]
    rw [hS0]
    exact hi0.norm.indicator (F.le 0 _ ((hτ.isStoppingTime n).measurableSet_eq 0))
  have he : Z = Y + fun _ ↦ B := stoppedProcess_eq_masked_add_initial (X := S) (τ n)
  have hmY : ∀ t, AEStronglyMeasurable (Y t) P := fun t ↦
    aestronglyMeasurable_masked_stopped_runningSupremum hM hF (hτ.isStoppingTime n) t
  have hmZ : ∀ t, AEStronglyMeasurable (Z t) P := by
    intro t
    rw [he]
    exact (hmY t).add hiB.aestronglyMeasurable
  have hbZ : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ G ω + ‖M 0 ω‖ := by
    filter_upwards [hb] with ω hω t
    rw [he]
    change ‖Y t ω + B ω‖ ≤ G ω + ‖M 0 ω‖
    have hB : ‖B ω‖ ≤ ‖M 0 ω‖ := by
      simpa only [B, hS0, norm_norm] using
        (norm_indicator_le_norm_self (s := {ω | τ n ω = 0}) (S 0) ω)
    exact (norm_add_le _ _).trans (add_le_add (hω t) hB)
  exact ⟨fun ω ↦ G ω + ‖M 0 ω‖, hiG.add hi0.norm, hbZ,
    integer_runningSupremum_integrable_of_envelope hmZ (hiG.add hi0.norm) hbZ⟩

end ProbabilityTheory

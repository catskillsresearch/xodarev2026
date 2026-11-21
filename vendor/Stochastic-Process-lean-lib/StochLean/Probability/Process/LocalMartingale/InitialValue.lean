/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale
public import Mathlib.Tactic.Positivity

/-! # Initial-value safeguards for local martingales

Any finite F₀-measurable random variable defines a constant Protter local
martingale, even without integrability. Unmasked localization cannot remove
the initial value or make an unbounded initial value bounded.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Z : Ω → ℝ}

/-- A concrete fundamental sequence for a constant process with arbitrary finite initial value. -/
noncomputable def initialValueLocalizer (Z : Ω → ℝ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if |Z ω| ≤ n then ⊤ else 0

theorem initialValueLocalizer_isStoppingTime (hZ : Measurable[F 0] Z) (n : ℕ) :
    IsStoppingTime F (initialValueLocalizer Z n) := by
  intro t
  have hs : MeasurableSet[F t] {ω | |Z ω| ≤ (n : ℝ)} :=
    F.mono bot_le _ (by
      let : MeasurableSpace Ω := F 0
      simpa only [Real.norm_eq_abs] using measurableSet_le hZ.norm measurable_const)
  convert hs.compl using 1
  ext ω
  by_cases h : |Z ω| ≤ (n : ℝ)
  · simp only [initialValueLocalizer, h, ↓reduceIte, mem_compl_iff, mem_ofPred_eq,
      not_true_eq_false, iff_false]
    exact WithTop.not_top_le_coe t
  · simp only [initialValueLocalizer, h, ↓reduceIte, mem_compl_iff, mem_ofPred_eq,
      not_false_eq_true]
    exact iff_true_intro bot_le

theorem initialValueLocalizer_monotone (Z : Ω → ℝ) : Monotone (initialValueLocalizer Z) := by
  intro n m hnm ω
  by_cases hn : |Z ω| ≤ (n : ℝ)
  · have hm : |Z ω| ≤ (m : ℝ) := hn.trans (by exact_mod_cast hnm)
    simp [initialValueLocalizer, hn, hm]
  · simp only [initialValueLocalizer, hn, ↓reduceIte]
    exact bot_le

theorem initialValueLocalizer_tendsto (Z : Ω → ℝ) (ω : Ω) :
    Tendsto (fun n ↦ initialValueLocalizer Z n ω) atTop (𝓝 ⊤) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |Z ω|
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
  have h : |Z ω| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  simp [initialValueLocalizer, h]

theorem initialValueLocalizer_isFundamentalSequence [IsFiniteMeasure P]
    [SigmaFiniteFiltration P F] (hZ : Measurable[F 0] Z) :
    IsFundamentalSequence (fun _ : ℝ≥0 ↦ Z) F P (initialValueLocalizer Z) := by
  refine ⟨⟨initialValueLocalizer_isStoppingTime hZ,
    ae_of_all _ (initialValueLocalizer_tendsto Z)⟩,
    initialValueLocalizer_monotone Z, fun n ↦ ?_⟩
  let s : Set Ω := {ω | |Z ω| ≤ (n : ℝ)}
  have hs : MeasurableSet[F 0] s := by
    let : MeasurableSpace Ω := F 0
    simpa only [Real.norm_eq_abs] using measurableSet_le hZ.norm measurable_const
  have hb : ∀ ω, ‖s.indicator Z ω‖ ≤ (n : ℝ) := by
    intro ω
    by_cases h : ω ∈ s
    · simpa only [Set.indicator_of_mem h, Real.norm_eq_abs] using
        (show |Z ω| ≤ (n : ℝ) from h)
    · simp [Set.indicator_of_notMem h]
  have hm := hZ.stronglyMeasurable.indicator hs
  have hlp : MemLp (s.indicator Z) 1 P :=
    MemLp.of_bound (hm.mono (F.le 0)).aestronglyMeasurable n (ae_of_all _ hb)
  have hui : IsUIMartingale (fun _ : ℝ≥0 ↦ s.indicator Z) F P :=
    ⟨martingale_const_fun F P hm (memLp_one_iff_integrable.mp hlp),
      uniformIntegrable_const le_rfl (by simp) hlp⟩
  have heq : stoppedProcess
      (fun _ : ℝ≥0 ↦ {ω | 0 < initialValueLocalizer Z n ω}.indicator Z)
      (initialValueLocalizer Z n) = fun _ : ℝ≥0 ↦ s.indicator Z := by
    rw [stoppedProcess_const]
    funext t ω
    by_cases h : |Z ω| ≤ (n : ℝ) <;> simp [initialValueLocalizer, s, h]
  rwa [heq]

/-- Integrability is deliberately absent: the Protter mask localizes the initial random value. -/
theorem isContinuousLocalMartingale_const_initial [IsFiniteMeasure P]
    [SigmaFiniteFiltration P F] (hZ : Measurable[F 0] Z) :
    IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ Z) F P := by
  have hcont : HasContinuousPaths (fun _ : ℝ≥0 ↦ Z) P :=
    ae_of_all _ fun _ ↦ continuous_const
  exact ⟨⟨fun t ↦ hZ.mono (F.mono bot_le) le_rfl, hcont.hasCadlagPaths,
    initialValueLocalizer Z, initialValueLocalizer_isFundamentalSequence hZ⟩, hcont⟩

/-- A nonintegrable constant process has no unmasked Klenke localizer. -/
theorem not_exists_klenkeLocalizingSequence_const (hZ : ¬ Integrable Z P) :
    ¬ ∃ τ, IsKlenkeLocalizingSequence (fun _ : ℝ≥0 ↦ Z) F P τ := by
  rintro ⟨τ, hτ⟩
  exact hZ hτ.integrable_initial

/-- The source residual at time zero fails without the square-integrable initial-value guard. -/
theorem not_exists_klenkeLocalizingSequence_const_sq
    (hZ : ¬ Integrable (fun ω ↦ Z ω ^ 2) P) :
    ¬ ∃ τ, IsKlenkeLocalizingSequence (fun _ : ℝ≥0 ↦ fun ω ↦ Z ω ^ 2) F P τ :=
  not_exists_klenkeLocalizingSequence_const hZ

/-- No stopping time can make a globally unbounded initial value globally bounded. -/
theorem not_bounded_stoppedProcess_of_unbounded_initial {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ C : ℝ, ∃ ω, C < |X 0 ω|) (τ : Ω → WithTop ℝ≥0) :
    ¬ ∃ C : ℝ, ∀ t ω, |stoppedProcess X τ t ω| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨ω, hω⟩ := hX C
  have h := hC 0 ω
  rw [stoppedProcess_eq_of_le (show (0 : ℝ≥0) ≤ τ ω from bot_le)] at h
  exact (not_le_of_gt hω) h

end ProbabilityTheory

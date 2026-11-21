/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import StochLean.Probability.Process.LocalMartingale.FiniteLinearCombination
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.FiniteVariationPerturbation
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartStopping

/-! # Stopping inside a region without losing arbitrary initial values

If the stopping time is zero, replace the stopped path by a prescribed point
of the region. This is an F0-measurable random constant perturbation, hence
preserves the canonical continuous square and mixed brackets. On the positive
stopping event the original stopped coordinates are unchanged. This supplies
the initial-event branch needed for open-domain Ito localization.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

theorem exists_region_patched_stopped_coordinates
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hτ : IsStoppingTime F τ) {R : (ι → ℝ) → Prop} (c : ι → ℝ) (hc : R c)
    (hstay : ∀ᵐ ω ∂P, 0 < τ ω → ∀ t, R (fun i ↦ stoppedProcess (X i) τ t ω)) :
    ∃ (Y : ι → ℝ≥0 → Ω → ℝ) (hY : ∀ i, IsContinuousLocalMartingale (Y i) F P),
      (∀ i, Indistinguishable (((hY i).isSemimartingale hF).continuousQuadraticVariation hF)
        (stoppedProcess (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) τ) P) ∧
      (∀ i j, Indistinguishable
        (((hY i).isSemimartingale hF).continuousQuadraticCovariation
          ((hY j).isSemimartingale hF) hF)
        (stoppedProcess (((hX i).isSemimartingale hF).continuousQuadraticCovariation
          ((hX j).isSemimartingale hF) hF) τ) P) ∧
      (∀ᵐ ω ∂P, ∀ t, R (fun i ↦ Y i t ω)) ∧
      (∀ ω, 0 < τ ω → ∀ t i, Y i t ω = stoppedProcess (X i) τ t ω) ∧
      (∀ ω, τ ω = 0 → ∀ t i, Y i t ω = c i) := by
  let C := fun i ↦ {ω | ¬ 0 < τ ω}.indicator (fun ω ↦ c i - X i 0 ω)
  have hmask : MeasurableSet[F 0] {ω | ¬ 0 < τ ω} := (hτ.measurableSet_gt 0).compl
  have hC : ∀ i, IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ C i) F P := fun i ↦
    isContinuousLocalMartingale_const_initial (P := P)
      ((measurable_const.sub ((hX i).1.1 0)).indicator hmask)
  have hvC : ∀ i, HasFiniteVariationPaths (fun _ : ℝ≥0 ↦ C i) P := fun _ ↦
    Eventually.of_forall (fun _ ↦ (monotone_const.monotoneOn univ).locallyBoundedVariationOn)
  let Y := fun i t ω ↦ stoppedProcess (X i) τ t ω + C i ω
  have hY : ∀ i, IsContinuousLocalMartingale (Y i) F P := fun i ↦
    ((hX i).stoppedProcess hF hτ).add (hC i) hF
  have he (ω : Ω) (hp : 0 < τ ω) (t : ℝ≥0) (i : ι) :
      Y i t ω = stoppedProcess (X i) τ t ω := by
    simp only [Y, C, indicator_of_notMem
      (show ω ∉ {ω | ¬ 0 < τ ω} from not_not_intro hp), add_zero]
  have hz (ω : Ω) (hzero : τ ω = 0) (t : ℝ≥0) (i : ι) : Y i t ω = c i := by
    have hp : ¬ 0 < τ ω := by rw [hzero]; exact lt_irrefl _
    have hstop : stoppedProcess (X i) τ t ω = X i 0 ω := by
      simp only [MeasureTheory.stoppedProcess, hzero,
        min_eq_right (show (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) from bot_le)]
      rfl
    simp only [Y, C, indicator_of_mem (show ω ∈ {ω | ¬ 0 < τ ω} from hp), hstop]
    ring
  refine ⟨Y, hY, fun i ↦ ?_, fun i j ↦ ?_, ?_, he, hz⟩
  · have hS := ((hX i).isSemimartingale hF).stoppedProcess hF hτ
    exact (hS.continuousQuadraticVariation_add_finiteVariation
      ((hC i).isSemimartingale hF) hF (hvC i)).trans
        (((hX i).isSemimartingale hF).continuousQuadraticVariation_stoppedProcess hF hτ)
  · have hS := ((hX i).isSemimartingale hF).stoppedProcess hF hτ
    exact (hS.continuousQuadraticCovariation_add_finiteVariation_both
        (((hX j).isSemimartingale hF).stoppedProcess hF hτ)
        ((hC i).isSemimartingale hF) ((hC j).isSemimartingale hF) hF (hvC i) (hvC j)).trans
        (((hX i).isSemimartingale hF).continuousQuadraticCovariation_stoppedProcess_both
          ((hX j).isSemimartingale hF) hF hτ)
  · filter_upwards [hstay] with ω hω t
    by_cases hp : 0 < τ ω
    · simpa only [he ω hp] using hω hp t
    · have hzero : τ ω = 0 := le_antisymm (le_of_not_gt hp) bot_le
      simpa only [hz ω hzero] using hc

end ProbabilityTheory

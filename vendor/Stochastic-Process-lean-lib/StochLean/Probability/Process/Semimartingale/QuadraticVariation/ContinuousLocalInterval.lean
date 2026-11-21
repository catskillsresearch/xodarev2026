/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.StoppedDifference
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousLocalConstancy
public import StochLean.Probability.Process.LocalMartingale.FiniteVariationInterval
public import StochLean.Probability.Process.Path.StoppingConstancy

/-! # Protter II.27, Corollary 1: constancy on a closed stopping interval

The same raw bracket controls the ordered stopped difference. Stopping times
may be zero or infinite and need only be ordered almost surely. Interval
statements refer to finite points of the closed stochastic interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}
  {σ τ : Ω → WithTop ℝ≥0}

theorem IsContinuousLocalMartingale.stoppedProcess_eq_of_quadraticVariation_stopped_eq
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω)
    (hQ : Indistinguishable
      (MeasureTheory.stoppedProcess ((hX.isSemimartingale hF).quadraticVariation hF) τ)
      (MeasureTheory.stoppedProcess ((hX.isSemimartingale hF).quadraticVariation hF) σ) P) :
    Indistinguishable (MeasureTheory.stoppedProcess X τ)
      (MeasureTheory.stoppedProcess X σ) P := by
  have hM : IsContinuousLocalMartingale
      (MeasureTheory.stoppedProcess X τ - MeasureTheory.stoppedProcess X σ) F P := by
    refine ⟨(hX.1.stoppedProcess hF hτ).sub (hX.1.stoppedProcess hF hσ) hF, ?_⟩
    filter_upwards [hX.2.stoppedProcess τ, hX.2.stoppedProcess σ] with ω ht hs
    exact ht.sub hs
  have hzero : Indistinguishable ((hM.isSemimartingale hF).quadraticVariation hF) 0 P := by
    filter_upwards [(hX.isSemimartingale hF).quadraticVariation_stopped_difference
      hF hσ hτ hle, hQ] with ω hq he t
    rw [hq t]
    exact sub_eq_zero.mpr (he t)
  filter_upwards [hM.indistinguishable_zero_of_quadraticVariation_zero hF hzero] with ω hω t
  exact sub_eq_zero.mp (hω t)

theorem IsContinuousLocalMartingale.quadraticVariation_stopped_eq_iff
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    Indistinguishable
        (MeasureTheory.stoppedProcess ((hX.isSemimartingale hF).quadraticVariation hF) τ)
        (MeasureTheory.stoppedProcess ((hX.isSemimartingale hF).quadraticVariation hF) σ) P ↔
      Indistinguishable (MeasureTheory.stoppedProcess X τ)
        (MeasureTheory.stoppedProcess X σ) P := by
  refine ⟨hX.stoppedProcess_eq_of_quadraticVariation_stopped_eq hF hσ hτ hle, ?_⟩
  intro he
  let hSM := hX.isSemimartingale hF
  exact (hSM.quadraticVariation_stoppedProcess hF hτ).symm.trans
    (((hSM.stoppedProcess hF hτ).quadraticVariation_congr
      (hSM.stoppedProcess hF hσ) hF he).trans
        (hSM.quadraticVariation_stoppedProcess hF hσ))

theorem IsContinuousLocalMartingale.constantOn_stopping_interval_iff_quadraticVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
      σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω → X s ω = X t ω) ↔
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
      σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω →
      (hX.isSemimartingale hF).quadraticVariation hF s ω =
        (hX.isSemimartingale hF).quadraticVariation hF t ω) := by
  have hconvert (Y : ℝ≥0 → Ω → ℝ) :
      Indistinguishable (MeasureTheory.stoppedProcess Y τ)
          (MeasureTheory.stoppedProcess Y σ) P ↔
        (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
          σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω → Y s ω = Y t ω) := by
    constructor
    · intro he
      exact he.mono fun _ hω ↦ eq_on_stopping_interval_of_stoppedProcess_eq hω
    · intro he
      filter_upwards [hle, he] with ω ho heω
      exact stoppedProcess_eq_of_eq_on_stopping_interval ho heω
  rw [← hconvert X, ← hconvert ((hX.isSemimartingale hF).quadraticVariation hF)]
  exact (hX.quadraticVariation_stopped_eq_iff hF hσ hτ hle).symm

theorem IsContinuousLocalMartingale.constantOn_stopping_interval_of_finiteVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω)
    (hv : ∀ᵐ ω ∂P, σ ω < τ ω → ∀ b : ℝ≥0, (b : WithTop ℝ≥0) ≤ τ ω →
      BoundedVariationOn (X · ω) (Ioo (σ ω).untopA b)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
      σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω → X s ω = X t ω :=
  (hX.stoppedProcess_eq_of_finiteVariation_interval hF hσ hτ hle hv).mono
    fun _ hω ↦ eq_on_stopping_interval_of_stoppedProcess_eq hω

end ProbabilityTheory

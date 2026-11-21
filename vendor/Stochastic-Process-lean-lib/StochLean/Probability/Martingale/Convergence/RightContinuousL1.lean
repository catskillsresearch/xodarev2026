/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.AntitoneSampling
public import StochLean.Probability.Process.Path.RightContinuous
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Order.IsLUB

/-! # Right continuity of one-sided martingale expectations

Decreasing deterministic samples are uniformly integrable, so common-event
right continuity gives their actual L1 convergence. The monotone expectation
function has a right limit, and this sampling identifies it with the expected
value at the endpoint. No uniform-in-time L1 bound or L2 hypothesis is assumed.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.tendsto_eLpNorm_of_antitone_right_sampling
    (hX : Supermartingale X F P) (hr : HasRightContinuousPaths X P)
    {a : ℕ → ℝ≥0} (ha : Antitone a) {t : ℝ≥0}
    (hl : Tendsto a atTop (𝓝[≥] t)) :
    Tendsto (fun n ↦ eLpNorm (X (a n) - X t) 1 P) atTop (𝓝 0) := by
  have hu := hX.uniformIntegrable_antitone_reindex ha
  have hx : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (a n) ω) atTop (𝓝 (X t ω)) :=
    hr.mono fun _ hω ↦ (hω t).tendsto.comp hl
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (memLp_one_iff_integrable.mpr (hX.integrable t)) hu.2.1 hx

theorem Submartingale.tendsto_eLpNorm_of_antitone_right_sampling
    (hX : Submartingale X F P) (hr : HasRightContinuousPaths X P)
    {a : ℕ → ℝ≥0} (ha : Antitone a) {t : ℝ≥0}
    (hl : Tendsto a atTop (𝓝[≥] t)) :
    Tendsto (fun n ↦ eLpNorm (X (a n) - X t) 1 P) atTop (𝓝 0) := by
  have hu := hX.uniformIntegrable_antitone_reindex ha
  have hx : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (a n) ω) atTop (𝓝 (X t ω)) :=
    hr.mono fun _ hω ↦ (hω t).tendsto.comp hl
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (memLp_one_iff_integrable.mpr (hX.integrable t)) hu.2.1 hx

theorem Supermartingale.isRightContinuousPath_integral
    (hX : Supermartingale X F P) (hr : HasRightContinuousPaths X P) :
    IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  have hm : Antitone (fun t ↦ ∫ ω, X t ω ∂P) := by
    intro s t hst
    simpa only [setIntegral_univ] using hX.setIntegral_le hst (@MeasurableSet.univ Ω (F s))
  intro t
  apply continuousWithinAt_Ioi_iff_Ici.mp
  apply hm.continuousWithinAt_Ioi_iff_rightLim_eq.mpr
  obtain ⟨a, ha, hat, hal⟩ := exists_seq_strictAnti_tendsto' (lt_add_one t)
  have hl : Tendsto a atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hal, Eventually.of_forall fun n ↦ (hat n).1⟩
  have hL1 := hX.tendsto_eLpNorm_of_antitone_right_sampling hr ha.antitone
    (hl.mono_right (nhdsWithin_mono _ (Set.Ioi_subset_Ici_self)))
  have hI := tendsto_integral_of_L1' (X t) (hX.integrable t).aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hX.integrable (a n)) hL1
  exact tendsto_nhds_unique ((hm.tendsto_rightLim t).comp hl) hI

theorem Submartingale.isRightContinuousPath_integral
    (hX : Submartingale X F P) (hr : HasRightContinuousPaths X P) :
    IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  have hrn : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have hn := hX.neg.isRightContinuousPath_integral hrn
  have he : (fun t ↦ ∫ ω, X t ω ∂P) = -(fun t ↦ ∫ ω, (-X) t ω ∂P) := by
    funext t
    simp only [Pi.neg_apply, integral_neg, neg_neg]
  rw [he]
  intro t
  exact (hn t).neg

end MeasureTheory

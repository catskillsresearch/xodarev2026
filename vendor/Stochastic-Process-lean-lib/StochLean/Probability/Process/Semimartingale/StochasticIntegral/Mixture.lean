/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.AbsoluteContinuity
public import StochLean.Probability.Process.Semimartingale.Mixture
public import StochLean.Probability.Process.Filtration.MeasureChange
public import Mathlib.Tactic.NormNum

/-! # Protter II.15: mixture invariance and a common integral version

The actual integral under the mixture measure is a version of every
positive-weight component integral. Mixture probability mass, usual conditions,
the semimartingale property and caglad integrand paths are all derived. The
two-probability corollary constructs a single adapted, everywhere cadlag process.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X H : ℝ≥0 → Ω → ℝ}

theorem stochasticIntegral_probability_mixture (P : ℕ → Measure Ω)
    [∀ k, IsProbabilityMeasure (P k)] (c : ℕ → ℝ≥0)
    (hc : (∑' k, (c k : ℝ≥0∞)) = 1)
    (hX : ∀ k, IsSemimartingale X F (P k)) (hF : ∀ k, F.IsUsual (P k))
    (ha : Adapted F H) (hr : ∀ k, HasCagladPaths H (P k)) :
    let := Measure.isProbabilityMeasure_probability_mixture P c hc
    let hXR := isSemimartingale_probability_mixture P c hc hX
    let hFR := Filtration.IsUsual.probability_mixture P c hc hF
    let hrR : HasCagladPaths H (Measure.sum (fun k ↦ (c k : ℝ≥0∞) • P k)) :=
      Measure.ae_sum_iff.mpr (fun k ↦ Measure.ae_smul_measure (hr k) _)
    ∀ k, c k ≠ 0 → Indistinguishable (hXR.stochasticIntegral hFR ha hrR)
      ((hX k).stochasticIntegral (hF k) ha (hr k)) (P k) := by
  let := Measure.isProbabilityMeasure_probability_mixture P c hc
  dsimp only
  intro k hk
  exact ((isSemimartingale_probability_mixture P c hc hX).stochasticIntegral_absolutelyContinuous
    (Measure.absolutelyContinuous_probability_mixture P c hk)
    (Filtration.IsUsual.probability_mixture P c hc hF) (hF k) ha
    (Measure.ae_sum_iff.mpr (fun j ↦ Measure.ae_smul_measure (hr j) _))).symm

theorem exists_common_stochasticIntegral_probability_mixture (P : ℕ → Measure Ω)
    [∀ k, IsProbabilityMeasure (P k)] (c : ℕ → ℝ≥0)
    (hc : (∑' k, (c k : ℝ≥0∞)) = 1)
    (hX : ∀ k, IsSemimartingale X F (P k)) (hF : ∀ k, F.IsUsual (P k))
    (ha : Adapted F H) (hr : ∀ k, HasCagladPaths H (P k)) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      ∀ k, c k ≠ 0 → Indistinguishable J ((hX k).stochasticIntegral (hF k) ha (hr k)) (P k) := by
  let := Measure.isProbabilityMeasure_probability_mixture P c hc
  let hXR := isSemimartingale_probability_mixture P c hc hX
  let hFR := Filtration.IsUsual.probability_mixture P c hc hF
  have hrR : HasCagladPaths H (Measure.sum (fun k ↦ (c k : ℝ≥0∞) • P k)) :=
    Measure.ae_sum_iff.mpr (fun k ↦ Measure.ae_smul_measure (hr k) _)
  exact ⟨hXR.stochasticIntegral hFR ha hrR, hXR.adapted_stochasticIntegral hFR ha hrR,
    hXR.isCadlagPath_stochasticIntegral hFR ha hrR,
    stochasticIntegral_probability_mixture P c hc hX hF ha hr⟩

/-- The corollary to II.15, using the two weights `1/2, 1/2` and zero thereafter. -/
theorem exists_common_stochasticIntegral {P Q : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hXP : IsSemimartingale X F P) (hXQ : IsSemimartingale X F Q)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q)
    (ha : Adapted F H) (hrP : HasCagladPaths H P) (hrQ : HasCagladPaths H Q) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      Indistinguishable J (hXP.stochasticIntegral hFP ha hrP) P ∧
      Indistinguishable J (hXQ.stochasticIntegral hFQ ha hrQ) Q := by
  let R : ℕ → Measure Ω := fun n ↦ if n = 0 then P else Q
  let c : ℕ → ℝ≥0 := fun n ↦ (if n = 0 then 1 / 2 else 0) + (if n = 1 then 1 / 2 else 0)
  have hc : (∑' n, (c n : ℝ≥0∞)) = 1 := by
    have heq (n : ℕ) : (c n : ℝ≥0∞) =
        (if n = 0 then 1 / 2 else 0) + (if n = 1 then 1 / 2 else 0) := by
      by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;> norm_num [c, h0, h1]
    simp_rw [heq]
    rw [ENNReal.tsum_add]
    simpa using ENNReal.inv_two_add_inv_two
  have (n : ℕ) : IsProbabilityMeasure (R n) := by
    dsimp [R]
    split <;> infer_instance
  have hXR (n : ℕ) : IsSemimartingale X F (R n) := by
    dsimp [R]
    split <;> assumption
  have hFR (n : ℕ) : F.IsUsual (R n) := by
    dsimp [R]
    split <;> assumption
  have hrR (n : ℕ) : HasCagladPaths H (R n) := by
    dsimp [R]
    split <;> assumption
  obtain ⟨J, haJ, hrJ, hJ⟩ :=
    exists_common_stochasticIntegral_probability_mixture R c hc hXR hFR ha hrR
  exact ⟨J, haJ, hrJ, hJ 0 (by norm_num [c]), hJ 1 (by norm_num [c])⟩

end ProbabilityTheory

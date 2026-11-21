/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.LinearMap

/-! # Source integral continuity away from zero

Actual simple-process subtraction and elementary linearity extend the canonical
zero-continuity criterion to every source simple integrand. This result still uses
uniform convergence in both time and sample; it does not assert UCP continuity.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- The source neighborhood bound is uniform in both simple integrands. -/
theorem IsGoodIntegrator.elementaryIntegral_uniform_continuity
    (hX : IsGoodIntegrator X F P) (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H K : ℝ≥0 → Ω → ℝ,
      ∀ hH : IsSimplePredictable H F, ∀ hK : IsSimplePredictable K F,
      (∀ t ω, ‖H t ω - K t ω‖ ≤ δ) →
      P {ω | ε ≤ ‖hH.elementaryIntegral X ω - hK.elementaryIntegral X ω‖} ≤ η := by
  obtain ⟨δ, hδ, hb⟩ := (isGoodIntegrator_iff_continuousAtZero.mp hX) ε hε η hη
  refine ⟨δ, hδ, fun H K hH hK hbound ↦ ?_⟩
  simpa only [hH.elementaryIntegral_sub hK X] using
    hb (H - K) (hH.sub hK) hbound

/-- Uniformly Cauchy source inputs give a Cauchy family in probability. This is
an estimate, not a selected limit or a claim that the general integral already exists. -/
theorem IsGoodIntegrator.elementaryIntegral_cauchyInMeasure
    (hX : IsGoodIntegrator X F P) {H : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : ∀ n, IsSimplePredictable (H n) F)
    (hc : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      ∀ t ω, ‖H m t ω - H n t ω‖ ≤ δ) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ,
      ∀ m n, N ≤ m → N ≤ n →
      P {ω | ε ≤ ‖(hH m).elementaryIntegral X ω - (hH n).elementaryIntegral X ω‖} ≤ η := by
  intro ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := hX.elementaryIntegral_uniform_continuity ε hε η hη
  obtain ⟨N, hN⟩ := hc δ hδ
  exact ⟨N, fun m n hm hn ↦ hb (H m) (H n) (hH m) (hH n) (hN m n hm hn)⟩

theorem IsGoodIntegrator.tendstoInMeasure_elementaryIntegral
    (hX : IsGoodIntegrator X F P) {H : ℕ → ℝ≥0 → Ω → ℝ} {K : ℝ≥0 → Ω → ℝ}
    (hH : ∀ n, IsSimplePredictable (H n) F) (hK : IsSimplePredictable K F)
    (hHK : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2)
      (fun z ↦ K z.1 z.2) atTop) :
    TendstoInMeasure P (fun n ↦ (hH n).elementaryIntegral X) atTop
      (hK.elementaryIntegral X) := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := hX.elementaryIntegral_uniform_continuity ε hε η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hHK δ hδ)
  refine ⟨N, fun n hn ↦ hb (H n) K (hH n) hK ?_⟩
  intro t ω
  simpa only [dist_eq_norm_sub, norm_sub_rev] using (hN n hn (t, ω)).le

end ProbabilityTheory

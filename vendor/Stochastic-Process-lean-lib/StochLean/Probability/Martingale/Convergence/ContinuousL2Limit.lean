/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobTailL2

/-! # Whole-half-line almost-sure and L2 martingale convergence

The tail envelopes tend to zero in L2. A subsequence tends to zero almost
surely by the measure-convergence/Borel-Cantelli theorem. Each envelope controls
every later time on one event. Combined with the actual integer-time limit,
this proves full-half-line almost-sure convergence, not just a subsequence.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem ae_tendsto_of_integer_L2_closing
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hZ : MemLp Z 2 P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hna : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (Z ω)))
    (hn : Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 2 P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)) := by
  choose g hgm hgn hgl hgb hgi using
    (fun n : ℕ ↦ hX.exists_memLp_two_tailEnvelope hc hZ hclose (n : ℝ≥0))
  have hL (t : ℝ≥0) : MemLp (X t) 2 P :=
    (hZ.condExp (by norm_num)).ae_eq (hclose t).symm
  have hgbound (n : ℕ) : eLpNorm (g n) 2 P ≤ 2 * eLpNorm (X (n : ℝ≥0) - Z) 2 P := by
    simpa using eLpNorm_two_le_mul_of_integral_sq_le (hgl n)
      ((hL (n : ℝ≥0)).sub hZ) 2 (by convert! hgi n using 1; norm_num)
  have hmul : Tendsto (fun n : ℕ ↦ 2 * eLpNorm (X (n : ℝ≥0) - Z) 2 P) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hn
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  have hgp : Tendsto (fun n ↦ eLpNorm (g n) 2 P) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hmul ε hε] with n hnε
    exact (hgbound n).trans hnε
  have hmeasure : TendstoInMeasure P g atTop (0 : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun n ↦ (hgl n).aestronglyMeasurable) aestronglyMeasurable_zero
      (by simpa only [sub_zero] using hgp)
  obtain ⟨k, hk, hg0⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hg0, hna, eventually_countable_forall.mpr hgb] with ω hgω hnω hbω
  have hdiff : Tendsto (fun j ↦ X (k j : ℝ≥0) ω - Z ω) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using
      (hnω.comp hk.tendsto_atTop).sub (tendsto_const_nhds (x := Z ω))
  have herr : Tendsto (fun j ↦ g (k j) ω + ‖X (k j : ℝ≥0) ω - Z ω‖) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, norm_zero, add_zero] using hgω.add hdiff.norm
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (herr.eventually (eventually_lt_nhds hε)).exists
  refine ⟨(k j : ℝ≥0), fun t ht ↦ ?_⟩
  calc
    dist (X t ω) (Z ω) = ‖X t ω - Z ω‖ := dist_eq_norm _ _
    _ ≤ ‖X t ω - X (k j : ℝ≥0) ω‖ + ‖X (k j : ℝ≥0) ω - Z ω‖ := by
      simpa only [dist_eq_norm] using dist_triangle (X t ω) (X (k j : ℝ≥0) ω) (Z ω)
    _ ≤ g (k j) ω + ‖X (k j : ℝ≥0) ω - Z ω‖ := add_le_add (hbω (k j) t ht) le_rfl
    _ < ε := hj

theorem exists_memLp_two_limit_of_bounded_second_moments
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P)
    (hL : ∀ t, MemLp (X t) 2 P) {C : ℝ} (hb : ∀ t, (∫ ω, X t ω ^ 2 ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 2 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧ (∫ ω, Z ω ^ 2 ∂P) ≤ C := by
  obtain ⟨Z, hZ, hna, hn, hclose, _, hE⟩ :=
    hX.exists_memLp_two_closing_and_second_moment_limit hc hL hb
  exact ⟨Z, hZ, hX.ae_tendsto_of_integer_L2_closing hc hZ hclose hna hn,
    hX.tendsto_eLpNorm_two_of_integer_closing (hZ.integrable (by norm_num)) hclose hn, hclose, hE⟩

end MeasureTheory.Martingale

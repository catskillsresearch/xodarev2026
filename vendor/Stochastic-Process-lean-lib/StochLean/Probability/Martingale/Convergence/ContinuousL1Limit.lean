/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousL1Closure
public import StochLean.Probability.Martingale.Inequalities.DoobWeakTailL1

/-! # Whole-half-line convergence of uniformly integrable martingales

Weak L1 tail bounds force the event of arbitrarily late deviations at each
fixed positive scale to have measure zero. A countable collection of scales
gives the actual all-real-time pathwise limit. This is not an inference from
integer-time convergence alone and requires no second moment or L1 supremum.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem ae_eventually_norm_sub_closing_le_two
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hn : Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 1 P) atTop (𝓝 0))
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ∀ t : ℝ≥0, (n : ℝ≥0) ≤ t →
      ‖X t ω - Z ω‖ ≤ 2 * (ε : ℝ) := by
  classical
  let B := {ω | ∀ n : ℕ, ∃ t : ℝ≥0,
    (n : ℝ≥0) ≤ t ∧ 2 * (ε : ℝ) < ‖X t ω - Z ω‖}
  have hb (n : ℕ) : (ε : ℝ≥0∞) * P B ≤ 2 * eLpNorm (X (n : ℝ≥0) - Z) 1 P := by
    apply le_trans _ (hX.measure_exists_tail_closing_error_gt_le hc hZ hclose (n : ℝ≥0) ε)
    exact mul_le_mul le_rfl (measure_mono fun ω hω ↦ hω n) (by positivity) (by positivity)
  have hmul : Tendsto (fun n : ℕ ↦ 2 * eLpNorm (X (n : ℝ≥0) - Z) 1 P) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hn
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  have hz : (ε : ℝ≥0∞) * P B = 0 := le_antisymm (ge_of_tendsto' hmul hb) bot_le
  have he : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have hB : P B = 0 := (mul_eq_zero.mp hz).resolve_left he
  have ha : ∀ᵐ ω ∂P, ω ∉ B := compl_mem_ae_iff.mpr hB
  filter_upwards [ha] with ω hω
  change ¬ ∀ n : ℕ, ∃ t : ℝ≥0, (n : ℝ≥0) ≤ t ∧
    2 * (ε : ℝ) < ‖X t ω - Z ω‖ at hω
  push Not at hω
  exact hω

theorem ae_tendsto_of_integer_L1_closing
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hn : Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 1 P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)) := by
  let ε (k : ℕ) : ℝ≥0 := 1 / ((k : ℝ≥0) + 1) / 2
  have he (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hb (k : ℕ) := hX.ae_eventually_norm_sub_closing_le_two hc hZ hclose hn (he k)
  filter_upwards [eventually_countable_forall.mpr hb] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨n, hn⟩ := hω k
  refine ⟨(n : ℝ≥0), fun t ht ↦ ?_⟩
  have heq : 2 * (ε k : ℝ) = 1 / (k + 1 : ℝ) := by
    simp only [ε, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one, NNReal.coe_ofNat]
    ring
  rw [dist_eq_norm]
  exact (hn t ht).trans_lt (heq.trans_lt hk)

/-- Protter I.12: a right-continuous UI martingale has an actual integrable
terminal limit over the entire half-line, and that limit closes the process.
The L1 convergence is also over all nonnegative real times. -/
theorem exists_integrable_limit_of_uniformIntegrable
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P)
    (hu : UniformIntegrable X 1 P) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 1 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) := by
  obtain ⟨Z, hZ, _, hn, hclose⟩ := hX.exists_integrable_integer_limit_closing hu
  exact ⟨Z, hZ, hX.ae_tendsto_of_integer_L1_closing hc hZ hclose hn,
    hX.tendsto_eLpNorm_of_integer_closing le_rfl hZ hclose hn, hclose⟩

/-- The UI/actual-limit-closing equivalence, without any square-integrability
hypothesis. The terminal variable is constructed, not supplied as a premise. -/
theorem uniformIntegrable_iff_exists_integrable_limit_closing
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) :
    UniformIntegrable X 1 P ↔ ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 1 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) :=
  ⟨hX.exists_integrable_limit_of_uniformIntegrable hc,
    fun ⟨_, hZ, _, _, hclose⟩ ↦ uniformIntegrable_of_integrable_closing hZ hclose⟩

end MeasureTheory.Martingale

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobContinuousL2

/-! # A global L2 envelope from uniformly bounded second moments

The existing dense running suprema on integer horizons increase almost surely
by right continuity. Monotone convergence and finite-horizon Doob estimates
give a finite global supremum before any conversion to real values. The
resulting envelope controls all nonnegative real times on one event.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E} {C : ℝ}

theorem Martingale.lintegral_iSup_denseRunningSupremum_norm_sq_le
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P)
    (hL : ∀ t, MemLp (X t) 2 P) (hb : ∀ t, (∫ ω, ‖X t ω‖ ^ 2 ∂P) ≤ C) :
    (∫⁻ ω, ⨆ n : ℕ, denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) (n : ℝ≥0) ω ∂P) ≤
      4 * ENNReal.ofReal C := by
  have hm (n : ℕ) : Measurable
      (denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) (n : ℝ≥0)) :=
    measurable_denseRunningSupremum (fun t ↦
      (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2) _
  rw [lintegral_iSup' (fun n ↦ (hm n).aemeasurable) (by
    filter_upwards [hc] with ω hω i j hij
    apply iSup_le
    intro k
    exact ofReal_le_denseRunningSupremum_of_rightContinuous
      ((min_le_left _ _).trans (by exact_mod_cast hij)) (fun t ↦ (hω t).norm.pow 2))]
  apply iSup_le
  intro n
  exact (hX.lintegral_denseRunningSupremum_norm_sq_le (hL (n : ℝ≥0))).trans
    (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (hb _)) (by positivity) (by positivity))

/-- Uniform L2 boundedness of a true right-continuous martingale supplies an
actual L2 envelope on the whole half-line, with Doob's factor four. -/
theorem Martingale.exists_memLp_two_globalEnvelope
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P)
    (hL : ∀ t, MemLp (X t) 2 P) (hb : ∀ t, (∫ ω, ‖X t ω‖ ^ 2 ∂P) ≤ C) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ g ω) ∧ (∫ ω, g ω ^ 2 ∂P) ≤ 4 * C := by
  let A (ω : Ω) : ℝ≥0∞ :=
    ⨆ n : ℕ, denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) (n : ℝ≥0) ω
  have hAm : Measurable A := Measurable.iSup fun n ↦
    measurable_denseRunningSupremum (fun t ↦
      (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2) _
  have hAi : (∫⁻ ω, A ω ∂P) < ∞ :=
    (hX.lintegral_iSup_denseRunningSupremum_norm_sq_le hc hL hb).trans_lt
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  have hAf : ∀ᵐ ω ∂P, A ω < ∞ := ae_lt_top hAm hAi.ne
  have hAr : Integrable (fun ω ↦ (A ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hAm.aemeasurable hAi.ne
  let g (ω : Ω) := Real.sqrt (A ω).toReal
  have hglp : MemLp g 2 P := by
    apply (memLp_two_iff_integrable_sq hAm.ennreal_toReal.sqrt.aestronglyMeasurable).mpr
    simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using hAr
  refine ⟨g, hAm.ennreal_toReal.sqrt, fun ω ↦ Real.sqrt_nonneg _, hglp, ?_, ?_⟩
  · filter_upwards [hAf, hc] with ω hf hω t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    apply Real.le_sqrt_of_sq_le
    apply (ENNReal.ofReal_le_iff_le_toReal hf.ne).mp
    exact (ofReal_le_denseRunningSupremum_of_rightContinuous hn
      (fun s ↦ (hω s).norm.pow 2)).trans
        (le_iSup (fun n : ℕ ↦ denseRunningSupremum
          (fun s ω ↦ ‖X s ω‖ ^ 2) (n : ℝ≥0) ω) n)
  · have hC : 0 ≤ C := (integral_nonneg fun ω ↦ sq_nonneg ‖X 0 ω‖).trans (hb 0)
    simp only [g, Real.sq_sqrt ENNReal.toReal_nonneg]
    rw [integral_toReal hAm.aemeasurable hAf]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_lt_top (by norm_num : (4 : ℝ≥0∞) < ∞) ENNReal.ofReal_lt_top).ne
      (hX.lintegral_iSup_denseRunningSupremum_norm_sq_le hc hL hb)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal hC] using h

end MeasureTheory

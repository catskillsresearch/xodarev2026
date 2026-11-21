/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.Regularization
public import StochLean.Probability.Martingale.Inequalities.DoobContinuousL2
public import StochLean.Probability.Process.Path.RightContinuousOrder
public import StochLean.Probability.Process.Path.RightContinuousSupremum
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Actual conditional martingales with maximal probability bounds

Doob regularization constructs a cadlag version of the conditional expectations
of a square-integrable input. Conditional-expectation contraction and the proved
continuous-time Doob inequality give its compact maximal probability estimate.
The maximal bound is a conclusion, not an assumed envelope. Nonnegative input
gives nonnegativity simultaneously at all times; extended running suprema are
proved finite almost surely before using their real values.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {D : Ω → ℝ}

omit [IsFiniteMeasure P] in
theorem ae_forall_nonneg_of_rightContinuous_condExp
    (hr : HasRightContinuousPaths M P) (hD : 0 ≤ᵐ[P] D)
    (he : ∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t]) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ M t ω := by
  have hz : HasRightContinuousPaths (fun _ : ℝ≥0 ↦ (0 : Ω → ℝ)) P :=
    Eventually.of_forall fun _ _ ↦ continuousWithinAt_const
  apply hz.ae_forall_le_of_forall_ae_le hr
  intro t
  exact (condExp_nonneg (m := F t) hD).trans_eq (he t).symm

private theorem Martingale.exists_memLp_two_condExp_envelope
    (hM : Martingale M F P) (hr : HasRightContinuousPaths M P) (hD : MemLp D 2 P)
    (he : ∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t]) (T : ℝ≥0) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T, ‖M t ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 4 * ∫ ω, D ω ^ 2 ∂P := by
  have hMT : MemLp (M T) 2 P := (hD.condExp (by norm_num)).ae_eq (he T).symm
  have hnorm : eLpNorm (M T) 2 P ≤ eLpNorm D 2 P := by
    rw [eLpNorm_congr_ae (he T)]
    exact eLpNorm_condExp_le_eLpNorm D (by norm_num)
  have hsq := integral_sq_le_of_eLpNorm_two_le hMT hD hnorm
  obtain ⟨g, hgm, hgn, hgl, hgb, hgi⟩ := hM.exists_memLp_two_maximalEnvelope hr hMT
  refine ⟨g, hgm, hgn, hgl, hgb, ?_⟩
  have hle : 4 * (∫ ω, (M T ω) ^ 2 ∂P) ≤ 4 * ∫ ω, D ω ^ 2 ∂P :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hgi' : (∫ ω, g ω ^ 2 ∂P) ≤ 4 * ∫ ω, (M T ω) ^ 2 ∂P := by
    simpa only [Real.norm_eq_abs, sq_abs] using hgi
  exact hgi'.trans hle

theorem Martingale.ae_denseRunningSupremum_condExp_ne_top
    (hM : Martingale M F P) (hr : HasRightContinuousPaths M P) (hD : MemLp D 2 P)
    (he : ∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t]) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, denseRunningSupremum M T ω ≠ ∞ := by
  obtain ⟨g, _, _, _, hgb, _⟩ := hM.exists_memLp_two_condExp_envelope hr hD he T
  filter_upwards [hgb] with ω hω
  apply denseRunningSupremum_ne_top_of_le (K := g ω)
  intro t ht
  exact (le_abs_self _).trans (hω t ht)

theorem Martingale.measureReal_denseRunningSupremum_condExp_gt_le
    (hM : Martingale M F P) (hr : HasRightContinuousPaths M P) (hD : MemLp D 2 P)
    (he : ∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t]) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ENNReal.ofReal a < denseRunningSupremum M T ω} ≤
      (4 * ∫ ω, D ω ^ 2 ∂P) / a ^ 2 := by
  obtain ⟨g, _, _, hgl, hgb, hgi⟩ := hM.exists_memLp_two_condExp_envelope hr hD he T
  have hmeasure : P {ω | ENNReal.ofReal a < denseRunningSupremum M T ω} ≤
      P {ω | a ≤ ‖g ω‖} := by
    apply measure_mono_ae
    filter_upwards [hgb] with ω hω hA
    have hsup : denseRunningSupremum M T ω ≤ ENNReal.ofReal (g ω) :=
      denseRunningSupremum_le_of_le (fun t ht ↦ (le_abs_self _).trans (hω t ht))
    have hag : a < g ω := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mp (hA.trans_le hsup)
    exact hag.le.trans (le_abs_self _)
  have hmarkov := measure_norm_ge_le_integral_sq_div hgl.integrable_sq ha
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmeasure.trans hmarkov)
  have hnonneg : 0 ≤ (∫ ω, g ω ^ 2 ∂P) / a ^ 2 :=
    div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg a)
  have hle : P.real {ω | ENNReal.ofReal a < denseRunningSupremum M T ω} ≤
      (∫ ω, g ω ^ 2 ∂P) / a ^ 2 := by
    simpa only [Measure.real, ENNReal.toReal_ofReal hnonneg] using hreal
  exact hle.trans (div_le_div_of_nonneg_right hgi (sq_nonneg a))

theorem Martingale.measureReal_toReal_denseRunningSupremum_condExp_gt_le
    (hM : Martingale M F P) (hr : HasRightContinuousPaths M P) (hD : MemLp D 2 P)
    (he : ∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t]) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | a < (denseRunningSupremum M T ω).toReal} ≤
      (4 * ∫ ω, D ω ^ 2 ∂P) / a ^ 2 := by
  have hevent : {ω | a < (denseRunningSupremum M T ω).toReal} =ᵐ[P]
      {ω | ENNReal.ofReal a < denseRunningSupremum M T ω} := by
    filter_upwards [hM.ae_denseRunningSupremum_condExp_ne_top hr hD he T] with ω hfin
    exact propext (ENNReal.ofReal_lt_iff_lt_toReal ha.le hfin).symm
  have hmeasure := measure_congr hevent
  change (P {ω | a < (denseRunningSupremum M T ω).toReal}).toReal ≤ _
  rw [hmeasure]
  exact hM.measureReal_denseRunningSupremum_condExp_gt_le hr hD he T ha

theorem exists_cadlag_conditionalEnvelope (hF : F.IsUsual P)
    (hD : MemLp D 2 P) (hDnonneg : 0 ≤ᵐ[P] D) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M F P ∧ HasCadlagPaths M P ∧
      (∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t]) ∧ (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ M t ω) ∧
      ∀ T : ℝ≥0, (∀ᵐ ω ∂P, denseRunningSupremum M T ω ≠ ∞) ∧
        ∀ a : ℝ, 0 < a →
          P.real {ω | ENNReal.ofReal a < denseRunningSupremum M T ω} ≤
            (4 * ∫ ω, D ω ^ 2 ∂P) / a ^ 2 ∧
          P.real {ω | a < (denseRunningSupremum M T ω).toReal} ≤
            (4 * ∫ ω, D ω ^ 2 ∂P) / a ^ 2 := by
  obtain ⟨M, hM, hcM, heM, _⟩ := (martingale_condExp D F P).exists_cadlag_modification hF
  have he : ∀ t : ℝ≥0, M t =ᵐ[P] P[D | F t] := fun t ↦ (heM t).symm
  refine ⟨M, hM, hcM, he,
    ae_forall_nonneg_of_rightContinuous_condExp hcM.hasRightContinuousPaths hDnonneg he, fun T ↦ ?_⟩
  refine ⟨hM.ae_denseRunningSupremum_condExp_ne_top hcM.hasRightContinuousPaths hD he T,
    fun a ha ↦ ?_⟩
  exact ⟨hM.measureReal_denseRunningSupremum_condExp_gt_le hcM.hasRightContinuousPaths hD he T ha,
    hM.measureReal_toReal_denseRunningSupremum_condExp_gt_le hcM.hasRightContinuousPaths hD he T ha⟩

end MeasureTheory

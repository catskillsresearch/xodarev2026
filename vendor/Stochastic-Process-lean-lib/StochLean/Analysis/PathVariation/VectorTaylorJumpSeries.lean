/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VectorCadlagBounds
public import StochLean.ForMathlib.Analysis.FrechetTaylorCoefficient

/-! # Absolute vector Taylor jump series from square-summable jump norms

Local compact bounds control the actual first- and second-order corrections.
The original path is not assumed to have finite variation.
-/

@[expose] public section

open Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {x : ℝ≥0 → E} {T : ℝ≥0}

theorem summable_abs_vector_pair_weighted_sq_jumps (hx : IsCadlagPath x)
    (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2)) :
    Summable (fun s : Ioc 0 T ↦ |Φ (leftLim x s) (x s) * ‖x s - leftLim x s‖ ^ 2|) := by
  obtain ⟨C, _, hC⟩ := exists_compact_vector_pair_bound_of_cadlag hx T hΦ
  apply (hs.mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖x s - leftLim x s‖)]
  exact mul_le_mul_of_nonneg_right (hC s ⟨s.2.1.le, s.2.2⟩) (sq_nonneg _)

theorem summable_abs_cadlag_bilinear_jumps [NormedSpace ℝ E] (hx : IsCadlagPath x)
    (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {L : E → E →L[ℝ] E →L[ℝ] ℝ} (hL : Continuous L) :
    Summable (fun s : Ioc 0 T ↦
      |L (leftLim x s) (x s - leftLim x s) (x s - leftLim x s)|) := by
  have hn : Continuous (fun a : E ↦ ‖L a‖) := by
    simpa only [Function.comp_def] using
      (continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).comp hL
  have hp : Continuous (fun p : E × E ↦ ‖L p.1‖) := by
    simpa only [Function.comp_def] using hn.comp continuous_fst
  obtain ⟨C, _, hC⟩ := exists_compact_vector_pair_bound_of_cadlag hx T
    (Φ := fun a _ ↦ ‖L a‖) hp
  apply (hs.mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs]
  have hc : ‖L (leftLim x s)‖ ≤ C := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (L (leftLim x s)))] using
      hC s ⟨s.2.1.le, s.2.2⟩
  calc
    _ ≤ ‖L (leftLim x s) (x s - leftLim x s)‖ * ‖x s - leftLim x s‖ :=
      (L (leftLim x s) (x s - leftLim x s)).le_opNorm _
    _ ≤ (‖L (leftLim x s)‖ * ‖x s - leftLim x s‖) * ‖x s - leftLim x s‖ :=
      mul_le_mul_of_nonneg_right ((L (leftLim x s)).le_opNorm _) (norm_nonneg _)
    _ ≤ (C * ‖x s - leftLim x s‖) * ‖x s - leftLim x s‖ := by gcongr
    _ = _ := by ring

theorem summable_abs_frechet_second_order_jump_remainders [NormedSpace ℝ E]
    (hx : IsCadlagPath x) (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦ |frechetSecondOrderRemainder f (leftLim x s) (x s)|) := by
  simpa only [frechetTaylorErrorCoefficient_mul_norm_sq] using
    summable_abs_vector_pair_weighted_sq_jumps hx hs
      (continuous_frechetTaylorErrorCoefficient_of_contDiff hf)

theorem summable_abs_frechet_first_order_jump_remainders [NormedSpace ℝ E]
    (hx : IsCadlagPath x) (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦
      |f (x s) - f (leftLim x s) - fderiv ℝ f (leftLim x s) (x s - leftLim x s)|) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hR := (summable_abs_frechet_second_order_jump_remainders hx hs hf).of_abs
  have hL := (summable_abs_cadlag_bilinear_jumps hx hs
    (hd.continuous_fderiv (by decide))).of_abs
  have hsum := hR.add (hL.mul_left (1 / 2 : ℝ))
  have he : (fun s : Ioc 0 T ↦ frechetSecondOrderRemainder f (leftLim x s) (x s) +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (leftLim x s)
        (x s - leftLim x s) (x s - leftLim x s)) =
      fun s : Ioc 0 T ↦ f (x s) - f (leftLim x s) -
        fderiv ℝ f (leftLim x s) (x s - leftLim x s) := by
    funext s
    unfold frechetSecondOrderRemainder
    ring
  rw [he] at hsum
  exact hsum.abs

end StochLean

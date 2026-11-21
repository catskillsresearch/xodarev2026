/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.StrongMarkov
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Brownian martingales in the natural filtration

The underlying Brownian law and natural filtration are the existing Mathlib
owners. Coordinate measurability is explicit: the pre-Brownian law alone only
gives AE measurability. Square integrability here is at every finite time,
not a global L2 bound. The square-minus-time proof uses independent increments
and Gaussian moments, with no stochastic integral or bracket assumption.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem IsPreBrownianReal.integral_eval_sq (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, B t ω ^ 2 ∂P) = (t : ℝ) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hL := hB.hasLaw_eval t
  have h := variance_eq_sub hL.hasGaussianLaw.memLp_two
  rw [hL.variance_eq, variance_id_gaussianReal, hB.integral_eval] at h
  simpa using h.symm

theorem IsPreBrownianReal.condExp_increment_natural
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u)) (s u : ℝ≥0) :
    P[(fun ω ↦ B (s + u) ω - B s ω) |
      Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable) s] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h := hB.condExp_futureIncrements_natural hBm s (fun _ : Unit ↦ u)
    (fun x ↦ x ()) (measurable_pi_apply ())
  simpa only [Function.comp_def, brownianFutureIncrements,
    (hB.shift s).integral_eval u] using h

theorem IsPreBrownianReal.condExp_increment_sq_natural
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u)) (s u : ℝ≥0) :
    P[(fun ω ↦ (B (s + u) ω - B s ω) ^ 2) |
      Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable) s] =ᵐ[P]
      fun _ ↦ (u : ℝ) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h := hB.condExp_futureIncrements_natural hBm s (fun _ : Unit ↦ u)
    (fun x ↦ (x ()) ^ 2) (by fun_prop)
  simpa only [Function.comp_def, brownianFutureIncrements,
    (hB.shift s).integral_eval_sq u] using h

theorem IsPreBrownianReal.martingale_natural
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u)) :
    Martingale B (Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)) P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F := Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)
  have had : StronglyAdapted F B := Filtration.stronglyAdapted_natural _
  refine ⟨had, fun s t hst ↦ ?_⟩
  have heq : s + (t - s) = t := add_tsub_cancel_of_le hst
  have hinc := hB.condExp_increment_natural hBm s (t - s)
  rw [heq] at hinc
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) (had s) (hB.integrable_eval s)] at hsub
  filter_upwards [hsub, hinc] with ω hω hz
  change P[(fun ω ↦ B t ω - B s ω) | F s] ω = 0 at hz
  change P[B t | F s] ω = B s ω
  change P[(fun ω ↦ B t ω - B s ω) | F s] ω = P[B t | F s] ω - B s ω at hω
  linarith

theorem IsPreBrownianReal.isSquareIntegrableMartingale_natural
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u)) :
    IsSquareIntegrableMartingale B (Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)) P :=
  ⟨hB.martingale_natural hBm, fun t ↦ (hB.hasLaw_eval t).hasGaussianLaw.memLp_two⟩

theorem IsPreBrownianReal.square_sub_time_martingale_natural
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u)) :
    Martingale (fun t ω ↦ B t ω ^ 2 - (t : ℝ))
      (Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)) P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F := Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)
  have had : StronglyAdapted F B := Filtration.stronglyAdapted_natural _
  have h2 (t : ℝ≥0) : MemLp (B t) 2 P := (hB.hasLaw_eval t).hasGaussianLaw.memLp_two
  refine ⟨fun t ↦ ((had t).pow 2).sub stronglyMeasurable_const, fun s t hst ↦ ?_⟩
  change P[(fun ω ↦ B t ω ^ 2 - (t : ℝ)) | F s] =ᵐ[P] (fun ω ↦ B s ω ^ 2 - (s : ℝ))
  let Z : Ω → ℝ := fun ω ↦ B t ω - B s ω
  have hZ2 : MemLp Z 2 P := (h2 t).sub (h2 s)
  have hZ : Integrable Z P := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hprod : Integrable (B s * Z) P := (h2 s).integrable_mul hZ2
  have hz := hB.condExp_increment_natural hBm s (t - s)
  have hz2 := hB.condExp_increment_sq_natural hBm s (t - s)
  rw [add_tsub_cancel_of_le hst] at hz hz2
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := F s) (had s) hprod hZ
  have hsquare : (fun ω ↦ B t ω ^ 2 - (t : ℝ)) =
      (fun ω ↦ Z ω ^ 2) + (2 : ℝ) • (B s * Z) + (fun ω ↦ B s ω ^ 2 - (t : ℝ)) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Z]
    ring
  rw [hsquare]
  have hlast : StronglyMeasurable[F s] (fun ω ↦ B s ω ^ 2 - (t : ℝ)) :=
    ((had s).pow 2).sub stronglyMeasurable_const
  have hlastInt : Integrable (fun ω ↦ B s ω ^ 2 - (t : ℝ)) P :=
    (h2 s).integrable_sq.sub (integrable_const _)
  have hcond := condExp_add (hZ2.integrable_sq.add (hprod.smul (2 : ℝ))) hlastInt (F s)
  have hcond' := condExp_add hZ2.integrable_sq (hprod.smul (2 : ℝ)) (F s)
  have hsmul := condExp_smul (μ := P) (2 : ℝ) (B s * Z) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) hlast hlastInt] at hcond
  filter_upwards [hcond, hcond', hsmul, hpull, hz, hz2] with ω hc hc' hsm hp hzω hz2ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hc hc' hsm hp
  have hdiff : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - s := NNReal.coe_sub hst
  change P[Z | F s] ω = 0 at hzω
  change P[(fun ω ↦ Z ω ^ 2) | F s] ω = ((t - s : ℝ≥0) : ℝ) at hz2ω
  rw [hc, hc', hsm, hp, hzω, hz2ω, hdiff]
  ring

theorem IsBrownianReal.isContinuousLocalMartingale_natural
    (hB : IsBrownianReal B P) (hBm : ∀ u, Measurable (B u)) :
    IsContinuousLocalMartingale B
      (Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)) P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (hB.toIsPreBrownianReal.martingale_natural hBm).isContinuousLocalMartingale hB.cont

end ProbabilityTheory

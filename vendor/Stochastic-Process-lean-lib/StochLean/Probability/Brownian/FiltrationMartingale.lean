/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Martingale
public import Mathlib.Probability.ConditionalExpectation

/-! # Brownian martingales in a compatible filtration

Brownian finite-dimensional laws alone do not imply the martingale property
in an arbitrary larger filtration. Adaptedness and increment independence
from that filtration's past are explicit here. No bracket hypothesis is used.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

theorem IsPreBrownianReal.condExp_increment_of_indep_past
    (hB : IsPreBrownianReal B P) (ha : Adapted F B) {s t : ℝ≥0} (hst : s ≤ t)
    (hind : Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    P[fun ω ↦ B t ω - B s ω | F s] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
  have hi : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    simpa only [add_tsub_cancel_of_le hst] using (hB.shift s).integral_eval (t - s)
  have h := condExp_indep_eq ((ha.measurable (i := t)).sub
    (ha.measurable (i := s))).comap_le (F.le s)
    (comap_measurable (fun ω ↦ B t ω - B s ω)).stronglyMeasurable hind.symm
  simpa only [hi] using h

theorem IsPreBrownianReal.condExp_increment_sq_of_indep_past
    (hB : IsPreBrownianReal B P) (ha : Adapted F B) {s t : ℝ≥0} (hst : s ≤ t)
    (hind : Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    P[fun ω ↦ (B t ω - B s ω) ^ 2 | F s] =ᵐ[P] fun _ ↦ (t : ℝ) - s := by
  have hi : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - s := by
    simpa only [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using
      (hB.shift s).integral_eval_sq (t - s)
  have h := condExp_indep_eq ((ha.measurable (i := t)).sub
    (ha.measurable (i := s))).comap_le (F.le s)
    ((comap_measurable (fun ω ↦ B t ω - B s ω)).stronglyMeasurable.pow 2) hind.symm
  change P[fun ω ↦ (B t ω - B s ω) ^ 2 | F s] =ᵐ[P]
    fun _ ↦ ∫ ω, (B t ω - B s ω) ^ 2 ∂P at h
  simpa only [hi] using h

theorem IsPreBrownianReal.martingale_of_indep_past
    (hB : IsPreBrownianReal B P) (ha : Adapted F B)
    (hind : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    Martingale B F P := by
  refine ⟨ha.stronglyAdapted, fun s t hst ↦ ?_⟩
  have hz := hB.condExp_increment_of_indep_past ha hst (hind s t hst)
  have he := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) (ha s).stronglyMeasurable
    (hB.integrable_eval s)] at he
  filter_upwards [hz, he] with ω hzω heω
  change P[fun ω ↦ B t ω - B s ω | F s] ω =
    P[B t | F s] ω - B s ω at heω
  linarith

theorem IsPreBrownianReal.square_sub_time_martingale_of_indep_past
    (hB : IsPreBrownianReal B P) (ha : Adapted F B)
    (hind : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    Martingale (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) F P := by
  have h2 (t : ℝ≥0) : MemLp (B t) 2 P := (hB.hasLaw_eval t).hasGaussianLaw.memLp_two
  refine ⟨fun t ↦ ((ha t).stronglyMeasurable.pow 2).sub stronglyMeasurable_const,
    fun s t hst ↦ ?_⟩
  change P[fun ω ↦ B t ω ^ 2 - (t : ℝ) | F s] =ᵐ[P] fun ω ↦ B s ω ^ 2 - (s : ℝ)
  let Z : Ω → ℝ := fun ω ↦ B t ω - B s ω
  have hZ2 : MemLp Z 2 P := (h2 t).sub (h2 s)
  have hZ : Integrable Z P := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hp : Integrable (B s * Z) P := (h2 s).integrable_mul hZ2
  have hz := hB.condExp_increment_of_indep_past ha hst (hind s t hst)
  have hz2 := hB.condExp_increment_sq_of_indep_past ha hst (hind s t hst)
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := F s)
    (ha s).stronglyMeasurable hp hZ
  have he : (fun ω ↦ B t ω ^ 2 - (t : ℝ)) =
      (fun ω ↦ Z ω ^ 2) + (2 : ℝ) • (B s * Z) + (fun ω ↦ B s ω ^ 2 - (t : ℝ)) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Z]
    ring
  rw [he]
  have hlast : StronglyMeasurable[F s] (fun ω ↦ B s ω ^ 2 - (t : ℝ)) :=
    ((ha s).stronglyMeasurable.pow 2).sub stronglyMeasurable_const
  have hlastI : Integrable (fun ω ↦ B s ω ^ 2 - (t : ℝ)) P :=
    (h2 s).integrable_sq.sub (integrable_const _)
  have hc := condExp_add (hZ2.integrable_sq.add (hp.smul (2 : ℝ))) hlastI (F s)
  have hc' := condExp_add hZ2.integrable_sq (hp.smul (2 : ℝ)) (F s)
  have hs := condExp_smul (μ := P) (2 : ℝ) (B s * Z) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) hlast hlastI] at hc
  filter_upwards [hc, hc', hs, hpull, hz, hz2] with ω hcω hcω' hsω hpω hzω hz2ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hcω hcω' hsω hpω
  change P[Z | F s] ω = 0 at hzω
  change P[fun ω ↦ Z ω ^ 2 | F s] ω = (t : ℝ) - s at hz2ω
  rw [hcω, hcω', hsω, hpω, hzω, hz2ω]
  ring

theorem IsBrownianReal.isContinuousLocalMartingale_of_indep_past
    (hB : IsBrownianReal B P) (ha : Adapted F B)
    (hind : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    IsContinuousLocalMartingale B F P :=
  (hB.toIsPreBrownianReal.martingale_of_indep_past ha hind).isContinuousLocalMartingale hB.cont

end ProbabilityTheory

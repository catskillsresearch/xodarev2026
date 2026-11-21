/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.KernelHazardUniformIntegrability
public import StochLean.Probability.Process.Counting.KernelHazardPaths
public import StochLean.Probability.Process.Counting.HazardUnrestrictedMartingale
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Bounded history clocks and actual kernel hazard increments

A bounded measurable observation clock may depend on the actual history
and lifetime. The original stopped kernel hazard at that clock is integrable:
its norm is dominated by the deterministic terminal stopped hazard on the
single joint full-measure monotonicity event.

For ordered bounded history clocks, the actual compensated single-jump
increment has zero integral on a measurable history event intersected with
survival at the earlier clock. Genuine composition-product Fubini reduces
this to the already proved single-law martingale identity in each fiber.
This is an integral identity, not a claim that future histories are initially
known in the natural filtration of the full arrival count.

The whole family of measurable clocks bounded by its calendar index also
retains UI. Its compensated count is dominated by two plus the norm of the
original calendar-time compensated count, a genuine uniformly integrable
family. No optional-sampling property of the arbitrary clocks is asserted.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {H : Type*} {mH : MeasurableSpace H}

/-- A bounded measurable joint clock preserves integrability of the actual
stopped kernel hazard, by its common-event monotone path bound. -/
theorem integrable_stopped_eCumulativeHazard_kernel_clock
    (η : Measure H) [IsFiniteMeasure η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsMarkovKernel κ]
    {q : H × WithTop ℝ≥0 → ℝ≥0} (hq : Measurable q)
    {T : ℝ≥0} (hqT : ∀ p, q p ≤ T) :
    Integrable (fun p : H × WithTop ℝ≥0 ↦ stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id (q p) p.2) (η ⊗ₘ κ) := by
  have hm : Measurable (fun p : H × WithTop ℝ≥0 ↦ stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id (q p) p.2) :=
    (measurable_eCumulativeHazard_kernel κ).ennreal_toReal.comp
      (measurable_fst.prodMk
        ((WithTop.continuous_coe.measurable.comp hq).min measurable_snd).untopA)
  apply (integrable_stoppedProcess_eCumulativeHazard_compProd η κ T).1.mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_compProd_stopped_eCumulativeHazard_paths η κ] with p hp
  have hn : 0 ≤ stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id (q p) p.2 := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact hp.2.1 (hqT p)

/-- On a history event and earlier-clock survival, the original compensated
kernel count has zero expected increment between ordered bounded history clocks. -/
theorem setIntegral_singleJump_sub_hazard_compProd_clock_sub
    (η : Measure H) [IsFiniteMeasure η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsMarkovKernel κ]
    {a b : H → ℝ≥0} (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ h, a h ≤ b h) {T : ℝ≥0} (hbT : ∀ h, b h ≤ T)
    {B : Set H} (hB : MeasurableSet B) :
    (∫ p : H × WithTop ℝ≥0 in {p | p.1 ∈ B ∧ (a p.1 : WithTop ℝ≥0) < p.2},
      ((if p.2 ≤ (b p.1 : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
          id (b p.1) p.2) -
      ((if p.2 ≤ (a p.1 : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
          id (a p.1) p.2) ∂(η ⊗ₘ κ)) = 0 := by
  classical
  let M : (H → ℝ≥0) → H × WithTop ℝ≥0 → ℝ := fun q p ↦
    (if p.2 ≤ (q p.1 : WithTop ℝ≥0) then 1 else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id (q p.1) p.2
  have hi (q : H → ℝ≥0) (hq : Measurable q) (hqT : ∀ h, q h ≤ T) :
      Integrable (M q) (η ⊗ₘ κ) := by
    have hmC : Measurable (fun p : H × WithTop ℝ≥0 ↦
        if p.2 ≤ (q p.1 : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd
        (WithTop.continuous_coe.measurable.comp (hq.comp measurable_fst)))
        measurable_const measurable_const
    have hiC : Integrable (fun p : H × WithTop ℝ≥0 ↦
        if p.2 ≤ (q p.1 : WithTop ℝ≥0) then (1 : ℝ) else 0) (η ⊗ₘ κ) := by
      apply (integrable_const (1 : ℝ)).mono' hmC.aestronglyMeasurable
      exact ae_of_all _ fun p ↦ by split_ifs <;> norm_num
    exact hiC.sub (integrable_stopped_eCumulativeHazard_kernel_clock η κ
      (hq.comp measurable_fst) (fun p ↦ hqT p.1))
  let S : Set (H × WithTop ℝ≥0) :=
    {p | p.1 ∈ B ∧ (a p.1 : WithTop ℝ≥0) < p.2}
  have hS : MeasurableSet S := (measurable_fst hB).inter
    (measurableSet_lt (WithTop.continuous_coe.measurable.comp (ha.comp measurable_fst))
      measurable_snd)
  have hiD := (hi b hb hbT).sub (hi a ha (fun h ↦ (hab h).trans (hbT h)))
  change Integrable (fun p ↦ M b p - M a p) (η ⊗ₘ κ) at hiD
  change (∫ p in S, M b p - M a p ∂(η ⊗ₘ κ)) = 0
  rw [← integral_indicator hS, Measure.integral_compProd (hiD.indicator hS)]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro h
  change (∫ v, S.indicator (fun p ↦ M b p - M a p) (h, v) ∂κ h) = 0
  by_cases hh : h ∈ B
  · have he : (fun v ↦ S.indicator (fun p ↦ M b p - M a p) (h, v)) =
        (Ioi (a h : WithTop ℝ≥0)).indicator (fun v ↦ M b (h, v) - M a (h, v)) := by
      funext v
      simp only [S, indicator_apply, mem_ofPred_eq, hh, true_and, mem_Ioi]
    rw [he, integral_indicator measurableSet_Ioi]
    have hM := martingale_singleJump_sub_hazard_unrestricted (κ h)
    have hs : MeasurableSet[(Filtration.natural
        (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount measurable_id)) (a h)]
        (Ioi (a h : WithTop ℝ≥0)) := by
      apply (measurableSet_natural_singleJumpCount_iff measurable_id (a h) _).mpr
      exact ⟨∅, MeasurableSet.empty, empty_subset _,
        Or.inr (by simp only [preimage_empty, empty_union]; rfl)⟩
    change (∫ v in Ioi (a h : WithTop ℝ≥0),
      ((if v ≤ (b h : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ h) r).toReal)
          id (b h) v) -
      ((if v ≤ (a h : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ h) r).toReal)
          id (a h) v) ∂κ h) = 0
    rw [integral_sub (hM.integrable (b h)).integrableOn (hM.integrable (a h)).integrableOn]
    exact sub_eq_zero.mpr (hM.setIntegral_eq (hab h) hs).symm
  · have he : (fun v ↦ S.indicator (fun p ↦ M b p - M a p) (h, v)) = 0 := by
      funext v
      simp only [S, indicator_apply, mem_ofPred_eq, hh, false_and, if_false, Pi.zero_apply]
    rw [he]
    change (∫ _ : WithTop ℝ≥0, (0 : ℝ) ∂κ h) = 0
    exact integral_zero _ _

/-- Measurable observation clocks bounded by their calendar index retain
global UI of the actual compensated kernel count, even when the clock also
depends on the lifetime. No stopping-time claim about these clocks is made. -/
theorem uniformIntegrable_singleJump_sub_hazard_compProd_clock
    (η : Measure H) [IsFiniteMeasure η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsMarkovKernel κ]
    {q : ℝ≥0 → H × WithTop ℝ≥0 → ℝ≥0}
    (hq : ∀ t, Measurable (q t)) (hqt : ∀ t p, q t p ≤ t) :
    UniformIntegrable (fun (t : ℝ≥0) (p : H × WithTop ℝ≥0) ↦
      (if p.2 ≤ (q t p : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id (q t p) p.2) 1 (η ⊗ₘ κ) := by
  classical
  let A : ℝ≥0 → H × WithTop ℝ≥0 → ℝ := fun t p ↦ stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal) id t p.2
  let C : ℝ≥0 → H × WithTop ℝ≥0 → ℝ :=
    fun t p ↦ if p.2 ≤ (t : WithTop ℝ≥0) then 1 else 0
  let M : ℝ≥0 → H × WithTop ℝ≥0 → ℝ := fun t p ↦ C t p - A t p
  have huM : UniformIntegrable M 1 (η ⊗ₘ κ) :=
    uniformIntegrable_singleJump_sub_hazard_compProd η κ
  have huNorm : UniformIntegrable (fun t p ↦ ‖M t p‖) 1 (η ⊗ₘ κ) :=
    huM.mono_norm (fun t ↦ (huM.1 t).norm)
      (fun _ ↦ ae_of_all _ fun _ ↦ by rw [norm_norm])
  have huConst : UniformIntegrable
      (fun (_ : ℝ≥0) (_ : H × WithTop ℝ≥0) ↦ (2 : ℝ)) 1 (η ⊗ₘ κ) :=
    uniformIntegrable_const le_rfl (by simp) (memLp_const 2)
  have hu := huConst.add huNorm le_rfl
  apply hu.mono_norm
  · intro t
    have hmC : Measurable (fun p : H × WithTop ℝ≥0 ↦
        if p.2 ≤ (q t p : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd
        (WithTop.continuous_coe.measurable.comp (hq t))) measurable_const measurable_const
    have hmA : Measurable (fun p : H × WithTop ℝ≥0 ↦ A (q t p) p) :=
      (measurable_eCumulativeHazard_kernel κ).ennreal_toReal.comp
        (measurable_fst.prodMk
          ((WithTop.continuous_coe.measurable.comp (hq t)).min measurable_snd).untopA)
    exact (hmC.sub hmA).stronglyMeasurable.aestronglyMeasurable
  intro t
  filter_upwards [ae_compProd_stopped_eCumulativeHazard_paths η κ] with p hp
  have ha : A (q t p) p ≤ A t p := hp.2.1 (hqt t p)
  have hnonneg : 0 ≤ A (q t p) p := ENNReal.toReal_nonneg
  have hnorm : ‖A (q t p) p‖ = A (q t p) p := abs_of_nonneg hnonneg
  have hcq : ‖C (q t p) p‖ ≤ 1 := by dsimp only [C]; split_ifs <;> norm_num
  have hct : C t p ≤ 1 := by dsimp only [C]; split_ifs <;> norm_num
  have hm : -(C t p - A t p) ≤ ‖M t p‖ := neg_le_abs (M t p)
  change ‖C (q t p) p - A (q t p) p‖ ≤ ‖(2 : ℝ) + ‖M t p‖‖
  calc
    _ ≤ ‖C (q t p) p‖ + ‖A (q t p) p‖ := norm_sub_le _ _
    _ ≤ 1 + A (q t p) p := by
      rw [hnorm]
      exact add_le_add hcq le_rfl
    _ ≤ 1 + A t p := add_le_add le_rfl ha
    _ ≤ 2 + ‖M t p‖ := by linarith
    _ = ‖(2 : ℝ) + ‖M t p‖‖ := by
      exact (abs_of_nonneg (show 0 ≤ (2 : ℝ) + ‖M t p‖ by positivity)).symm

end ProbabilityTheory

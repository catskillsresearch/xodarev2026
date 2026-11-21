/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.ConsistentLocalization
public import StochLean.Probability.Process.Measurability.Predictable

/-! # Predictable cadlag limits of stopped-consistent local processes

The existing stopped-consistency estimate and UCP completion supply the limit.
Stopping and UCP uniqueness recover every local level, which makes the entire
sequence eventually equal to the limit on every compact interval on one event.

A usual initial-null reset is applied to both that limit and the predictable
approximants. The reset sequence converges pointwise everywhere, so its limit
is genuinely predictable by the native strong-measurability limit theorem.
Predictability is not inferred from an arbitrary indistinguishable change.
No martingale, integrable-variation, or additional limit-selector owner is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}
  {A : ℕ → ℝ≥0 → Ω → ℝ}

/-- Stopped consistency constructs an actual predictable, everywhere-cadlag
UCP limit. The full sequence is eventually equal to it on each compact interval
on one common event, and stopping recovers every original local process. -/
theorem IsPreLocalizingSequence.exists_predictable_cadlag_limit_of_stopped_consistency
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (hp : ∀ n, IsStronglyPredictable F (A n)) (hc : ∀ n, HasCadlagPaths (A n) P)
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F Y ∧ (∀ ω, IsCadlagPath (Y · ω)) ∧ TendstoUCP P A atTop Y ∧
      (∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, ∀ t ≤ T, A n t ω = Y t ω := by
  classical
  have hC := hτ.cauchyUCP_of_stopped_consistency hcons
  obtain ⟨V, _, hVc, hAV⟩ := hC.exists_adapted_cadlag_limit
    (fun n ↦ (hp n).stronglyAdapted.adapted) hF hc
  have hrV : HasRightContinuousPaths V P :=
    Eventually.of_forall fun ω ↦ (hVc ω).1
  have hstop : ∀ n, Indistinguishable (stoppedProcess V (τ n)) (A n) P := by
    intro n
    have hs : TendstoUCP P (fun k : ℕ ↦ stoppedProcess (A (k + n)) (τ n)) atTop
        (stoppedProcess V (τ n)) :=
      (hAV.comp (tendsto_add_atTop_nat n)).stoppedProcess (τ n)
    have he : TendstoUCP P (fun k : ℕ ↦ stoppedProcess (A (k + n)) (τ n)) atTop
        (A n) :=
      (tendstoUCP_const (P := P) atTop (A n)).congr_left
        (fun k ↦ (hcons n (k + n) (Nat.le_add_left n k)).symm)
    exact hs.indistinguishable_unique he (hrV.stoppedProcess (τ n))
      (hc n).hasRightContinuousPaths
  have hevent : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop,
      ∀ t ≤ T, A n t ω = V t ω := by
    filter_upwards [ae_all_iff.mpr hstop, hτ.tendsto_top] with ω hω hτω T
    filter_upwards [hτω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
    intro t ht
    have htime : (t : WithTop ℝ≥0) ≤ τ n ω :=
      (WithTop.coe_le_coe.mpr ht).trans hn.le
    have he := hω n t
    rw [stoppedProcess_eq_of_le htime] at he
    exact he.symm
  let good : Set Ω := {ω | ∀ T : ℝ≥0, ∀ᶠ n in atTop, ∀ t ≤ T, A n t ω = V t ω}
  have hbad : MeasurableSet[F 0] goodᶜ := hF.complete_initial goodᶜ (ae_iff.mp hevent)
  have hgood : MeasurableSet[F 0] good := by
    simpa only [compl_compl] using hbad.compl
  let K : ℝ≥0 → Ω → ℝ := fun _ ω ↦ if ω ∈ good then 1 else 0
  have haK : Adapted F K := fun t ↦
    Measurable.ite (F.mono bot_le _ hgood) measurable_const measurable_const
  have hpK : IsStronglyPredictable F K :=
    haK.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  let B : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ A n * K
  let Y : ℝ≥0 → Ω → ℝ := V * K
  have hBp (n : ℕ) : IsStronglyPredictable F (B n) := (hp n).mul hpK
  have hlim (t : ℝ≥0) (ω : Ω) : Tendsto (fun n ↦ B n t ω) atTop (𝓝 (Y t ω)) := by
    by_cases hω : ω ∈ good
    · have he : (fun n ↦ B n t ω) =ᶠ[atTop] (fun _ ↦ Y t ω) := by
        filter_upwards [hω t] with n hn
        simpa only [B, Y, Pi.mul_apply, K, if_pos hω, mul_one] using hn t le_rfl
      exact tendsto_const_nhds.congr' he.symm
    · simpa only [B, Y, Pi.mul_apply, K, if_neg hω, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hYp : IsStronglyPredictable F Y := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    change StronglyMeasurable (Function.uncurry Y)
    apply stronglyMeasurable_of_tendsto atTop (fun n : ℕ ↦ hBp n)
    exact tendsto_pi_nhds.mpr fun p ↦ hlim p.1 p.2
  have hYc (ω : Ω) : IsCadlagPath (Y · ω) := by
    by_cases hω : ω ∈ good
    · simpa only [Y, Pi.mul_apply, K, if_pos hω, mul_one] using hVc ω
    · simpa only [Y, Pi.mul_apply, K, if_neg hω, mul_zero] using
        (IsContinuousPath.isCadlagPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  have heVY : Indistinguishable V Y P := by
    filter_upwards [hevent] with ω hω t
    have hg : ω ∈ good := hω
    simp only [Y, Pi.mul_apply, K, if_pos hg, mul_one]
  refine ⟨Y, hYp, hYc, hAV.congr_right heVY,
    fun n ↦ (heVY.symm.stoppedProcess (τ n)).trans (hstop n), ?_⟩
  filter_upwards [hevent, heVY] with ω hω heω T
  exact (hω T).mono fun _ hn t ht ↦ (hn t ht).trans (heω t)

/-- Monotonicity and the almost-sure zero initial value pass to the same
actual predictable limit through the existing UCP inheritance theorems. -/
theorem IsPreLocalizingSequence.exists_predictable_cadlag_monotone_limit_of_stopped_consistency
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (hp : ∀ n, IsStronglyPredictable F (A n)) (hc : ∀ n, HasCadlagPaths (A n) P)
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P)
    (hm : ∀ n, HasMonotonePaths (A n) P) (h0 : ∀ n, A n 0 =ᵐ[P] 0) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F Y ∧ (∀ ω, IsCadlagPath (Y · ω)) ∧ TendstoUCP P A atTop Y ∧
      (∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P) ∧
      HasMonotonePaths Y P ∧ HasFiniteVariationPaths Y P ∧ Y 0 =ᵐ[P] 0 ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Y t ω) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, ∀ t ≤ T, A n t ω = Y t ω := by
  obtain ⟨Y, hpY, hcY, hAY, hstop, hevent⟩ :=
    hτ.exists_predictable_cadlag_limit_of_stopped_consistency hF hp hc hcons
  exact ⟨Y, hpY, hcY, hAY, hstop, hAY.hasMonotonePaths hm,
    (hAY.hasMonotonePaths hm).hasFiniteVariationPaths, hAY.ae_eq_initial h0,
    hAY.ae_nonneg_of_monotone_zero hm h0, hevent⟩

end ProbabilityTheory

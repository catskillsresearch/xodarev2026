/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.CagladContinuousLimit
public import StochLean.Probability.Process.UCP.Stopping
public import StochLean.Probability.Process.UCP.MonotoneLimit
public import StochLean.Probability.Process.Stopping.LocalizingTail
public import StochLean.Probability.Process.Path.FiniteVariation

/-! # Continuous UCP limits of consistent localized processes

Stopping consistency makes the local processes eventually identical on
each compact interval, outside an event controlled by the localizer tail.
The existing UCP completion constructs the limit; this module introduces
no alternative limit selector.

Stopping the shifted convergent sequence and using UCP uniqueness proves
that the global limit recovers every local process after stopping. This
argument concerns whole paths, including times after a finite cutoff,
and retains infinite cutoffs without evaluating an infinite time.

Only a pre-localizing sequence is needed: the assumed stopped consistency
already supplies the compact comparison, without using monotonicity of
the lifetimes. In particular the results apply to localizing sequences
whose monotonicity holds only almost surely. No martingale or uniform
integrability conclusion is asserted by this generic path construction.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}
  {A : ℕ → ℝ≥0 → Ω → ℝ}

/-- Actual stopped consistency and vanishing early-localization tails imply
the UCP-Cauchy property. No path regularity is needed for this step. -/
theorem IsPreLocalizingSequence.cauchyUCP_of_stopped_consistency
    (hτ : IsPreLocalizingSequence F τ P)
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P) :
    CauchyUCP P A := by
  intro T ε hε η hη
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp (hτ.tendsto_measure_le T) η hη
  refine ⟨N, fun m n hm hn ↦ le_trans ?_ (hN N le_rfl)⟩
  apply measure_mono_ae
  filter_upwards [hcons N m hm, hcons N n hn] with ω hmω hnω hdev
  by_contra hnot
  have hTN : (T : WithTop ℝ≥0) < τ N ω := lt_of_not_ge hnot
  obtain ⟨t, ht, hgt⟩ := hdev
  have htime : (t : WithTop ℝ≥0) ≤ τ N ω :=
    (WithTop.coe_le_coe.mpr ht).trans hTN.le
  have hem : A m t ω = A N t ω := by
    simpa only [stoppedProcess_eq_of_le htime] using hmω t
  have hen : A n t ω = A N t ω := by
    simpa only [stoppedProcess_eq_of_le htime] using hnω t
  rw [hem, hen, sub_self, norm_zero] at hgt
  exact (not_lt_of_ge hε.le) hgt

/-- A consistent family of adapted continuous local processes has an
actual adapted everywhere-continuous UCP limit, and stopping recovers every
level. A common event supports eventual compact equality of the full sequence. -/
theorem IsPreLocalizingSequence.exists_continuous_limit_of_stopped_consistency
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (ha : ∀ n, Adapted F (A n)) (hc : ∀ n ω, Continuous (A n · ω))
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      Adapted F Y ∧ (∀ ω, Continuous (Y · ω)) ∧ TendstoUCP P A atTop Y ∧
      (∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, ∀ t ≤ T, A n t ω = Y t ω := by
  have hC := hτ.cauchyUCP_of_stopped_consistency hcons
  have hcag : ∀ n, HasCagladPaths (A n) P := fun n ↦
    Eventually.of_forall fun ω ↦ IsContinuousPath.isCagladPath (hc n ω)
  have hR : TendstoInMeasure P (fun _ : ℕ ↦ (0 : Ω → ℝ)) atTop 0 :=
    (tendstoUCP_const (P := P) atTop (0 : ℝ≥0 → Ω → ℝ)).fixedTime 0
  have hgap : ∀ n, ∀ᵐ ω ∂P, ∀ t,
      ‖rightLimitProcess (A n) t ω - A n t ω‖ ≤ (0 : ℝ) := by
    intro n
    refine Eventually.of_forall fun ω t ↦ ?_
    rw [(IsContinuousPath.isRightContinuousPath (hc n ω)).rightLimitProcess_eq,
      sub_self, norm_zero]
  obtain ⟨Y, hYa, hYc, hAY⟩ :=
    hC.exists_everywhere_continuous_limit_of_caglad ha hF hcag hR hgap
  have hrY : HasRightContinuousPaths Y P :=
    Eventually.of_forall fun ω ↦ IsContinuousPath.isRightContinuousPath (hYc ω)
  have hrecovery : ∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P := by
    intro n
    have hs : TendstoUCP P (fun k : ℕ ↦ stoppedProcess (A (k + n)) (τ n)) atTop
        (stoppedProcess Y (τ n)) :=
      (hAY.comp (tendsto_add_atTop_nat n)).stoppedProcess (τ n)
    have he : TendstoUCP P (fun k : ℕ ↦ stoppedProcess (A (k + n)) (τ n)) atTop
        (A n) :=
      (tendstoUCP_const (P := P) atTop (A n)).congr_left
        (fun k ↦ (hcons n (k + n) (Nat.le_add_left n k)).symm)
    exact hs.indistinguishable_unique he (hrY.stoppedProcess (τ n))
      (Eventually.of_forall fun ω ↦ IsContinuousPath.isRightContinuousPath (hc n ω))
  refine ⟨Y, hYa, hYc, hAY, hrecovery, ?_⟩
  filter_upwards [ae_all_iff.mpr hrecovery, hτ.tendsto_top] with ω hω hτω T
  filter_upwards [hτω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
  intro t ht
  have htime : (t : WithTop ℝ≥0) ≤ τ n ω :=
    (WithTop.coe_le_coe.mpr ht).trans hn.le
  have he := hω n t
  rw [stoppedProcess_eq_of_le htime] at he
  exact he.symm

/-- Initial values and monotone paths pass to the same constructed limit by
the existing UCP inheritance results. The initial equality is almost sure;
no additional pointwise normalization is silently imposed. -/
theorem IsPreLocalizingSequence.exists_continuous_monotone_limit_of_stopped_consistency
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (ha : ∀ n, Adapted F (A n)) (hc : ∀ n ω, Continuous (A n · ω))
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P)
    (hm : ∀ n, HasMonotonePaths (A n) P) (h0 : ∀ n, A n 0 =ᵐ[P] 0) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      Adapted F Y ∧ (∀ ω, Continuous (Y · ω)) ∧ TendstoUCP P A atTop Y ∧
      (∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P) ∧
      HasMonotonePaths Y P ∧ HasFiniteVariationPaths Y P ∧ Y 0 =ᵐ[P] 0 ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Y t ω) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, ∀ t ≤ T, A n t ω = Y t ω := by
  obtain ⟨Y, hYa, hYc, hAY, hstop, hevent⟩ :=
    hτ.exists_continuous_limit_of_stopped_consistency hF ha hc hcons
  exact ⟨Y, hYa, hYc, hAY, hstop, hAY.hasMonotonePaths hm,
    (hAY.hasMonotonePaths hm).hasFiniteVariationPaths, hAY.ae_eq_initial h0,
    hAY.ae_nonneg_of_monotone_zero hm h0, hevent⟩

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.FirstExit
public import StochLean.Probability.Process.Path.Oscillation
public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual

/-! # Recursive oscillation stopping times

The next time is the existing first hit of `X - X^tau`, so it never evaluates an
unprovided value `X_infinity`. For a positive threshold, finite successive times
are strictly separated and their sampled values differ by at least the threshold.
Cadlag paths therefore force the actual recursive times to tend to infinity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

noncomputable def nextOscillationTime (X : ℝ≥0 → Ω → ℝ) (ε : ℝ)
    (τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  hittingAfter (X - stoppedProcess X τ) {x | ε < ‖x‖} 0

theorem nextOscillationTime_const (Z : Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    nextOscillationTime (fun _ : ℝ≥0 ↦ Z) ε τ ω = ⊤ := by
  apply hittingAfter_eq_top_iff.mpr
  intro t _
  change ¬ ε < ‖Z ω - stoppedProcess (fun _ : ℝ≥0 ↦ Z) τ t ω‖
  simp only [stoppedProcess_const, sub_self, norm_zero]
  exact not_lt_of_ge hε

theorem le_nextOscillationTime {ε : ℝ} (hε : 0 ≤ ε) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    τ ω ≤ nextOscillationTime X ε τ ω := by
  cases hτ : τ ω with
  | top =>
    have heq : nextOscillationTime X ε τ ω = ⊤ := by
      apply hittingAfter_eq_top_iff.mpr
      intro t _
      change ¬ ε < ‖X t ω - stoppedProcess X τ t ω‖
      rw [stoppedProcess_eq_of_le (by rw [hτ]; exact le_top), sub_self, norm_zero]
      exact not_lt_of_ge hε
    rw [heq]
  | coe T =>
    by_contra hn
    have hlt : nextOscillationTime X ε τ ω < (T : WithTop ℝ≥0) := lt_of_not_ge hn
    obtain ⟨t, ht, hhit⟩ := hittingAfter_lt_iff.mp hlt
    have hstop : stoppedProcess X τ t ω = X t ω := stoppedProcess_eq_of_le
      (by rw [hτ]; exact WithTop.coe_le_coe.mpr ht.2.le)
    change ε < ‖X t ω - stoppedProcess X τ t ω‖ at hhit
    rw [hstop, sub_self, norm_zero] at hhit
    exact not_lt_of_ge hε hhit

private theorem rightContinuous_sub_stopped {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) :
    IsRightContinuousPath (fun t ↦ X t ω - stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top =>
    have heq : (fun t ↦ X t ω - stoppedProcess X τ t ω) = fun _ ↦ (0 : ℝ) := by
      funext t
      rw [stoppedProcess_eq_of_le (by rw [hτ]; exact le_top), sub_self]
    rw [heq]
    exact IsContinuousPath.isRightContinuousPath continuous_const
  | coe T =>
    have heq : (fun t ↦ X t ω - stoppedProcess X τ t ω) =
        fun t ↦ X t ω - X (min t T) ω := by
      funext t
      change X t ω - X (min (t : WithTop ℝ≥0) (τ ω)).untopA ω = _
      rw [hτ, ← WithTop.coe_min]
      rfl
    rw [heq]
    exact fun t ↦ (hX t).sub (hX.min_const T t)

theorem le_norm_increment_nextOscillationTime {ε : ℝ} (hε : 0 ≤ ε)
    (τ : Ω → WithTop ℝ≥0) {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    (hne : nextOscillationTime X ε τ ω ≠ ⊤) :
    ε ≤ ‖X (nextOscillationTime X ε τ ω).untopA ω - X (τ ω).untopA ω‖ := by
  have hR := le_norm_hittingAfter_norm_of_ne_top (rightContinuous_sub_stopped hX) hne
  have htime : τ ω ≤ ((nextOscillationTime X ε τ ω).untopA : WithTop ℝ≥0) := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
    exact le_nextOscillationTime hε τ ω
  change ε ≤ ‖X (nextOscillationTime X ε τ ω).untopA ω -
    stoppedProcess X τ (nextOscillationTime X ε τ ω).untopA ω‖ at hR
  rw [stoppedProcess_eq_of_ge htime] at hR
  exact hR

theorem lt_nextOscillationTime_of_ne_top {ε : ℝ} (hε : 0 < ε)
    (τ : Ω → WithTop ℝ≥0) {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    (hne : nextOscillationTime X ε τ ω ≠ ⊤) : τ ω < nextOscillationTime X ε τ ω := by
  apply lt_of_le_of_ne (le_nextOscillationTime hε.le τ ω)
  intro heq
  have h := le_norm_increment_nextOscillationTime hε.le τ hX hne
  rw [heq, sub_self, norm_zero] at h
  exact not_le_of_gt hε h

/-- On a left-open, right-closed oscillation cell, the left limit stays within the
threshold of the original sample. The right endpoint need not be a hit of the open target. -/
theorem norm_leftLimit_sub_le_of_oscillation_interval (τ : Ω → WithTop ℝ≥0)
    {ω : Ω} (hX : IsCadlagPath (X · ω)) {ε : ℝ} {t : ℝ≥0}
    (hτt : τ ω < (t : WithTop ℝ≥0)) (htR : (t : WithTop ℝ≥0) ≤ nextOscillationTime X ε τ ω) :
    ‖leftLimitProcess X t ω - X (τ ω).untopA ω‖ ≤ ε := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτt.le
  have hcoe : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  have hleft : (τ ω).untopA < t := WithTop.coe_lt_coe.mp (by rw [hcoe]; exact hτt)
  have ht0 : (0 : ℝ≥0) < t := (bot_le : (0 : ℝ≥0) ≤ (τ ω).untopA).trans_lt hleft
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  have hlim : Tendsto (fun s ↦ ‖X s ω - X (τ ω).untopA ω‖) (𝓝[<] t)
      (𝓝 ‖leftLimitProcess X t ω - X (τ ω).untopA ω‖) :=
    ((hX.tendsto_leftLimitProcess (ne_of_gt ht0)).sub tendsto_const_nhds).norm
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hleft] with s hs
  have hbefore := norm_le_of_lt_hittingAfter_norm (X := X - stoppedProcess X τ)
    ((WithTop.coe_lt_coe.mpr hs.2).trans_le htR)
  change ‖X s ω - stoppedProcess X τ s ω‖ ≤ ε at hbefore
  have hτs : τ ω ≤ (s : WithTop ℝ≥0) := by
    rw [← hcoe]
    exact WithTop.coe_le_coe.mpr hs.1.le
  rwa [stoppedProcess_eq_of_ge hτs] at hbefore

noncomputable def oscillationTimes (X : ℝ≥0 → Ω → ℝ) (ε : ℝ) : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ ↦ 0
  | n + 1 => nextOscillationTime X ε (oscillationTimes X ε n)

@[simp] theorem oscillationTimes_zero (ε : ℝ) (ω : Ω) : oscillationTimes X ε 0 ω = 0 := rfl

theorem oscillationTimes_const_succ (Z : Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (n : ℕ) (ω : Ω) : oscillationTimes (fun _ : ℝ≥0 ↦ Z) ε (n + 1) ω = ⊤ :=
  nextOscillationTime_const Z hε _ ω

theorem monotone_oscillationTimes {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) :
    Monotone (fun n ↦ oscillationTimes X ε n ω) :=
  monotone_nat_of_le_succ fun _ ↦ le_nextOscillationTime hε _ ω

theorem tendsto_top_oscillationTimes {ε : ℝ} (hε : 0 < ε) {ω : Ω}
    (hX : IsCadlagPath (X · ω)) :
    Tendsto (fun n ↦ oscillationTimes X ε n ω) atTop (𝓝 ⊤) :=
  hX.tendsto_top_of_separated_extended_samples (monotone_oscillationTimes hε.le ω)
    (fun n ↦ lt_nextOscillationTime_of_ne_top hε (oscillationTimes X ε n) hX.1) hε
    (fun n ↦ le_norm_increment_nextOscillationTime hε.le (oscillationTimes X ε n) hX.1)

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem isStoppingTime_nextOscillationTime (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (ε : ℝ) : IsStoppingTime F (nextOscillationTime X ε τ) := by
  have ha : Adapted F (X - stoppedProcess X τ) := fun t ↦
    (hX t).sub ((hX.stronglyAdapted.stoppedProcess_of_usual hF hr hτ).adapted t)
  have hreg : HasRightContinuousPaths (X - stoppedProcess X τ) P :=
    hr.mono fun _ hω ↦ rightContinuous_sub_stopped hω
  exact ha.isStoppingTime_hittingAfter_norm_of_usual hF hreg ε

theorem isStoppingTime_oscillationTimes (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (ε : ℝ) (n : ℕ) :
    IsStoppingTime F (oscillationTimes X ε n) := by
  induction n with
  | zero => exact isStoppingTime_const F 0
  | succ n ih => exact isStoppingTime_nextOscillationTime hX hF hr ih ε

theorem ae_tendsto_top_oscillationTimes (hc : HasCadlagPaths X P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ oscillationTimes X ε n ω) atTop (𝓝 ⊤) :=
  hc.mono fun _ hω ↦ tendsto_top_oscillationTimes hε hω

end ProbabilityTheory

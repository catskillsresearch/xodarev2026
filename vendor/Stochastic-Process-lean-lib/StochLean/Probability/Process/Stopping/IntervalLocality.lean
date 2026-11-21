/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Stopping
public import StochLean.Probability.Process.Stopping.IntegrandAE

/-! # Pathwise locality on a left-open stochastic interval

Right continuity recovers the integrator value at the excluded left endpoint.
Cutoff differences, in contrast, do not use the integrand's value there.
All statements are pathwise and allow an infinite upper endpoint.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem IsRightContinuousPath.eq_at_left_of_eqOn_Ioc {x y : ℝ≥0 → ℝ}
    (hx : IsRightContinuousPath x) (hy : IsRightContinuousPath y)
    {a b : ℝ≥0} (hab : a < b) (hxy : EqOn x y (Ioc a b)) : x a = y a := by
  have hxlim : Tendsto x (𝓝[>] a) (𝓝 (x a)) := (hx a).mono Ioi_subset_Ici_self
  have hylim : Tendsto y (𝓝[>] a) (𝓝 (y a)) := (hy a).mono Ioi_subset_Ici_self
  have heq : x =ᶠ[𝓝[>] a] y := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hab)] with t hta htb
    exact hxy ⟨hta, htb.le⟩
  exact tendsto_nhds_unique hxlim (hylim.congr' heq.symm)

variable {Ω : Type*} {X Y H K : ℝ≥0 → Ω → ℝ}
  {σ τ : Ω → WithTop ℝ≥0} {ω : Ω}

theorem cutoffIntegrand_sub_congr_on_interval (hστ : σ ω ≤ τ ω)
    (hHK : ∀ t : ℝ≥0,
      σ ω < (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω)
    (t : ℝ≥0) :
    cutoffIntegrand H τ t ω - cutoffIntegrand H σ t ω =
      cutoffIntegrand K τ t ω - cutoffIntegrand K σ t ω := by
  by_cases htσ : (t : WithTop ℝ≥0) ≤ σ ω
  · simp only [cutoffIntegrand, if_pos htσ, if_pos (htσ.trans hστ), sub_self]
  · by_cases htτ : (t : WithTop ℝ≥0) ≤ τ ω
    · simp only [cutoffIntegrand, if_pos htτ, if_neg htσ, sub_zero]
      exact hHK t (lt_of_not_ge htσ) htτ
    · simp only [cutoffIntegrand, if_neg htτ, if_neg htσ]

theorem stoppedProcess_sub_congr_on_interval
    (hX : IsRightContinuousPath (X · ω)) (hY : IsRightContinuousPath (Y · ω))
    (hστ : σ ω < τ ω)
    (hXY : ∀ t : ℝ≥0,
      σ ω < (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) ≤ τ ω → X t ω = Y t ω)
    (t : ℝ≥0) :
    stoppedProcess X τ t ω - stoppedProcess X σ t ω =
      stoppedProcess Y τ t ω - stoppedProcess Y σ t ω := by
  cases hσ : σ ω with
  | top => simp only [hσ, not_top_lt] at hστ
  | coe a =>
    have hex : ∃ b : ℝ≥0, a < b ∧ (b : WithTop ℝ≥0) ≤ τ ω := by
      cases hτ : τ ω with
      | top => exact ⟨a + 1, by simp, le_top⟩
      | coe b =>
        exact ⟨b, WithTop.coe_lt_coe.mp (by simpa only [hσ, hτ] using hστ), le_rfl⟩
    obtain ⟨b, hab, hbτ⟩ := hex
    have hstart : X a ω = Y a ω := hX.eq_at_left_of_eqOn_Ioc hY hab (fun s hs ↦
      hXY s (by rw [hσ]; exact WithTop.coe_lt_coe.mpr hs.1)
        ((WithTop.coe_le_coe.mpr hs.2).trans hbτ))
    by_cases htσ : (t : WithTop ℝ≥0) ≤ σ ω
    · rw [stoppedProcess_eq_of_le (τ := τ) (ω := ω) (htσ.trans hστ.le),
        stoppedProcess_eq_of_le (τ := σ) (ω := ω) htσ,
        stoppedProcess_eq_of_le (τ := τ) (ω := ω) (htσ.trans hστ.le),
        stoppedProcess_eq_of_le (τ := σ) (ω := ω) htσ]
      simp only [sub_self]
    · let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (τ ω)).untopA
      have hne : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hu : (u : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ ω) := by
        simp only [u, WithTop.untopA_eq_untop hne, WithTop.coe_untop]
      have hxyu : X u ω = Y u ω := hXY u
        (by rw [hu]; exact lt_min (lt_of_not_ge htσ) hστ)
        (by rw [hu]; exact min_le_right _ _)
      change X u ω - X (min (t : WithTop ℝ≥0) (σ ω)).untopA ω =
        Y u ω - Y (min (t : WithTop ℝ≥0) (σ ω)).untopA ω
      rw [min_eq_right (le_of_not_ge htσ), hσ]
      change X u ω - X a ω = Y u ω - Y a ω
      rw [hxyu, hstart]

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.TimeChange.QuadraticVariationClock

/-! # Path and stopping foundations for Dambis--Dubins--Schwarz

The actual inverse of the canonical continuous bracket gives finite stopping
times, continuous adapted sampled paths and the pathwise factorization. For
zero initial values these are the source raw-bracket inverse times. This file
keeps the path argument separate from the conditional-characteristic-function
proof of the Brownian law in `DambisDubinsSchwarzCharacteristic` and the
source raw-bracket theorem in `DambisDubinsSchwarzRaw`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.tendsto_continuousQuadraticVariation_of_raw
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Tendsto ((hX.isSemimartingale hF).quadraticVariation hF · ω) atTop atTop) :
    ∀ᵐ ω ∂P,
      Tendsto ((hX.isSemimartingale hF).continuousQuadraticVariation hF · ω) atTop atTop := by
  filter_upwards [hu,
    (hX.isSemimartingale hF).continuousQuadraticVariation_eq_of_continuous hF hX.2]
    with ω huω hq
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [huω.eventually (eventually_ge_atTop (b + (X 0 ω) ^ 2))] with t ht
  rw [hq t]
  linarith

theorem IsContinuousLocalMartingale.raw_inverse_times_eq_clock
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (h0 : X 0 =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      clockInverseTime ((hX.isSemimartingale hF).continuousBracketClock hF) s ω =
        hittingAfter ((hX.isSemimartingale hF).quadraticVariation hF) (Ioi (s : ℝ)) 0 ω := by
  filter_upwards [h0,
    (hX.isSemimartingale hF).continuousQuadraticVariation_eq_of_continuous hF hX.2]
    with ω h0ω hq s
  have he (t : ℝ≥0) :
      (hX.isSemimartingale hF).continuousBracketClock hF t ω ∈ Ioi s ↔
        (hX.isSemimartingale hF).quadraticVariation hF t ω ∈ Ioi (s : ℝ) := by
    change (s : ℝ) < ((hX.isSemimartingale hF).continuousBracketClock hF t ω : ℝ) ↔ _
    rw [(hX.isSemimartingale hF).coe_continuousBracketClock hF, hq t]
    simp only [h0ω, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero, mem_Ioi]
  have hex : (∃ t : ℝ≥0, 0 ≤ t ∧
      (hX.isSemimartingale hF).continuousBracketClock hF t ω ∈ Ioi s) ↔
      (∃ t : ℝ≥0, 0 ≤ t ∧ (hX.isSemimartingale hF).quadraticVariation hF t ω ∈ Ioi (s : ℝ)) :=
    exists_congr fun t ↦ and_congr_right fun _ ↦ he t
  classical
  dsimp only [clockInverseTime, hittingAfter]
  by_cases h : ∃ t : ℝ≥0, 0 ≤ t ∧
      (hX.isSemimartingale hF).quadraticVariation hF t ω ∈ Ioi (s : ℝ)
  · rw [if_pos (hex.mpr h), if_pos h]
    congr 2
    ext t
    exact and_congr_right fun _ ↦ he t
  · rw [if_neg (fun h' ↦ h (hex.mp h')), if_neg h]

theorem IsContinuousLocalMartingale.inverse_quadraticVariation_timeChange
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Tendsto ((hX.isSemimartingale hF).quadraticVariation hF · ω) atTop atTop) :
    let A := (hX.isSemimartingale hF).continuousBracketClock hF
    let τ := clockInverseTime A
    ∃ hτ : ∀ s, IsStoppingTime F (τ s),
      (∀ᵐ ω ∂P, ∀ s, τ s ω ≠ ⊤) ∧
      HasContinuousPaths (fun s ↦ stoppedValue X (τ s)) P ∧
      Adapted (F.stoppingTimeReindex τ hτ (clockInverseTime_monotone A))
        (fun s ↦ stoppedValue X (τ s)) ∧
      Indistinguishable (fun t ω ↦ stoppedValue X (τ (A t ω)) ω) X P ∧
      Indistinguishable (fun s ↦ stoppedValue A (τ s)) (fun s _ ↦ s) P ∧
      ∀ t, IsStoppingTime (F.stoppingTimeReindex τ hτ (clockInverseTime_monotone A))
        (fun ω ↦ (A t ω : WithTop ℝ≥0)) := by
  let hS := hX.isSemimartingale hF
  let A := hS.continuousBracketClock hF
  have ha : Adapted F A := hS.adapted_continuousBracketClock hF
  have hc : HasContinuousPaths A P := Eventually.of_forall (hS.continuous_continuousBracketClock hF)
  have hm : HasMonotonePaths A P := Eventually.of_forall (hS.monotone_continuousBracketClock hF)
  have h0 : A 0 =ᵐ[P] 0 := Eventually.of_forall (hS.continuousBracketClock_zero hF)
  have hU : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t, s < A t ω :=
    hS.continuousBracketClock_unbounded_of_tendsto hF
      (hX.tendsto_continuousQuadraticVariation_of_raw hF hu)
  have hf := hX.ae_eq_of_continuousBracketClock_eq hF
  refine ⟨ha.isStoppingTime_clockInverseTime hF hc, clockInverseTime_finite_ae hU,
    hasContinuousPaths_stoppedValue_clockInverseTime hc hm h0 hU hX.2 hf,
    adapted_stoppedValue_clockInverseTime ha hF hc hX.2 hX.1.1,
    stoppedValue_clockInverseTime_comp_clock hc hm h0 hU hf,
    clockInverseTime_value hc hm h0 hU, ?_⟩
  exact isStoppingTime_clock_in_inverse_filtration ha hF
    (hS.continuous_continuousBracketClock hF) (hS.monotone_continuousBracketClock hF)
    (hS.continuousBracketClock_zero hF)

end ProbabilityTheory

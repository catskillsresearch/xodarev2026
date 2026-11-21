/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousClosingUpperTime
public import StochLean.Probability.Martingale.Convergence.Regularization
public import StochLean.Probability.Martingale.Potential.Basic
public import StochLean.Probability.Process.Path.RightContinuousOrder
public import StochLean.Probability.Process.Path.Subtraction
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The actual terminal potential of a bounded supermartingale

The full-half-line convergence theorem constructs the actual terminal variable.
Optional sampling proves that its conditional expectations lie below the process.
A cadlag martingale version therefore leaves a nonnegative potential. No finite
termination time, compensator, or continuous-time Doob--Meyer theorem is used.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X M : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} {N : ℝ}

theorem Supermartingale.exists_bounded_actualLimit
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ MemLp Z 2 P ∧ (∀ᵐ ω ∂P, ‖Z ω‖ ≤ N) ∧
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)) := by
  have hb (t : ℝ≥0) : (∫ ω, ‖X t ω‖ ∂P) ≤ ∫ _ : Ω, N ∂P :=
    integral_mono_ae (hX.integrable t).norm (integrable_const N)
      (hbound.mono fun _ hω ↦ hω t)
  obtain ⟨Z, hiZ, hl⟩ := hX.exists_integrable_limit_of_L1_bounded
    hc.hasRightContinuousPaths hb
  have hbZ : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ N := by
    filter_upwards [hl, hbound] with ω hlω hbω
    exact le_of_tendsto' hlω.norm hbω
  exact ⟨Z, hiZ, MemLp.of_bound hiZ.aestronglyMeasurable N hbZ, hbZ, hl⟩

/-- The lower-closing input is the deterministic bound, not the desired terminal
conditional expectation. The latter is obtained from actual-limit optional sampling. -/
theorem Supermartingale.condExp_actualLimit_le_of_uniform_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) (t : ℝ≥0) :
    P[Z | F t] ≤ᵐ[P] X t := by
  have hlower (s : ℝ≥0) : P[(fun _ : Ω ↦ -N) | F s] ≤ᵐ[P] X s := by
    rw [condExp_const (F.le s)]
    filter_upwards [hbound] with ω hω
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hω s)).1
  have htop : IsStoppingTime F (fun _ : Ω ↦ (⊤ : WithTop ℝ≥0)) :=
    fun _ ↦ by simp
  have h := hX.condExp_actualLimit_stoppedValue_le_of_bounded_lower_time
    hF hc.hasRightContinuousPaths (integrable_const (-N)) hlower hl
    (isStoppingTime_const F t) htop (fun _ ↦ le_top) (fun _ ↦ le_rfl)
  simpa only [stoppedValueWithTerminal_top, IsStoppingTime.measurableSpace_const,
    stoppedValue_const] using h

/-- Any martingale below the process bounds every future conditional decrement.
This is a fixed-pair AE assertion, not an uncountable intersection of null sets. -/
theorem Supermartingale.conditional_increment_le_sub_martingale
    (hX : Supermartingale X F P) (hM : Martingale M F P)
    (hle : ∀ t, M t ≤ᵐ[P] X t) {t u : ℝ≥0} (htu : t ≤ u) :
    P[X t - X u | F t] ≤ᵐ[P] X t - M t := by
  have hCE := condExp_mono (m := F t) (hM.integrable u) (hX.integrable u) (hle u)
  have hsub := condExp_sub (hX.integrable t) (hX.integrable u) (F t)
  rw [condExp_of_stronglyMeasurable (F.le t) (hX.stronglyAdapted t)
    (hX.integrable t)] at hsub
  filter_upwards [hCE, hM.condExp_ae_eq htu, hsub] with ω hω heω hsω
  simpa only [hsω, Pi.sub_apply, heω] using sub_le_sub_left hω (X t ω)

/-- A bounded cadlag supermartingale is its actual terminal conditional martingale
plus a bounded nonnegative potential. The potential's means vanish over all real
times, which in particular gives the integer-time tail required for localization. -/
theorem Supermartingale.exists_bounded_terminal_potential
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (_hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ (Z : Ω → ℝ) (M : ℝ≥0 → Ω → ℝ),
      Integrable Z P ∧ MemLp Z 2 P ∧ (∀ᵐ ω ∂P, ‖Z ω‖ ≤ N) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Martingale M F P ∧ HasCadlagPaths M P ∧ (∀ t, M t =ᵐ[P] P[Z | F t]) ∧
      IsPotential (X - M) F P ∧ HasCadlagPaths (X - M) P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ (X - M) t ω ∧ (X - M) t ω ≤ 2 * N) ∧
      ∀ t u, t ≤ u → P[X t - X u | F t] ≤ᵐ[P] (X - M) t := by
  obtain ⟨Z, hiZ, hLZ, hbZ, hl⟩ := hX.exists_bounded_actualLimit hc hbound
  obtain ⟨M, hM, hcM, he, _⟩ := (martingale_condExp Z F P).exists_cadlag_modification hF
  have hclose (t : ℝ≥0) : M t =ᵐ[P] P[Z | F t] := (he t).symm
  have hle (t : ℝ≥0) : M t ≤ᵐ[P] X t :=
    (hclose t).trans_le (hX.condExp_actualLimit_le_of_uniform_bound hF hc hbound hl t)
  have hleAll : ∀ᵐ ω ∂P, ∀ t, M t ω ≤ X t ω :=
    hcM.hasRightContinuousPaths.ae_forall_le_of_forall_ae_le hc.hasRightContinuousPaths hle
  have hrNorm : HasRightContinuousPaths (fun t ω ↦ ‖M t ω‖) P :=
    hcM.hasRightContinuousPaths.mono fun _ hω t ↦ (hω t).norm
  have hrN : HasRightContinuousPaths (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ N) P :=
    Eventually.of_forall fun _ _ ↦ continuousWithinAt_const
  have hbM : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ N := by
    apply hrNorm.ae_forall_le_of_forall_ae_le hrN
    intro t
    filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := F t) hbZ, hclose t]
      with ω hbω heω
    simpa only [heω] using hbω
  have hbU : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (X - M) t ω ∧ (X - M) t ω ≤ 2 * N := by
    filter_upwards [hleAll, hbound, hbM] with ω hleω hbXω hbMω t
    have hx := abs_le.mp (by simpa only [Real.norm_eq_abs] using hbXω t)
    have hm := abs_le.mp (by simpa only [Real.norm_eq_abs] using hbMω t)
    change 0 ≤ X t ω - M t ω ∧ X t ω - M t ω ≤ 2 * N
    constructor
    · exact sub_nonneg.mpr (hleω t)
    · linarith only [hx.2, hm.1]
  have hmeanX : Tendsto (fun t : ℝ≥0 ↦ ∫ ω, X t ω ∂P) atTop (𝓝 (∫ ω, Z ω ∂P)) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ N)
      (Eventually.of_forall fun t ↦ (hX.integrable t).aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ hbound.mono fun _ hω ↦ hω t) (integrable_const N) hl
  have hmeanM (t : ℝ≥0) : (∫ ω, M t ω ∂P) = ∫ ω, Z ω ∂P :=
    (integral_congr_ae (hclose t)).trans (integral_condExp (F.le t))
  have hmeanU : Tendsto (fun t : ℝ≥0 ↦ ∫ ω, (X - M) t ω ∂P) atTop (𝓝 0) := by
    have h := hmeanX.sub_const (∫ ω, Z ω ∂P)
    simpa only [Pi.sub_apply, integral_sub (hX.integrable _) (hM.integrable _),
      hmeanM, sub_self] using h
  have hpot : IsPotential (X - M) F P :=
    ⟨hX.sub_martingale hM, fun t ↦ hbU.mono fun _ hω ↦ (hω t).1, hmeanU⟩
  exact ⟨Z, M, hiZ, hLZ, hbZ, hl, hM, hcM, hclose, hpot, hc.sub hcM, hbU,
    fun _ _ htu ↦ hX.conditional_increment_le_sub_martingale hM hle htu⟩

end MeasureTheory

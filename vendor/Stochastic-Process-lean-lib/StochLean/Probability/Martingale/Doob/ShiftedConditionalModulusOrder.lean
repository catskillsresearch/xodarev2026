/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalModulus
public import StochLean.Probability.Process.Path.RightContinuousOrder
public import StochLean.Probability.Process.Path.RightContinuousSupremum
public import Mathlib.Probability.Martingale.Basic

/-! # Order of actual shifted conditional projections and signed moduli

For a supermartingale, later future conditional projections are smaller.
Right-continuous versions inherit this order on a common full-measure event.
The actual conditional increment modulus on `[0,T]` is bounded by the existing
running supremum of `X - Qδ`, where `Qδ` represents `E[X(t+δ)|F_t]`.
The converse comparison needs horizon `T+δ`, since the sample at `T` uses
`X(T+δ)`. No unweighted jump-occurrence bound or TI hypothesis is used.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Q R : ℝ≥0 → Ω → ℝ} {δ η T : ℝ≥0}

private theorem Supermartingale.condExp_future_ae_le_of_le
    (hX : Supermartingale X F P) {s u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    P[X t | F s] ≤ᵐ[P] P[X u | F s] := by
  have hle := condExp_mono (m := F s) integrable_condExp (hX.integrable u)
    (hX.condExp_ae_le hut)
  have htower := condExp_condExp_of_le (μ := P) (F.mono hsu) (F.le u) (f := X t)
  exact htower.symm.trans_le hle

/-- Common-event width comparison of any right-continuous versions of the
actual future conditional projections. Increasing the width decreases them. -/
theorem Supermartingale.ae_forall_condExp_add_time_le_of_le
    (hX : Supermartingale X F P) (hδη : δ ≤ η)
    (hrQ : HasRightContinuousPaths Q P) (hrR : HasRightContinuousPaths R P)
    (heQ : ∀ t, Q t =ᵐ[P] P[X (t + δ) | F t])
    (heR : ∀ t, R t =ᵐ[P] P[X (t + η) | F t]) :
    ∀ᵐ ω ∂P, ∀ t, R t ω ≤ Q t ω := by
  apply hrR.ae_forall_le_of_forall_ae_le hrQ
  intro t
  exact (heR t).trans_le
    ((hX.condExp_future_ae_le_of_le (le_add_of_nonneg_right (show 0 ≤ δ from bot_le))
      (add_le_add le_rfl hδη)).trans_eq (heQ t).symm)

/-- The version-safe source modulus is bounded by the actual signed
projection residual's running supremum on the same compact horizon. -/
theorem Supermartingale.ae_conditionalIncrementModulus_le_denseRunningSupremum
    (hX : Supermartingale X F P) (hrX : HasRightContinuousPaths X P)
    (hrQ : HasRightContinuousPaths Q P)
    (heQ : ∀ t, Q t =ᵐ[P] P[X (t + δ) | F t])
    {W : Ω → ℝ≥0∞} (hW : IsConditionalIncrementModulus F P X T δ W) :
    W ≤ᵐ[P] denseRunningSupremum (X - Q) T := by
  apply hW.ae_le_of_bound
  intro t u htu huT huδ
  have hfuture := hX.condExp_future_ae_le_of_le htu huδ
  have hsub := condExp_sub (m := F t) (hX.integrable t) (hX.integrable u)
  rw [condExp_of_stronglyMeasurable (F.le t) (hX.stronglyAdapted t)
    (hX.integrable t)] at hsub
  filter_upwards [hfuture, hsub, heQ t, hrX, hrQ] with ω hfutureω hsubω heω hrXω hrQω
  have hle : P[X t - X u | F t] ω ≤ (X - Q) t ω := by
    simp only [Pi.sub_apply] at hsubω ⊢
    rw [hsubω, heω]
    exact sub_le_sub_left hfutureω _
  exact (ENNReal.ofReal_le_ofReal hle).trans
    (ofReal_le_denseRunningSupremum_of_rightContinuous (htu.trans huT)
      (fun s ↦ (hrXω s).sub (hrQω s)))

/-- The reverse comparison needs the enlarged horizon `T+δ`; it cannot in
general use `T`, since the residual at the right endpoint samples `T+δ`. -/
theorem Supermartingale.ae_denseRunningSupremum_le_conditionalIncrementModulus
    (hX : Supermartingale X F P)
    (heQ : ∀ t, Q t =ᵐ[P] P[X (t + δ) | F t])
    {W : Ω → ℝ≥0∞} (hW : IsConditionalIncrementModulus F P X (T + δ) δ W) :
    denseRunningSupremum (X - Q) T ≤ᵐ[P] W := by
  have hpoint (t : ℝ≥0) (ht : t ≤ T) :
      (fun ω ↦ ENNReal.ofReal ((X - Q) t ω)) ≤ᵐ[P] W := by
    have hle := hW.conditional_increment_le
      (le_add_of_nonneg_right (show 0 ≤ δ from bot_le))
      (add_le_add ht le_rfl) le_rfl
    have hsub := condExp_sub (m := F t) (hX.integrable t) (hX.integrable (t + δ))
    rw [condExp_of_stronglyMeasurable (F.le t) (hX.stronglyAdapted t)
      (hX.integrable t)] at hsub
    filter_upwards [hle, hsub, heQ t] with ω hleω hsubω heω
    simpa only [hsubω, Pi.sub_apply, heω] using hleω
  have hdense := eventually_countable_forall.mpr
    (fun n ↦ hpoint (denseTimeUpTo T n) (min_le_left _ _))
  filter_upwards [hdense] with ω hω
  exact iSup_le hω

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.UpcrossingGlobalL1
public import StochLean.Analysis.PathVariation.DenseUpcrossingLimit
public import StochLean.Probability.Process.Path.RightContinuous
public import Mathlib.Probability.Martingale.Convergence

/-! # General L1-bounded half-line martingale convergence

Right-continuous submartingales and supermartingales with uniformly bounded
first moments have an actual integrable limit along all nonnegative times.
No uniform integrability, L1 convergence, closing identity, or second moment
is assumed or asserted. The full-time bridge excludes excursions between
integer observations by the independently proved dense upcrossing bound.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}

theorem Submartingale.exists_integrable_limit_of_L1_bounded
    (hX : Submartingale X F P) (hr : HasRightContinuousPaths X P)
    (hC : ∀ t, (∫ ω, ‖X t ω‖ ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      ∀ᵐ ω ∂P, Tendsto (fun t ↦ X t ω) atTop (𝓝 (Z ω)) := by
  let e (n : ℕ) : ℝ≥0 := n
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hN : Submartingale (fun n ↦ X (e n)) G P := hX.reindex e he
  have hb (n : ℕ) : eLpNorm (X (e n)) 1 P ≤ (Real.toNNReal C : ℝ≥0∞) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable (e n))]
    exact ENNReal.ofReal_le_ofReal (hC (e n))
  let Z := G.limitProcess (fun n ↦ X (e n)) P
  have hZ : Integrable Z P := memLp_one_iff_integrable.mp (hN.memLp_limitProcess hb)
  refine ⟨Z, hZ, ?_⟩
  filter_upwards [hr, hN.ae_tendsto_limitProcess hb,
    hX.ae_all_rat_denseUpcrossings_lt_top hC] with ω hrω hnω hfω
  exact tendsto_of_integer_limit_of_denseUpcrossings hrω hnω hfω

theorem Supermartingale.exists_integrable_limit_of_L1_bounded
    (hX : Supermartingale X F P) (hr : HasRightContinuousPaths X P)
    (hC : ∀ t, (∫ ω, ‖X t ω‖ ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      ∀ᵐ ω ∂P, Tendsto (fun t ↦ X t ω) atTop (𝓝 (Z ω)) := by
  have hrn : HasRightContinuousPaths (-X) P :=
    hr.mono fun _ hω t ↦ (hω t).neg
  have hCn : ∀ t, (∫ ω, ‖(-X) t ω‖ ∂P) ≤ C := by
    simpa only [Pi.neg_apply, norm_neg] using hC
  obtain ⟨Z, hZ, hl⟩ := hX.neg.exists_integrable_limit_of_L1_bounded hrn hCn
  refine ⟨-Z, hZ.neg, ?_⟩
  filter_upwards [hl] with ω hω
  simpa only [Pi.neg_apply, neg_neg] using hω.neg

theorem Martingale.exists_integrable_limit_of_L1_bounded
    (hX : Martingale X F P) (hr : HasRightContinuousPaths X P)
    (hC : ∀ t, (∫ ω, ‖X t ω‖ ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      ∀ᵐ ω ∂P, Tendsto (fun t ↦ X t ω) atTop (𝓝 (Z ω)) :=
  hX.submartingale.exists_integrable_limit_of_L1_bounded hr hC

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.DiscreteOneSided
public import StochLean.ForMathlib.MeasureTheory.ConditionalLowerBound

/-! # Signed weak maximal bounds for discrete one-sided martingales

The first absolute-level hitting time is bounded. Its first moment is controlled
by the initial expectation and the terminal first moment, using optional sampling
and conditional L1 contraction. No positivity or square-integrability is assumed.
-/

@[expose] public section

open Finset Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem Supermartingale.integral_norm_stoppedValue_le_endpoints
    (hX : Supermartingale X F P) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime F τ)
    {N : ℕ} (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, ‖stoppedValue X τ ω‖ ∂P) ≤
      (∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X N ω‖ ∂P) := by
  have hi := integrable_stoppedValue ℕ hτ hX.integrable hb
  have hl := hX.condExp_stoppedValue_ae_le_of_le hτ (isStoppingTime_const F N)
    hb (fun _ ↦ le_rfl)
  rw [stoppedValue_const] at hl
  have hu := hX.condExp_stoppedValue_ae_le_of_le (isStoppingTime_const F 0) hτ
    (fun _ ↦ bot_le) hb
  rw [stoppedValue_const] at hu
  have he := integral_mono_ae integrable_condExp (hX.integrable 0) hu
  rw [integral_condExp (isStoppingTime_const F 0).measurableSpace_le] at he
  exact (hi.integral_norm_le_of_condExp_le hl).trans (add_le_add he le_rfl)

theorem Supermartingale.maximal_ineq_norm_discrete (hX : Supermartingale X F P)
    (N : ℕ) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ (range (N + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X k ω‖)} ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X N ω‖ ∂P)) := by
  let τ : Ω → WithTop ℕ := fun ω ↦
    (hittingBtwn (fun k ω ↦ ‖X k ω‖) {y : ℝ | ε ≤ y} 0 N ω : ℕ)
  have hτ : IsStoppingTime F τ :=
    hX.stronglyAdapted.norm.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hb (ω) : τ ω ≤ N := by
    change ((hittingBtwn (fun k ω ↦ ‖X k ω‖) {y : ℝ | ε ≤ y} 0 N ω : ℕ) :
      WithTop ℕ) ≤ (N : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr (hittingBtwn_le (u := fun k ω ↦ ‖X k ω‖)
      (s := {y : ℝ | ε ≤ y}) (n := 0) (m := N) ω)
  have hi := integrable_stoppedValue ℕ hτ hX.integrable hb
  let A := {ω | (ε : ℝ) ≤ (range (N + 1)).sup' nonempty_range_add_one
    (fun k ↦ ‖X k ω‖)}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ ↦
      ((hX.stronglyMeasurable n).measurable.mono (F.le n) le_rfl).norm)
  have hh (ω) (hω : ω ∈ A) : (ε : ℝ) ≤ ‖stoppedValue X τ ω‖ := by
    change (ε : ℝ) ≤ (range (N + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X k ω‖) at hω
    have hw : (ε : ℝ) ≤ stoppedValue (fun k ω ↦ ‖X k ω‖) τ ω := by
      apply stoppedValue_hittingBtwn_mem
      obtain ⟨k, hk, hv⟩ := (le_sup'_iff nonempty_range_add_one).mp hω
      exact ⟨k, ⟨Nat.zero_le _, Nat.le_of_lt_succ (mem_range.mp hk)⟩, hv⟩
    simpa only [stoppedValue, apply_ite, norm_zero] using hw
  have hs := setIntegral_ge_of_const_le_real hA (measure_ne_top P A) hh hi.norm.integrableOn
  have hbound := hX.integral_norm_stoppedValue_le_endpoints hτ hb
  have hpos : 0 ≤ (∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X N ω‖ ∂P) :=
    (integral_nonneg fun _ ↦ norm_nonneg _).trans hbound
  rw [ENNReal.le_ofReal_iff_toReal_le (by finiteness) hpos, ENNReal.toReal_mul]
  simp only [ENNReal.coe_toReal]
  exact hs.trans ((setIntegral_le_integral hi.norm
    (Eventually.of_forall fun _ ↦ norm_nonneg _)).trans hbound)

theorem Submartingale.maximal_ineq_norm_discrete (hX : Submartingale X F P)
    (N : ℕ) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ (range (N + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X k ω‖)} ≤
      ENNReal.ofReal (-(∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X N ω‖ ∂P)) := by
  simpa only [Pi.neg_apply, norm_neg, integral_neg] using
    hX.neg.maximal_ineq_norm_discrete N ε

end MeasureTheory

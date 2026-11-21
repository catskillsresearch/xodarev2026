/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Tails of raw extended lifetimes

The integer tail probabilities converge to the mass at infinity. They tend to
zero only when the lifetime is almost surely finite. The proof keeps the raw
extended time throughout; no default finite evaluation is used at infinity.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {τ : Ω → WithTop ℝ≥0}

theorem tendsto_measureReal_nat_lt_lifetime (hτ : Measurable τ) :
    Tendsto (fun n : ℕ ↦ P.real {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω})
      atTop (𝓝 (P.real {ω | τ ω = ⊤})) := by
  have hm (n : ℕ) : MeasurableSet {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω} :=
    measurableSet_lt measurable_const hτ
  have htop : MeasurableSet {ω | τ ω = ⊤} := measurableSet_eq_fun hτ measurable_const
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) ω)
      atTop (𝓝 ({ω | τ ω = ⊤}.indicator (fun _ ↦ (1 : ℝ)) ω)) := by
    filter_upwards with ω
    cases heτ : τ ω with
    | top =>
      have he (n : ℕ) :
          {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) ω = 1 :=
        indicator_of_mem (by
          change ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω
          rw [heτ]
          exact WithTop.coe_lt_top (n : ℝ≥0)) _
      simp only [he, indicator_of_mem (s := {ω | τ ω = ⊤}) heτ]
      exact tendsto_const_nhds
    | coe t =>
      have hnot : ω ∉ {ω | τ ω = ⊤} := by
        change τ ω ≠ ⊤
        rw [heτ]
        exact WithTop.coe_ne_top
      rw [indicator_of_notMem hnot]
      apply tendsto_const_nhds.congr'
      obtain ⟨N, hN⟩ := exists_nat_gt t
      filter_upwards [eventually_ge_atTop N] with n hn
      have htn : t ≤ (n : ℝ≥0) := hN.le.trans (Nat.cast_le.mpr hn)
      have hnτ : ¬ ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω := by
        rw [heτ]
        exact not_lt_of_ge (WithTop.coe_le_coe.mpr htn)
      exact (indicator_of_notMem hnτ (fun _ ↦ (1 : ℝ))).symm
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
    (fun n ↦ (measurable_const.indicator (hm n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n ↦ Eventually.of_forall fun ω ↦
      (norm_indicator_le_norm_self (fun _ : Ω ↦ (1 : ℝ)) ω).trans_eq (norm_one (α := ℝ))) hlim
  simpa only [integral_indicator (hm _), integral_indicator htop, integral_const,
    Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using hint

theorem tendsto_measureReal_nat_lt_lifetime_of_ae_ne_top
    (hτ : Measurable τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ P.real {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω}) atTop (𝓝 0) := by
  have hzero : P {ω | τ ω = ⊤} = 0 := by
    simpa only [ne_eq, not_not] using ae_iff.mp hfinite
  simpa only [Measure.real, hzero, ENNReal.toReal_zero] using
    tendsto_measureReal_nat_lt_lifetime (P := P) hτ

theorem IsStoppingTime.tendsto_measureReal_nat_lt_of_ae_ne_top
    {F : Filtration ℝ≥0 mΩ} (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ P.real {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω}) atTop (𝓝 0) :=
  tendsto_measureReal_nat_lt_lifetime_of_ae_ne_top
    (hτ.measurable.mono hτ.measurableSpace_le le_rfl) hfinite

end MeasureTheory

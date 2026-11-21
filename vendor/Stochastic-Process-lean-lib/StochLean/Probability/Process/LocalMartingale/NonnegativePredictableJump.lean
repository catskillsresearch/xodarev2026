/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale
public import StochLean.Probability.Process.Path.JumpSampling
public import StochLean.Probability.Process.Stopping.PredictableRestriction
public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpIntegrableTerminal

/-! # Nonnegative local-martingale jumps vanish at predictable times

The actual masked UI fundamental sequence makes the stopped jump genuinely
integrable. Its conditional mean is zero, and the source positive-time jump
condition makes it nonnegative. Hence each localized jump vanishes; the
original localizers tending to infinity then recover the original jump.

Restricting a predictable test to its positive-lifetime event removes only
its zero-time graph. At infinity the sampled jump has explicit terminal zero.
No global jump integrability, finite variation, initial moment, or finite
testing lifetime is assumed. This file proves only the predictable-test
conclusion, not a countable totally-inaccessible jump covering.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- A native local martingale with nonnegative positive-time jumps has zero
jump on the positive finite graph of every predictable stopping time. The
common event may depend on that testing stopping time. -/
theorem IsLocalMartingale.ae_jumpProcess_eq_zero_at_predictable_of_nonneg_jumps
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → 0 ≤ jumpProcess M t ω)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsPredictableStoppingTime F σ P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → σ ω = (t : WithTop ℝ≥0) →
      jumpProcess M t ω = 0 := by
  classical
  let τ := restrictedStoppingTime σ {ω | 0 < σ ω}
  have hτ : IsPredictableStoppingTime F τ P :=
    hσ.restrictedStoppingTime_before hF (hσ.1.measurable_before measurableSet_Ioi)
  have hpos (ω : Ω) : 0 < τ ω := by
    change 0 < restrictedStoppingTime σ {ω | 0 < σ ω} ω
    by_cases hp : 0 < σ ω
    · rw [restrictedStoppingTime_of_mem σ hp]
      exact hp
    · rw [restrictedStoppingTime_of_notMem σ hp]
      exact WithTop.coe_lt_top 0
  obtain ⟨ρ, hρ⟩ := hM.2.2
  let E (n : ℕ) : Set Ω := {ω | 0 < ρ n ω}
  let Y (n : ℕ) := MeasureTheory.stoppedProcess (fun t ↦ (E n).indicator (M t)) (ρ n)
  let J := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ
  let K (n : ℕ) := (E n).indicator ({ω | τ ω ≤ ρ n ω}.indicator J)
  have hJnonneg : 0 ≤ᵐ[P] J := by
    filter_upwards [hj] with ω hω
    change 0 ≤ stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ ω
    cases ht : τ ω with
    | top =>
      simpa only [stoppedValueWithTerminal_jump_eq_zero_of_top ht] using (le_refl (0 : ℝ))
    | coe t =>
      rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
      exact hω t (WithTop.coe_lt_coe.mp (ht ▸ hpos ω))
  have hKzero (n : ℕ) : K n =ᵐ[P] 0 := by
    have hcY : HasCadlagPaths (Y n) P := (hM.2.1.indicator (E n)).stoppedProcess (ρ n)
    obtain ⟨hi, hz⟩ :=
      (hρ.2.2 n).1.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
        (hρ.2.2 n).2 hF hcY hτ (Eventually.of_forall hpos)
    have he : stoppedValueWithTerminal (jumpProcess (Y n)) (fun _ ↦ (0 : ℝ)) τ =ᵐ[P]
        K n := hM.2.1.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess (E n) (ρ n) τ
    have hiK : Integrable (K n) P := hi.congr he
    have hCE : P[K n | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 :=
      (condExp_congr_ae he).symm.trans hz
    have hKnonneg : 0 ≤ᵐ[P] K n := by
      filter_upwards [hJnonneg] with ω hω
      simp only [K, Pi.zero_apply, indicator_apply]
      split_ifs <;> first | exact hω | exact le_rfl
    apply (integral_eq_zero_iff_of_nonneg_ae hKnonneg hiK).mp
    calc
      (∫ ω, K n ω ∂P) = ∫ ω, P[K n | hτ.1.measurableSpaceBefore] ω ∂P :=
        (integral_condExp hτ.1.measurableSpaceBefore_le_ambient).symm
      _ = 0 := by
        simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hCE
  have hall : ∀ᵐ ω ∂P, ∀ n, K n ω = 0 := by
    rw [ae_all_iff]
    exact hKzero
  filter_upwards [hall, hρ.1.tendsto_top] with ω hzero hlim t ht hσt
  have hpσ : 0 < σ ω := by
    rw [hσt]
    exact WithTop.coe_lt_coe.mpr ht
  have hτt : τ ω = (t : WithTop ℝ≥0) :=
    (restrictedStoppingTime_of_mem σ hpσ).trans hσt
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
  have hEω : ω ∈ E n := lt_of_le_of_lt bot_le hn
  have hcap : ω ∈ {ω | τ ω ≤ ρ n ω} := by
    change τ ω ≤ ρ n ω
    rw [hτt]
    exact hn.le
  have hJzero : J ω = 0 := by
    simpa only [K, indicator_of_mem hEω, indicator_of_mem hcap] using hzero n
  exact (stoppedValueWithTerminal_jump_eq_of_eq_coe hτt).symm.trans hJzero

/-- A local martingale has zero jump at a predictable stopping time when only
that sampled jump, rather than every positive-time jump of the process, is
known to be nonnegative.  This localized form is useful at a predictable
boundary selected from the path itself. -/
theorem IsLocalMartingale.ae_jumpProcess_eq_zero_at_predictable_of_sampled_nonneg
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsPredictableStoppingTime F σ P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → σ ω = (t : WithTop ℝ≥0) →
      0 ≤ jumpProcess M t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → σ ω = (t : WithTop ℝ≥0) →
      jumpProcess M t ω = 0 := by
  classical
  let τ := restrictedStoppingTime σ {ω | 0 < σ ω}
  have hτ : IsPredictableStoppingTime F τ P :=
    hσ.restrictedStoppingTime_before hF (hσ.1.measurable_before measurableSet_Ioi)
  have hpos (ω : Ω) : 0 < τ ω := by
    change 0 < restrictedStoppingTime σ {ω | 0 < σ ω} ω
    by_cases hp : 0 < σ ω
    · rw [restrictedStoppingTime_of_mem σ hp]
      exact hp
    · rw [restrictedStoppingTime_of_notMem σ hp]
      exact WithTop.coe_lt_top 0
  obtain ⟨ρ, hρ⟩ := hM.2.2
  let E (n : ℕ) : Set Ω := {ω | 0 < ρ n ω}
  let Y (n : ℕ) := MeasureTheory.stoppedProcess (fun t ↦ (E n).indicator (M t)) (ρ n)
  let J := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ
  let K (n : ℕ) := (E n).indicator ({ω | τ ω ≤ ρ n ω}.indicator J)
  have hJnonneg : 0 ≤ᵐ[P] J := by
    filter_upwards [hj] with ω hω
    change 0 ≤ stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ ω
    cases ht : τ ω with
    | top =>
      simpa only [stoppedValueWithTerminal_jump_eq_zero_of_top ht] using (le_refl (0 : ℝ))
    | coe t =>
      rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
      have hpσ : 0 < σ ω := by
        by_contra hn
        have hnot : ω ∉ {ω | 0 < σ ω} := hn
        have htop : τ ω = ⊤ := by
          exact restrictedStoppingTime_of_notMem σ hnot
        rw [htop] at ht
        exact WithTop.top_ne_coe ht
      have hτσ : τ ω = σ ω := restrictedStoppingTime_of_mem σ hpσ
      exact hω t (WithTop.coe_lt_coe.mp (ht ▸ hpos ω)) (hτσ ▸ ht)
  have hKzero (n : ℕ) : K n =ᵐ[P] 0 := by
    have hcY : HasCadlagPaths (Y n) P := (hM.2.1.indicator (E n)).stoppedProcess (ρ n)
    obtain ⟨hi, hz⟩ :=
      (hρ.2.2 n).1.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
        (hρ.2.2 n).2 hF hcY hτ (Eventually.of_forall hpos)
    have he : stoppedValueWithTerminal (jumpProcess (Y n)) (fun _ ↦ (0 : ℝ)) τ =ᵐ[P]
        K n := hM.2.1.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess (E n) (ρ n) τ
    have hiK : Integrable (K n) P := hi.congr he
    have hCE : P[K n | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 :=
      (condExp_congr_ae he).symm.trans hz
    have hKnonneg : 0 ≤ᵐ[P] K n := by
      filter_upwards [hJnonneg] with ω hω
      simp only [K, Pi.zero_apply, indicator_apply]
      split_ifs <;> first | exact hω | exact le_rfl
    apply (integral_eq_zero_iff_of_nonneg_ae hKnonneg hiK).mp
    calc
      (∫ ω, K n ω ∂P) = ∫ ω, P[K n | hτ.1.measurableSpaceBefore] ω ∂P :=
        (integral_condExp hτ.1.measurableSpaceBefore_le_ambient).symm
      _ = 0 := by
        simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hCE
  have hall : ∀ᵐ ω ∂P, ∀ n, K n ω = 0 := by
    rw [ae_all_iff]
    exact hKzero
  filter_upwards [hall, hρ.1.tendsto_top] with ω hzero hlim t ht hσt
  have hpσ : 0 < σ ω := by
    rw [hσt]
    exact WithTop.coe_lt_coe.mpr ht
  have hτt : τ ω = (t : WithTop ℝ≥0) :=
    (restrictedStoppingTime_of_mem σ hpσ).trans hσt
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
  have hEω : ω ∈ E n := lt_of_le_of_lt bot_le hn
  have hcap : ω ∈ {ω | τ ω ≤ ρ n ω} := by
    change τ ω ≤ ρ n ω
    rw [hτt]
    exact hn.le
  have hJzero : J ω = 0 := by
    simpa only [K, indicator_of_mem hEω, indicator_of_mem hcap] using hzero n
  exact (stoppedValueWithTerminal_jump_eq_of_eq_coe hτt).symm.trans hJzero

end ProbabilityTheory

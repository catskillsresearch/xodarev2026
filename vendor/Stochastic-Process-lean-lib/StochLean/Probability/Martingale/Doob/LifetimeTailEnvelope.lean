/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalEnvelope
public import StochLean.Probability.Process.Stopping.FiniteLifetimeTail

/-! # Conditional martingale envelopes of lifetime tails

For each deterministic cutoff, the indicator that a raw stopping lifetime is
still ahead has an actual cadlag conditional martingale version between zero
and one. Its maximal probability estimate is independent of the time horizon.
Almost-sure finiteness is needed only to make these tail probabilities vanish
as the cutoff grows, not to construct an individual envelope.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

omit [IsFiniteMeasure P] in
theorem IsStoppingTime.integral_sq_indicator_gt (hτ : IsStoppingTime F τ) (T : ℝ≥0) :
    (∫ ω, ({ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) ω) ^ 2 ∂P) =
      P.real {ω | (T : WithTop ℝ≥0) < τ ω} := by
  have hA : MeasurableSet {ω | (T : WithTop ℝ≥0) < τ ω} :=
    F.le T _ (hτ.measurableSet_gt T)
  have he : (fun ω ↦ ({ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) ω) ^ 2) =
      {ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : (T : WithTop ℝ≥0) < τ ω
    · simp only [indicator_of_mem (s := {ω | (T : WithTop ℝ≥0) < τ ω}) hω, one_pow]
    · simp only [indicator_of_notMem (s := {ω | (T : WithTop ℝ≥0) < τ ω}) hω,
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [he, integral_indicator hA]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]

theorem Martingale.measureReal_lifetimeTailEnvelope_gt_le
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) (hr : HasRightContinuousPaths M P)
    (hτ : IsStoppingTime F τ) (T U : ℝ≥0)
    (he : ∀ t : ℝ≥0, M t =ᵐ[P]
      P[{ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) | F t])
    {a : ℝ} (ha : 0 < a) :
    P.real {ω | a < (denseRunningSupremum M U ω).toReal} ≤
      4 * P.real {ω | (T : WithTop ℝ≥0) < τ ω} / a ^ 2 := by
  have hA : MeasurableSet {ω | (T : WithTop ℝ≥0) < τ ω} :=
    F.le T _ (hτ.measurableSet_gt T)
  have hD : MemLp ({ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ))) 2 P :=
    (memLp_const (1 : ℝ)).indicator hA
  have hbound := hM.measureReal_toReal_denseRunningSupremum_condExp_gt_le hr hD he U ha
  rw [hτ.integral_sq_indicator_gt T] at hbound
  exact hbound

theorem IsStoppingTime.exists_cadlag_lifetimeTailEnvelope
    (hτ : IsStoppingTime F τ) (hF : F.IsUsual P) (T : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M F P ∧ HasCadlagPaths M P ∧
      (∀ t : ℝ≥0, M t =ᵐ[P]
        P[{ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) | F t]) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ M t ω ∧ M t ω ≤ 1) ∧
      ∀ U : ℝ≥0, (∀ᵐ ω ∂P, denseRunningSupremum M U ω ≠ ∞) ∧
        ∀ a : ℝ, 0 < a → P.real {ω | a < (denseRunningSupremum M U ω).toReal} ≤
          4 * P.real {ω | (T : WithTop ℝ≥0) < τ ω} / a ^ 2 := by
  let D := {ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ))
  have hA : MeasurableSet {ω | (T : WithTop ℝ≥0) < τ ω} :=
    F.le T _ (hτ.measurableSet_gt T)
  have hD : MemLp D 2 P := (memLp_const (1 : ℝ)).indicator hA
  have hD0 : 0 ≤ᵐ[P] D :=
    Eventually.of_forall fun ω ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) ω
  have hD1 : D ≤ᵐ[P] fun _ ↦ (1 : ℝ) := by
    filter_upwards with ω
    by_cases hω : (T : WithTop ℝ≥0) < τ ω
    · exact (indicator_of_mem (s := {ω | (T : WithTop ℝ≥0) < τ ω}) hω _).le
    · have he : D ω = 0 :=
        indicator_of_notMem (s := {ω | (T : WithTop ℝ≥0) < τ ω}) hω _
      rw [he]
      exact zero_le_one
  obtain ⟨M, hM, hcM, heM, hnonneg, _⟩ := exists_cadlag_conditionalEnvelope hF hD hD0
  have hupper : ∀ t : ℝ≥0, M t ≤ᵐ[P] fun _ ↦ (1 : ℝ) := fun t ↦
    (heM t).trans_le (condExp_le_nonneg_const (m := F t) zero_le_one hD1)
  have hu := hcM.hasRightContinuousPaths.ae_forall_le_of_forall_ae_le
    (Eventually.of_forall fun _ _ ↦ continuousWithinAt_const) hupper
  refine ⟨M, hM, hcM, heM, ?_, fun U ↦ ?_⟩
  · filter_upwards [hnonneg, hu] with ω hn hu t
    exact ⟨hn t, hu t⟩
  · exact ⟨hM.ae_denseRunningSupremum_condExp_ne_top hcM.hasRightContinuousPaths hD heM U,
      fun a ha ↦ hM.measureReal_lifetimeTailEnvelope_gt_le
        hcM.hasRightContinuousPaths hτ T U heM ha⟩

theorem IsStoppingTime.tendsto_measureReal_lifetimeTailEnvelope_sup
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    {M : ℕ → ℝ≥0 → Ω → ℝ} (hM : ∀ n, Martingale (M n) F P)
    (hr : ∀ n, HasRightContinuousPaths (M n) P)
    (he : ∀ n (t : ℝ≥0), M n t =ᵐ[P]
      P[{ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) | F t])
    (U : ℕ → ℝ≥0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n ↦ P.real {ω | a < (denseRunningSupremum (M n) (U n) ω).toReal})
      atTop (𝓝 0) := by
  have htail := hτ.tendsto_measureReal_nat_lt_of_ae_ne_top hfinite
  have hbound : Tendsto (fun n : ℕ ↦
      4 * P.real {ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω} / a ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (htail.const_mul 4).div_const (a ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ measureReal_nonneg)
    (fun n ↦ (hM n).measureReal_lifetimeTailEnvelope_gt_le (hr n) hτ n (U n) (he n) ha)

theorem IsStoppingTime.exists_cadlag_lifetimeTailEnvelopes_tendsto
    (hτ : IsStoppingTime F τ) (hF : F.IsUsual P) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∃ M : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, Martingale (M n) F P ∧ HasCadlagPaths (M n) P ∧
        (∀ t : ℝ≥0, M n t =ᵐ[P]
          P[{ω | ((n : ℝ≥0) : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) | F t]) ∧
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ M n t ω ∧ M n t ω ≤ 1) ∧
        ∀ U : ℝ≥0, ∀ᵐ ω ∂P, denseRunningSupremum (M n) U ω ≠ ∞) ∧
      ∀ U : ℕ → ℝ≥0, ∀ a : ℝ, 0 < a →
        Tendsto (fun n ↦ P.real {ω | a < (denseRunningSupremum (M n) (U n) ω).toReal})
          atTop (𝓝 0) := by
  choose M hm hc he hb hmax using fun n : ℕ ↦ hτ.exists_cadlag_lifetimeTailEnvelope hF n
  refine ⟨M, fun n ↦ ⟨hm n, hc n, he n, hb n, fun U ↦ (hmax n U).1⟩, fun U a ha ↦ ?_⟩
  exact hτ.tendsto_measureReal_lifetimeTailEnvelope_sup hfinite hm
    (fun n ↦ (hc n).hasRightContinuousPaths) he U ha

end MeasureTheory

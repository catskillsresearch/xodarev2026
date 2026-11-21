/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorMonotone
public import StochLean.Probability.Process.LocalMartingale.Congr

/-! # An actual everywhere-increasing predictable compensator

The proved increasing integrable-variation compensator initially has monotone
paths on one common full-measure event. The complement is measurable at time
zero by relative completeness. Multiplication by its predictable constant-in-
time zero-one mask gives an everywhere-cadlag, everywhere-monotone process.

Predictability is proved by this explicit predictable multiplication, not
inferred from an arbitrary indistinguishable modification. Actual integrable
variation, the true UI remainder, finite-time integrability and mean identity,
and uniqueness all transfer along the resulting common path equality.

The original source is not modified, and its initial random value need not
be zero. The mean identity retains the original initial expectation. This is
an existence strengthening of the existing compensator, not a new selector.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual unique increasing predictable integrable-variation compensator
can be chosen with cadlag and monotone paths everywhere, while retaining the
original UI remainder and all finite-time mean and uniqueness conclusions. -/
theorem HasIntegrableVariation.exists_unique_everywhere_monotone_predictable_compensator
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) (hmX : HasMonotonePaths X P) :
    ∃ B : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F B ∧
      (∀ ω, IsCadlagPath (B · ω) ∧ Monotone (B · ω)) ∧ B 0 = 0 ∧
      HasIntegrableVariation B P ∧ IsUIMartingale (X - B) F P ∧
      (∀ t, Integrable (B t) P ∧
        (∫ ω, B t ω ∂P) = (∫ ω, X t ω ∂P) - ∫ ω, X 0 ω ∂P) ∧
      ∀ A : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F A → HasFiniteVariationPaths A P →
        A 0 =ᵐ[P] 0 → IsLocalMartingale (X - A) F P → Indistinguishable B A P := by
  classical
  obtain ⟨A, hpA, hcA, hA0, hmA, hvA, huA, hmean, huniq⟩ :=
    hvX.exists_unique_monotone_predictable_compensator haX hF hcX hi0 hmX
  let bad := {ω | ¬ Monotone (A · ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hmA)
  let K : ℝ≥0 → Ω → ℝ := fun _ ω ↦ if ω ∈ bad then 0 else 1
  have haK : Adapted F K := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const measurable_const
  have hpK : IsStronglyPredictable F K :=
    haK.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  let B := A * K
  have hpB : IsStronglyPredictable F B := hpA.mul hpK
  have heAB : Indistinguishable A B P := by
    filter_upwards [hmA] with ω hω t
    have hb : ω ∉ bad := fun h ↦ h hω
    simp only [B, Pi.mul_apply, K, if_neg hb, mul_one]
  have hcBm (ω : Ω) : IsCadlagPath (B · ω) ∧ Monotone (B · ω) := by
    by_cases hb : ω ∈ bad
    · simp only [B, Pi.mul_apply, K, if_pos hb, mul_zero]
      exact ⟨IsContinuousPath.isCadlagPath continuous_const, monotone_const⟩
    · simpa only [B, Pi.mul_apply, K, if_neg hb, mul_one] using
        (show IsCadlagPath (A · ω) ∧ Monotone (A · ω) from ⟨hcA ω, not_not.mp hb⟩)
  have hB0 : B 0 = 0 := by
    funext ω
    change A 0 ω * K 0 ω = 0
    rw [congrFun hA0 ω, Pi.zero_apply, zero_mul]
  have heR : Indistinguishable (X - A) (X - B) P := by
    filter_upwards [heAB] with ω hω t
    change X t ω - A t ω = X t ω - B t ω
    rw [hω t]
  have huB : IsUIMartingale (X - B) F P :=
    huA.congr (haX.sub hpB.stronglyAdapted.adapted) heR
  refine ⟨B, hpB, hcBm, hB0, hvA.congr heAB, huB, ?_, ?_⟩
  · intro t
    exact ⟨(hmean t).1.congr (heAB.ae_eq t),
      (integral_congr_ae (heAB.ae_eq t).symm).trans (hmean t).2⟩
  · intro Z hpZ hvZ hZ0 hMZ
    exact heAB.symm.trans (huniq Z hpZ hvZ hZ0 hMZ)

end ProbabilityTheory

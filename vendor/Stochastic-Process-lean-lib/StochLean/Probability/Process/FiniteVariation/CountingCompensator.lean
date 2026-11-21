/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.BoundedJumpLocalization
public import StochLean.Probability.Process.FiniteVariation.CompensatorLocalMonotone

/-! # Actual compensators for increasing bounded-jump processes

Monotonicity gives finite variation on compact intervals. The proved actual
variation-exit construction upgrades this to locally integrable variation
when positive-time jumps are bounded. The existing local theorem then
constructs the unique increasing predictable compensator.

The second result is a unit-jump counting-domain consumer: the source takes
finite natural-number values at every finite time, has common monotone paths,
is right-continuous, and has real positive-time jump norm at most one. Real
cadlag paths are derived from these hypotheses. No Poisson law, independence,
finite expected count, or zero/integrable initial count is required.

This file does not introduce a counting-process predicate or claim to supply
all source definitions surrounding Protter III.22. Its hypotheses state the
counting domain directly, and its conclusion is actual compensator existence,
not a supplied candidate or an assumed local-integrable-variation certificate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- An adapted increasing cadlag process with bounded positive-time jumps
has an actual unique normalized increasing predictable compensator. The
original initial random value is retained in the local-martingale remainder. -/
theorem HasMonotonePaths.exists_unique_predictable_compensator_of_jump_bound
    (hm : HasMonotonePaths X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hC : 0 ≤ C)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C) :
    ∃ B : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F B ∧ (∀ ω, IsCadlagPath (B · ω)) ∧ B 0 = 0 ∧
      HasMonotonePaths B P ∧ HasLocallyIntegrableVariation B F P ∧
      IsLocalMartingale (X - B) F P ∧
      ∀ A : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F A → HasFiniteVariationPaths A P →
        A 0 =ᵐ[P] 0 → IsLocalMartingale (X - A) F P → Indistinguishable B A P := by
  have hv : HasLocallyIntegrableVariation X F P :=
    hm.hasFiniteVariationPaths.hasLocallyIntegrableVariation_of_jump_bound ha hF hc hC hj
  exact hv.exists_unique_monotone_predictable_compensator ha hF hc hm

/-- Actual compensator existence on the finite-valued, increasing,
right-continuous unit-jump counting domain. The real path has finite left
limits by monotonicity; no separate cadlag or variation assumption is needed. -/
theorem HasMonotonePaths.exists_unique_predictable_compensator_of_unit_jumps_nat
    {N : ℝ≥0 → Ω → ℕ} (hm : HasMonotonePaths N P) (ha : Adapted F N)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths N P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ‖jumpProcess (fun s v ↦ (N s v : ℝ)) t ω‖ ≤ 1) :
    ∃ B : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F B ∧ (∀ ω, IsCadlagPath (B · ω)) ∧ B 0 = 0 ∧
      HasMonotonePaths B P ∧ HasLocallyIntegrableVariation B F P ∧
      IsLocalMartingale ((fun t ω ↦ (N t ω : ℝ)) - B) F P ∧
      ∀ A : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F A → HasFiniteVariationPaths A P →
        A 0 =ᵐ[P] 0 → IsLocalMartingale ((fun t ω ↦ (N t ω : ℝ)) - A) F P →
          Indistinguishable B A P := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ)
  have haY : Adapted F Y := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  have hmY : HasMonotonePaths Y P := by
    filter_upwards [hm] with ω hω s t hst
    change (N s ω : ℝ) ≤ (N t ω : ℝ)
    exact_mod_cast hω hst
  have hcY : HasCadlagPaths Y P := by
    filter_upwards [hmY, hr] with ω hmω hrω
    refine ⟨fun t ↦ ?_, fun t _ ↦
      ⟨Function.leftLim (Y · ω) t, hmω.tendsto_leftLim t⟩⟩
    have hcast : Continuous (fun n : ℕ ↦ (n : ℝ)) := continuous_of_discreteTopology
    exact hcast.continuousAt.comp_continuousWithinAt (hrω t)
  exact hmY.exists_unique_predictable_compensator_of_jump_bound haY hF hcY zero_le_one hj

end ProbabilityTheory

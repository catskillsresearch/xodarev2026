/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.PredictableJumps
public import StochLean.Probability.Process.Stopping.PredictableCountableAvoidance
public import StochLean.Probability.Process.Stopping.PredictableJumpCoverage

/-! # Actual predictable coverage of finite-variation jumps

Predictable finite-variation paths cannot jump at totally inaccessible times.
The proof derives this from the actual unit-jump continuous compensator and
Stieltjes duality on countable predictable fibers. It does not assume a general
compensator, naturality, or a predictable jump cover. The previously proved
ordinary jump enumeration and stopping-time classification then construct the
countable predictable cover. Path assumptions may hold only almost surely.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}

/-- Positive-time jumps of the actual predictable FV input vanish at every
totally inaccessible stopping time, including times that may be infinite. -/
theorem IsStronglyPredictable.ae_jump_eq_zero_at_totallyInaccessibleStoppingTime
    (hX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsTotallyInaccessibleStoppingTime F τ P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → τ ω = (t : WithTop ℝ≥0) →
      jumpProcess X t ω = 0 := by
  obtain ⟨Y, hXY, hpY, hY⟩ :=
    hX.exists_cadlag_finiteVariation_indistinguishable_of_usual hF hc hv
  have hav := hτ.ae_avoids_predictable_countable_set hF
    (hpY.measurableSet_positive_jumpSupport (fun ω ↦ (hY ω).1))
    (fun ω ↦ countable_positive_jumpSupport_of_locallyBoundedVariation
      ω (hY ω).2 (hY ω).1)
  filter_upwards [hav, hXY.jumpProcess] with ω hω he t ht hτt
  by_contra hj
  apply hω t ht hτt
  exact ⟨ht, fun hzero ↦ hj ((he t).trans hzero)⟩

/-- Countably many actually constructed predictable stopping times cover
every positive nonzero FV jump on a single full-measure path event. They need
not be disjoint yet, and individual ordinary jump times need not be predictable. -/
theorem IsStronglyPredictable.exists_predictableStoppingTime_cover_jumps
    (hX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (σ n) P) ∧
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → jumpProcess X t ω ≠ 0 →
          ∃ n, σ n ω = (t : WithTop ℝ≥0) := by
  apply Adapted.exists_predictableStoppingTime_cover_jumps_of_no_totallyInaccessible_jumps
    hX.stronglyAdapted.adapted hF hc
  exact fun _ hτ ↦ hX.ae_jump_eq_zero_at_totallyInaccessibleStoppingTime hF hc hv hτ

end MeasureTheory

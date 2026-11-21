/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Compensator
public import StochLean.Probability.Process.Poisson.Moments
public import StochLean.Probability.Process.Path.LifetimeStepJump
public import StochLean.Probability.Process.Stopping.PredictableAfterCoefficient
public import Mathlib.Probability.Process.HittingTime

/-! # A deterministic one-jump counting regression

On any probability space the count which jumps once at time one is a
nonexplosive counting process. Its actual selected predictable compensator
is the real count itself, by canonical uniqueness after constructing the
predictable deterministic step. It is not Poisson at any constant rate:
the first moments at times one and two are incompatible with that law.

The original native arrival clocks are computed pointwise: the first is
one and every subsequent clock is infinite. Thus a terminating arrival
sequence is retained, rather than replaced by artificial finite values.
No special sample space, candidate compensator, or independence premise is
used, and no new counting process or arrival selector is defined.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

private theorem natCast_deterministicUnitJump :
    (fun t (_ : Ω) ↦ ((if (1 : ℝ≥0) ≤ t then 1 else 0 : ℕ) : ℝ)) =
      fun t (_ : Ω) ↦ if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0 := by
  funext t ω
  split_ifs <;> norm_num

/-- The finite natural-valued deterministic unit step satisfies the
counting predicate on every measure space, with all path statements exact. -/
theorem isNonexplosiveCountingProcess_deterministicUnitJump :
    IsNonexplosiveCountingProcess
      (fun t (_ : Ω) ↦ if (1 : ℝ≥0) ≤ t then 1 else 0) P := by
  refine ⟨fun _ ↦ aemeasurable_const, ?_, ?_, ?_, ?_⟩
  · exact Eventually.of_forall fun ω ↦ by
      change (if (1 : ℝ≥0) ≤ 0 then (1 : ℕ) else 0) = 0
      norm_num
  · exact Eventually.of_forall fun ω s t hst ↦ by
      by_cases hs : (1 : ℝ≥0) ≤ s
      · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
      · simp only [if_neg hs]
        split_ifs <;> norm_num
  · exact Eventually.of_forall fun _ ↦ (isCadlagPath_step_Ici (1 : ℝ≥0) (1 : ℕ)).1
  · rw [natCast_deterministicUnitJump]
    exact Eventually.of_forall fun ω t _ht ↦ by
      rw [jumpProcess_step_Ici]
      by_cases ht : (1 : ℝ≥0) = t <;> simp only [ht, if_true, if_false, or_true, true_or]

variable {F : Filtration ℝ≥0 mΩ}

/-- Actual counting-domain compensation returns the deterministic real
count itself, identified by the sole canonical compensator's uniqueness. -/
theorem predictableCompensator_deterministicUnitJump [IsProbabilityMeasure P]
    (hF : F.IsUsual P) :
    let N : ℝ≥0 → Ω → ℕ := fun t _ ↦ if (1 : ℝ≥0) ≤ t then 1 else 0
    let hN : IsNonexplosiveCountingProcess N P :=
      isNonexplosiveCountingProcess_deterministicUnitJump
    let ha : Adapted F N := fun _ ↦ measurable_const
    let hv := hN.hasLocallyIntegrableVariation_real ha hF
    Indistinguishable
      (hv.predictableCompensator ha.natCast_real hF hN.hasCadlagPaths_real)
      (fun t ω ↦ (N t ω : ℝ)) P := by
  let N : ℝ≥0 → Ω → ℕ := fun t _ ↦ if (1 : ℝ≥0) ≤ t then 1 else 0
  have hN : IsNonexplosiveCountingProcess N P :=
    isNonexplosiveCountingProcess_deterministicUnitJump
  have ha : Adapted F N := fun _ ↦ measurable_const
  have hv := hN.hasLocallyIntegrableVariation_real ha hF
  have hp : IsStronglyPredictable F (fun t ω ↦ (N t ω : ℝ)) := by
    have hτ := isPredictableStoppingTime_const F P (1 : ℝ≥0)
    have hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] (fun _ : Ω ↦ (1 : ℝ)) :=
      stronglyMeasurable_const
    have hstep := hK.isStronglyPredictable_indicator_stoppingTime_le hτ hF.complete_initial
    change IsStronglyPredictable F (fun (t : ℝ≥0) (ω : Ω) ↦
      {v : Ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator
        (fun _ : Ω ↦ (1 : ℝ)) ω) at hstep
    simpa only [N, natCast_deterministicUnitJump, indicator_apply, mem_ofPred_eq,
      WithTop.coe_le_coe] using hstep
  apply hv.predictableCompensator_unique ha.natCast_real hF hN.hasCadlagPaths_real hp
    hN.hasFiniteVariationPaths_real hN.initial_real
  have hzero : IsLocalMartingale (0 : ℝ≥0 → Ω → ℝ) F P :=
    (isContinuousLocalMartingale_const_initial
      (F := F) (P := P) (Z := fun _ : Ω ↦ (0 : ℝ)) measurable_const).1
  simpa only [sub_self] using hzero

/-- A single deterministic jump is not a Poisson process at any rate;
the contradiction uses the actual marginal means at two finite times. -/
theorem not_isPoissonProcess_deterministicUnitJump [IsProbabilityMeasure P] (rate : ℝ≥0) :
    ¬ IsPoissonProcess (fun t (_ : Ω) ↦ if (1 : ℝ≥0) ≤ t then 1 else 0) rate P := by
  intro hN
  have h1 := hN.integral_real 1
  have h2 := hN.integral_real 2
  norm_num at h1 h2
  linarith

/-- The original first arrival is one and all later original arrivals
are infinite, pointwise on the entire sample space. -/
theorem hittingAfter_deterministicUnitJump (n : ℕ) (ω : Ω) :
    hittingAfter (fun t (_ : Ω) ↦ if (1 : ℝ≥0) ≤ t then (1 : ℕ) else 0)
      (Ioi n) 0 ω = if n = 0 then (1 : WithTop ℝ≥0) else ⊤ := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl, hittingAfter_def]
    have hex : ∃ j : ℝ≥0, 0 ≤ j ∧ (if 1 ≤ j then (1 : ℕ) else 0) ∈ Ioi 0 :=
      ⟨1, bot_le, by norm_num⟩
    rw [if_pos hex]
    have hs : {i : ℝ≥0 | 0 ≤ i ∧ (if 1 ≤ i then (1 : ℕ) else 0) ∈ Ioi 0} = Ici 1 := by
      ext i
      by_cases hi : (1 : ℝ≥0) ≤ i <;> simp [hi]
    rw [hs, csInf_Ici]
    rfl
  · rw [if_neg hn]
    apply hittingAfter_eq_top_iff.mpr
    intro t _ht
    change ¬ n < (if (1 : ℝ≥0) ≤ t then (1 : ℕ) else 0)
    split_ifs <;> omega

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousBounded
public import StochLean.Probability.Martingale.Doob.ContinuousUniqueness

/-! # A nonzero continuous-compensator regression for the actual existence theorem

The decreasing deterministic ramp starts at one and reaches zero at time
one. Its compensator is the increasing ramp from zero to one. The test
invokes the actual dyadic existence theorem and only then identifies its
output with the explicit ramp using continuous finite-variation uniqueness.
Thus an explicit decomposition certificate is not substituted for existence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.ContinuousBoundedRegression

variable {Ω : Type*}

noncomputable def descendingRamp : ℝ≥0 → Ω → ℝ := fun t _ ↦ 1 - min (t : ℝ) 1

noncomputable def rampCompensator : ℝ≥0 → Ω → ℝ := fun t _ ↦ min (t : ℝ) 1

/-- Neither the source initial value nor its terminal compensator is zero. -/
theorem initial_and_terminal_values :
    (descendingRamp (Ω := Ω)) 0 = (fun _ ↦ 1) ∧
      (rampCompensator (Ω := Ω)) 0 = 0 ∧
      (rampCompensator (Ω := Ω)) 1 = (fun _ ↦ 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext ω <;> norm_num [descendingRamp, rampCompensator]

private theorem continuous_descendingRamp (ω : Ω) : Continuous (descendingRamp · ω) :=
  continuous_const.sub (NNReal.continuous_coe.min continuous_const)

private theorem continuous_rampCompensator (ω : Ω) : Continuous (rampCompensator · ω) :=
  NNReal.continuous_coe.min continuous_const

private theorem norm_descendingRamp_le_one (t : ℝ≥0) (ω : Ω) :
    ‖descendingRamp t ω‖ ≤ 1 := by
  change ‖1 - min (t : ℝ) 1‖ ≤ 1
  rw [Real.norm_of_nonneg (sub_nonneg.mpr (min_le_right _ _))]
  exact sub_le_self _ (le_min t.coe_nonneg zero_le_one)

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}

private theorem supermartingale_descendingRamp : Supermartingale descendingRamp F P := by
  refine ⟨fun _ ↦ stronglyMeasurable_const, ?_, fun _ ↦ integrable_const _⟩
  intro s t hst
  change P[(fun _ : Ω ↦ 1 - min (t : ℝ) 1) | F s] ≤ᵐ[P]
    (fun _ : Ω ↦ 1 - min (s : ℝ) 1)
  rw [condExp_const (F.le s)]
  exact Eventually.of_forall fun _ ↦
    sub_le_sub_left (min_le_min (NNReal.coe_le_coe.mpr hst) le_rfl) 1

omit [IsProbabilityMeasure P] in
private theorem monotone_rampCompensator : HasMonotonePaths rampCompensator P := by
  refine Eventually.of_forall fun _ s t hst ↦ ?_
  exact min_le_min (NNReal.coe_le_coe.mpr hst) le_rfl

private theorem martingale_ramp_sum : Martingale (descendingRamp + rampCompensator) F P := by
  convert martingale_const F P (1 : ℝ) using 1
  funext t ω
  change (1 - min (t : ℝ) 1) + min (t : ℝ) 1 = 1
  ring

/-- The genuinely constructed continuous compensator is the nonzero ramp.
Its convergence from the actual dyadic approximants is retained in the
conclusion, alongside its identification by the uniqueness theorem. -/
theorem exists_actual_compensator_identified (hF : F.IsUsual P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ Martingale (descendingRamp + A) F P ∧
      Indistinguishable A rampCompensator P ∧
      TendstoUCP P (dyadicDoobStep descendingRamp F P) atTop A := by
  have hX : Supermartingale descendingRamp F P := supermartingale_descendingRamp
  have hXc : HasContinuousPaths descendingRamp P :=
    Eventually.of_forall continuous_descendingRamp
  have hXcad : HasCadlagPaths descendingRamp P :=
    Eventually.of_forall fun ω ↦ IsContinuousPath.isCadlagPath (continuous_descendingRamp ω)
  have hb : ∀ᵐ ω ∂P, ∀ t, ‖descendingRamp t ω‖ ≤ 1 :=
    Eventually.of_forall fun ω t ↦ norm_descendingRamp_le_one t ω
  obtain ⟨A, _, hAa, hAp, hAc, hA0, hAm, hAv, _, _, hM, _, _, _, hUCP⟩ :=
    hX.exists_continuous_doob_decomposition_of_bound hF hXcad
      (hXc.hasTotallyInaccessibleJumps F) (by norm_num : (0 : ℝ) ≤ 1) hb
  have hR0 : (rampCompensator (Ω := Ω)) 0 = 0 := initial_and_terminal_values.2.1
  have he : Indistinguishable A rampCompensator P :=
    indistinguishable_of_continuous_finiteVariation_martingale_add_zero hF
      hM martingale_ramp_sum (Eventually.of_forall hAc)
      (Eventually.of_forall continuous_rampCompensator)
      hAv monotone_rampCompensator.hasFiniteVariationPaths
      (Eventually.of_forall fun ω ↦ congrFun hA0 ω)
      (Eventually.of_forall fun ω ↦ congrFun hR0 ω)
  exact ⟨A, hAa, hAp, hAc, hA0, hAm, hM, he, hUCP⟩

end ProbabilityTheory.ContinuousBoundedRegression

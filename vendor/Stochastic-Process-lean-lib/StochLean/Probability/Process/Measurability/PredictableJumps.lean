/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.Predictable
public import StochLean.Probability.Process.FiniteVariation.Stieltjes
public import StochLean.Analysis.PathVariation.VariationJumpSeries

/-! # Predictable jump supports and everywhere-good FV versions

The positive-time jump support of a predictable cadlag process is predictable.
Local finite variation makes its time fibers countable. A usual initial-null
reset preserves actual predictability while making both path assumptions hold
everywhere; it does not claim predictability of arbitrary exceptional paths.
-/

@[expose] public section

open ProbabilityTheory StochLean MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- The source jump process has predictable coordinates jointly in time and
sample when the actual input is predictable and every path is cadlag. -/
theorem IsStronglyPredictable.jumpProcess_of_cadlag (hX : IsStronglyPredictable F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) : IsStronglyPredictable F (jumpProcess X) := by
  have hl := hX.stronglyAdapted.adapted.isStronglyPredictable_leftLimitProcess_of_cadlag hc
  exact hX.sub hl

/-- Zero time is excluded explicitly: the project's jump at zero is the
initial value, not a positive-time discontinuity. -/
theorem IsStronglyPredictable.measurableSet_positive_jumpSupport
    (hX : IsStronglyPredictable F X) (hc : ∀ ω, IsCadlagPath (X · ω)) :
    MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | 0 < p.1 ∧ jumpProcess X p.1 p.2 ≠ 0} := by
  have hp : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | 0 < p.1} := by
    simpa only [prod_univ, preimage, mem_Ioi] using
      (measurableSet_predictable_Ioi_prod (𝓕 := F) (i := 0) MeasurableSet.univ)
  exact hp.inter ((hX.jumpProcess_of_cadlag hc).measurable (measurableSet_singleton 0)).compl

/-- A single initial null event is removed by a predictable constant-in-time
mask. No new process selector or path-regularity owner is introduced. -/
theorem IsStronglyPredictable.exists_cadlag_finiteVariation_indistinguishable_of_usual
    (hX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyPredictable F Y ∧
      ∀ ω, IsCadlagPath (Y · ω) ∧ LocallyBoundedVariationOn (Y · ω) univ := by
  classical
  let bad := {ω | ¬ (IsCadlagPath (X · ω) ∧ LocallyBoundedVariationOn (X · ω) univ)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp (hc.and hv))
  let K : ℝ≥0 → Ω → ℝ := fun _ ω ↦ if ω ∈ bad then 0 else 1
  have haK : Adapted F K := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const measurable_const
  have hpK : IsStronglyPredictable F K :=
    haK.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  let Y : ℝ≥0 → Ω → ℝ := X * K
  refine ⟨Y, ?_, hX.mul hpK, ?_⟩
  · filter_upwards [hc, hv] with ω hcω hvω t
    have hb : ω ∉ bad := fun h ↦ h ⟨hcω, hvω⟩
    simp only [Y, Pi.mul_apply, K, if_neg hb, mul_one]
  · intro ω
    by_cases hb : ω ∈ bad
    · simp only [Y, Pi.mul_apply, K, if_pos hb, mul_zero]
      exact ⟨IsContinuousPath.isCadlagPath continuous_const,
        (monotone_const.monotoneOn univ).locallyBoundedVariationOn⟩
    · simpa only [Y, Pi.mul_apply, K, if_neg hb, mul_one] using
        (not_not.mp hb : IsCadlagPath (X · ω) ∧ LocallyBoundedVariationOn (X · ω) univ)

end MeasureTheory

namespace ProbabilityTheory

/-- Countability is proved from the actual path variation, independently of
any predictable enumeration or stopping-time section theorem. -/
theorem countable_positive_jumpSupport_of_locallyBoundedVariation
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} (ω : Ω)
    (hv : LocallyBoundedVariationOn (X · ω) univ) (hc : IsCadlagPath (X · ω)) :
    {t : ℝ≥0 | 0 < t ∧ jumpProcess X t ω ≠ 0}.Countable := by
  apply (countable_support_jump_of_locallyBoundedVariation hv hc.1).mono
  intro t ht
  simpa only [Function.mem_support, jumpProcess, Pi.sub_apply,
    leftLimitProcess, if_neg ht.1.ne'] using ht.2

end ProbabilityTheory

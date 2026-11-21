/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Jordan
public import StochLean.ForMathlib.MeasurableStieltjesNNReal
public import Mathlib.Probability.Kernel.Basic

/-! # Random Stieltjes measures of finite-variation processes

The three kernels are the deterministic canonical measures on each path. Their
restrictions through time `T` are measurable for the original `F T`, not merely
the ambient sigma-algebra. A common null-event reset supplies everywhere-good
versions from the almost-sure source assumptions under usual conditions.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  (X : ℝ≥0 → Ω → ℝ) (ha : Adapted F X)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

noncomputable def totalVariationKernel : Kernel Ω ℝ≥0 where
  toFun ω := (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure
  measurable' := measurable_stieltjesMeasure (fun t ↦
    (ha.totalVariationProcess_of_rightContinuous hr t).mono (F.le t) le_rfl)

noncomputable def positiveVariationKernel : Kernel Ω ℝ≥0 where
  toFun ω := (positiveVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure
  measurable' := measurable_stieltjesMeasure (fun t ↦
    (ha.positiveVariationProcess_of_rightContinuous hr t).mono (F.le t) le_rfl)

noncomputable def negativeVariationKernel : Kernel Ω ℝ≥0 where
  toFun ω := (negativeVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure
  measurable' := measurable_stieltjesMeasure (fun t ↦
    (ha.negativeVariationProcess_of_rightContinuous hr t).mono (F.le t) le_rfl)

theorem totalVariationKernel_eq_add :
    totalVariationKernel X ha hv hr =
      positiveVariationKernel X ha hv hr + negativeVariationKernel X ha hv hr := by
  ext1 ω
  exact totalVariationStieltjes_measure_eq_add _ _ _

theorem totalVariationKernel_Ioc {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    totalVariationKernel X ha hv hr ω (Ioc s t) = eVariationOn (fun u ↦ X u ω) (Icc s t) :=
  totalVariationStieltjes_measure_Ioc _ _ _ hst

theorem variationKernel_Ioc_sub {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    (positiveVariationKernel X ha hv hr ω (Ioc s t)).toReal -
      (negativeVariationKernel X ha hv hr ω (Ioc s t)).toReal = X t ω - X s ω :=
  variationStieltjes_measure_Ioc_sub _ _ _ hst

theorem measurable_totalVariationKernel_restrict (T : ℝ≥0) :
    Measurable[F T] (fun ω ↦ (totalVariationKernel X ha hv hr ω).restrict (Iic T)) := by
  let : MeasurableSpace Ω := F T
  exact measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T
    (fun t ht ↦ (ha.totalVariationProcess_of_rightContinuous hr t).mono (F.mono ht) le_rfl)

theorem measurable_positiveVariationKernel_restrict (T : ℝ≥0) :
    Measurable[F T] (fun ω ↦ (positiveVariationKernel X ha hv hr ω).restrict (Iic T)) := by
  let : MeasurableSpace Ω := F T
  exact measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T
    (fun t ht ↦ (ha.positiveVariationProcess_of_rightContinuous hr t).mono (F.mono ht) le_rfl)

theorem measurable_negativeVariationKernel_restrict (T : ℝ≥0) :
    Measurable[F T] (fun ω ↦ (negativeVariationKernel X ha hv hr ω).restrict (Iic T)) := by
  let : MeasurableSpace Ω := F T
  exact measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T
    (fun t ht ↦ (ha.negativeVariationProcess_of_rightContinuous hr t).mono (F.mono ht) le_rfl)

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

theorem Adapted.exists_cadlag_finiteVariation_indistinguishable_of_usual
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, IsCadlagPath (fun t ↦ Y t ω) ∧ LocallyBoundedVariationOn (fun t ↦ Y t ω) univ := by
  classical
  let bad := {ω | ¬ (IsCadlagPath (fun t ↦ X t ω) ∧
    LocallyBoundedVariationOn (fun t ↦ X t ω) univ)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp (hc.and hv))
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : StronglyAdapted F Y := fun t ↦
    StronglyMeasurable.ite (F.mono bot_le _ hbad) stronglyMeasurable_const (ha t).stronglyMeasurable
  have hY : ∀ ω, IsCadlagPath (fun t ↦ Y t ω) ∧
      LocallyBoundedVariationOn (fun t ↦ Y t ω) univ := by
    intro ω
    by_cases hb : ω ∈ bad
    · simp only [Y, if_pos hb]
      exact ⟨IsContinuousPath.isCadlagPath continuous_const,
        (monotone_const.monotoneOn univ).locallyBoundedVariationOn⟩
    · simpa only [Y, if_neg hb] using (not_not.mp hb : IsCadlagPath (fun t ↦ X t ω) ∧
        LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  refine ⟨Y, ?_, hYa.isStronglyProgressive_of_rightContinuous (fun ω ↦ (hY ω).1.1), hY⟩
  filter_upwards [hc, hv] with ω hcω hvω t
  exact (if_neg (show ω ∉ bad from fun hb ↦ hb ⟨hcω, hvω⟩)).symm

end MeasureTheory

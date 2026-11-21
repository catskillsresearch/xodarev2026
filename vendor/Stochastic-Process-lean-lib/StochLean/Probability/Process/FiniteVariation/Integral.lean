/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Stieltjes
public import StochLean.Analysis.PathVariation.StieltjesIntegral
public import StochLean.ForMathlib.MeasurableIntegralFiniteFibers

/-! # Pathwise finite-variation integrals

The definition uses the canonical pathwise Stieltjes integral, including the
separate initial term. Measurability does not assert integrability: as for the
Mathlib Bochner integral, values on nonintegrable inputs have the totalized
convention. Bounded Borel integrands on each finite interval are integrable.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter Function
open scoped NNReal ENNReal Topology

namespace StochLean

theorem stronglyMeasurable_stieltjesIntegral_Ioc_of_measurable_upTo
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Ω → StieltjesFunction ℝ≥0} (T : ℝ≥0)
    (hA : ∀ t ≤ T, Measurable fun ω ↦ A ω t)
    {f : Ω → ℝ≥0 → E} (hf : StronglyMeasurable (uncurry f)) :
    StronglyMeasurable fun ω ↦ ∫ u in Ioc 0 T, f ω u ∂(A ω).measure := by
  let κ : ProbabilityTheory.Kernel Ω ℝ≥0 :=
    ⟨fun ω ↦ (A ω).measure.restrict (Iic T),
      measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T hA⟩
  have heq (ω : Ω) : κ.restrict (measurableSet_Ioc (a := 0) (b := T)) ω =
      (A ω).measure.restrict (Ioc 0 T) := by
    change ((A ω).measure.restrict (Iic T)).restrict (Ioc 0 T) = _
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc 0 T ⊆ Iic T from fun _ hu ↦ hu.2)]
  have h := stronglyMeasurable_integral_kernel_of_finite_fibers
    (κ.restrict (measurableSet_Ioc (a := 0) (b := T)))
    (fun ω ↦ ⟨by rw [heq, Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩) hf
  simpa only [heq] using h

theorem stronglyMeasurable_stieltjesIntegral_Ioc {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Ω → StieltjesFunction ℝ≥0} (hA : ∀ t, Measurable fun ω ↦ A ω t)
    {f : Ω → ℝ≥0 → E} (hf : StronglyMeasurable (uncurry f)) (s t : ℝ≥0) :
    StronglyMeasurable fun ω ↦ ∫ u in Ioc s t, f ω u ∂(A ω).measure := by
  let κ : ProbabilityTheory.Kernel Ω ℝ≥0 := ⟨fun ω ↦ (A ω).measure, measurable_stieltjesMeasure hA⟩
  exact stronglyMeasurable_integral_kernel_of_finite_fibers
    (κ.restrict measurableSet_Ioc)
    (fun ω ↦ ⟨by change ((A ω).measure.restrict (Ioc s t)) univ < ∞
                 rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩) hf

end StochLean

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

noncomputable def finiteVariationIntegral (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathStieltjesIntegral (fun u ↦ X u ω) (hv ω) (hr ω) (fun u ↦ H u ω) t

@[simp] theorem finiteVariationIntegral_zero (H : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    finiteVariationIntegral X hv hr H 0 ω = H 0 ω * X 0 ω :=
  pathStieltjesIntegral_zero _

theorem finiteVariationIntegral_const (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    finiteVariationIntegral X hv hr (fun _ _ ↦ c) t ω = c * X t ω :=
  pathStieltjesIntegral_const c t

theorem norm_finiteVariationIntegral_le (H : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} {ω : Ω} {C : ℝ}
    (hC : ∀ u ∈ Icc 0 t, ‖H u ω‖ ≤ C) :
    ‖finiteVariationIntegral X hv hr H t ω‖ ≤ C * (|X 0 ω| + totalVariationProcess X t ω) :=
  norm_pathStieltjesIntegral_le hC

theorem measurable_finiteVariationIntegral {F : Filtration ℝ≥0 mΩ} (ha : Adapted F X)
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyMeasurable (uncurry H)) (T : ℝ≥0) :
    Measurable (finiteVariationIntegral X hv hr H T) := by
  have hf : StronglyMeasurable (uncurry (fun ω t ↦ H t ω)) := hH.comp_measurable measurable_swap
  have hp := stronglyMeasurable_stieltjesIntegral_Ioc
    (A := fun ω ↦ positiveVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω))
    (fun t ↦ (ha.positiveVariationProcess_of_rightContinuous hr t).mono (F.le t) le_rfl) hf 0 T
  have hn := stronglyMeasurable_stieltjesIntegral_Ioc
    (A := fun ω ↦ negativeVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω))
    (fun t ↦ (ha.negativeVariationProcess_of_rightContinuous hr t).mono (F.le t) le_rfl) hf 0 T
  have h0 : Measurable (fun ω ↦ H 0 ω * X 0 ω) :=
    (hH.of_uncurry_left.measurable).mul ((ha 0).mono (F.le 0) le_rfl)
  exact h0.add (hp.measurable.sub hn.measurable)

theorem adapted_finiteVariationIntegral {F : Filtration ℝ≥0 mΩ} (ha : Adapted F X)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyProgressive F H) :
    Adapted F (finiteVariationIntegral X hv hr H) := by
  intro T
  let : MeasurableSpace Ω := F T
  have hf : StronglyMeasurable (uncurry (fun ω t ↦ H (min t T) ω)) := by
    exact (hH T).comp_measurable
      (((measurable_snd.min measurable_const).subtype_mk
        (h := fun p : Ω × ℝ≥0 ↦ by
          change min p.2 T ≤ T
          exact min_le_right _ _)).prodMk measurable_fst)
  have hp := stronglyMeasurable_stieltjesIntegral_Ioc_of_measurable_upTo
    (A := fun ω ↦ positiveVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)) T
    (fun t ht ↦ (ha.positiveVariationProcess_of_rightContinuous hr t).mono (F.mono ht) le_rfl) hf
  have hn := stronglyMeasurable_stieltjesIntegral_Ioc_of_measurable_upTo
    (A := fun ω ↦ negativeVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)) T
    (fun t ht ↦ (ha.negativeVariationProcess_of_rightContinuous hr t).mono (F.mono ht) le_rfl) hf
  have h0 : Measurable (fun ω ↦ H 0 ω * X 0 ω) :=
    ((hH.stronglyAdapted 0).measurable.mono (F.mono bot_le) le_rfl).mul
      ((ha 0).mono (F.mono bot_le) le_rfl)
  have heq (ω : Ω) (A : StieltjesFunction ℝ≥0) :
      (∫ u in Ioc 0 T, H (min u T) ω ∂A.measure) = ∫ u in Ioc 0 T, H u ω ∂A.measure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [min_eq_left hu.2]
  have h := h0.add (hp.measurable.sub hn.measurable)
  simp only [heq] at h
  exact h

end ProbabilityTheory

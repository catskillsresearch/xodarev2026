/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LifetimeStepSeries
public import StochLean.Probability.Process.Stopping.PredictableAfterCoefficient
public import StochLean.ForMathlib.MeasureTheory.Function.SummableNorm
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Actual sums of integrable predictable lifetime steps

Summable first absolute moments give one common event of absolute coefficient
summability. On that event the actual closed-step series and its series of
absolute values converge uniformly on the whole half-line. Tonelli proves
finiteness of the extended coefficient sum before any real-valued `tsum` is
used as a convergent series or as an integrable bound.

Predictability is exact for the original `tsum` expression; the native theorem
for strongly measurable series also treats its exceptional nonsummability
set. Path regularity and finite variation are then established on the common
event of genuine convergence. No new process, compensator selector, or value
at infinite time is introduced. Lifetimes may coincide, be zero, or be infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {K : ℕ → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}

/-- A single common event supports genuine absolute summability and both
signed and absolute uniform convergence on the entire half-line. -/
theorem ae_summable_norm_tendstoUniformly_indicator_lifetime_le
    (τ : ℕ → Ω → WithTop ℝ≥0) (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    ∀ᵐ ω ∂P, Summable (fun n ↦ ‖K n ω‖) ∧
      TendstoUniformly
        (fun (N : ℕ) (t : ℝ≥0) ↦ ∑ n ∈ Finset.range N,
          {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω)
        (fun t : ℝ≥0 ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) atTop ∧
      TendstoUniformly
        (fun (N : ℕ) (t : ℝ≥0) ↦ ∑ n ∈ Finset.range N,
          ‖{ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω‖)
        (fun t : ℝ≥0 ↦ ∑' n, ‖{ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω‖) atTop := by
  classical
  filter_upwards [(ae_summable_norm_and_integrable_tsum_norm hi hs).1] with ω hω
  refine ⟨hω, ?_, ?_⟩
  · simpa only [indicator_apply, mem_ofPred_eq] using
      tendstoUniformly_tsum_indicator_lifetime_le (fun n ↦ τ n ω) hω
  · apply tendstoUniformly_tsum_nat hω
    intro n t
    simp only [norm_norm, indicator_apply, mem_ofPred_eq]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (K n ω)

/-- The actual lifetime-step series has cadlag paths on one common event;
the lifetimes need not be stopping times for this path statement. -/
theorem hasCadlagPaths_tsum_indicator_lifetime_le
    (τ : ℕ → Ω → WithTop ℝ≥0) (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    HasCadlagPaths
      (fun (t : ℝ≥0) ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) P := by
  classical
  filter_upwards [(ae_summable_norm_and_integrable_tsum_norm hi hs).1] with ω hω
  simpa only [indicator_apply, mem_ofPred_eq] using
    isCadlagPath_tsum_indicator_lifetime_le (fun n ↦ τ n ω) hω

variable {F : Filtration ℝ≥0 mΩ}

/-- Native measurability of a countable sum gives predictability of the
original `tsum`, without choosing a version on exceptional trajectories. -/
theorem isStronglyPredictable_tsum_indicator_stoppingTime_le
    (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n)) :
    IsStronglyPredictable F
      (fun t ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change StronglyMeasurable
    (fun p : ℝ≥0 × Ω ↦ ∑' n, {ω | τ n ω ≤ (p.1 : WithTop ℝ≥0)}.indicator (K n) p.2)
  exact StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ)
    (fun n ↦ (hK n).isStronglyPredictable_indicator_stoppingTime_le (hτ n) hc0)

private theorem ae_eVariationOn_tsum_indicator_lifetime_le
    (τ : ℕ → Ω → WithTop ℝ≥0) (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    ∀ᵐ ω ∂P, eVariationOn
      (fun t : ℝ≥0 ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) univ ≤
        ENNReal.ofReal (∑' n, ‖K n ω‖) := by
  classical
  filter_upwards [(ae_summable_norm_and_integrable_tsum_norm hi hs).1] with ω hω
  simpa only [indicator_apply, mem_ofPred_eq] using
    eVariationOn_univ_tsum_indicator_lifetime_le (fun n ↦ τ n ω) hω

/-- The actual predictable series has integrable whole-half-line variation.
Usual cadlag measurability supplies the original variation's measurability. -/
theorem hasIntegrableVariation_tsum_indicator_stoppingTime_le
    (hF : F.IsUsual P) (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n))
    (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    HasIntegrableVariation
      (fun t ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) P := by
  have hp := isStronglyPredictable_tsum_indicator_stoppingTime_le hτ hF.complete_initial hK
  have hc := hasCadlagPaths_tsum_indicator_lifetime_le τ hi hs
  have hm := hp.stronglyAdapted.adapted.measurable_eVariationOn_univ_of_usual hF hc
  have hb := ae_eVariationOn_tsum_indicator_lifetime_le τ hi hs
  constructor
  · exact hb.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  · apply (ae_summable_norm_and_integrable_tsum_norm hi hs).2.1.mono'
      hm.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hω).trans_eq
      (ENNReal.toReal_ofReal (tsum_nonneg fun n ↦ norm_nonneg (K n ω)))

/-- The first absolute moments bound expected actual total variation. No
finite-measure, disjoint-graph, or positive-lifetime hypothesis is needed. -/
theorem integral_eVariationOn_tsum_indicator_stoppingTime_le
    (hF : F.IsUsual P) (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n))
    (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    (∫ ω, (eVariationOn
      (fun t : ℝ≥0 ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) univ).toReal ∂P) ≤
        ∑' n, ∫ ω, ‖K n ω‖ ∂P := by
  rw [← (ae_summable_norm_and_integrable_tsum_norm hi hs).2.2]
  apply integral_mono_ae
    (hasIntegrableVariation_tsum_indicator_stoppingTime_le hF hτ hK hi hs).2
    (ae_summable_norm_and_integrable_tsum_norm hi hs).2.1
  filter_upwards [ae_eVariationOn_tsum_indicator_lifetime_le τ hi hs] with ω hω
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hω).trans_eq
    (ENNReal.toReal_ofReal (tsum_nonneg fun n ↦ norm_nonneg (K n ω)))

/-- Positive lifetimes give zero initial value on one common event. Infinite
lifetimes satisfy positivity but remain inactive. -/
theorem tsum_indicator_lifetime_le_zero_ae
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 < τ n ω) :
    (fun ω ↦ ∑' n, {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω) =ᵐ[P] 0 := by
  classical
  filter_upwards [ae_all_iff.mpr hpos] with ω hω
  have he (n : ℕ) :
      {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω = 0 := by
    have hnot : ω ∉ {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} := not_le.mpr (hω n)
    exact indicator_of_notMem hnot _
  simp only [he, tsum_zero, Pi.zero_apply]

end ProbabilityTheory

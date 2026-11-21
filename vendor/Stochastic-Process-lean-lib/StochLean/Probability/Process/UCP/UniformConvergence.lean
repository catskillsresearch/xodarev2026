/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! # Uniform path convergence and a subsequence criterion for UCP

Measurability of the output compact deviations is explicit in the converse.
No continuity of an outer measure on arbitrary decreasing sets is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem TendstoUCP.indistinguishable_unique {ι : Type*} {l : Filter ι}
    [l.NeBot] [l.IsCountablyGenerated] {X : ι → ℝ≥0 → Ω → ℝ} {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : TendstoUCP P X l Y) (hZ : TendstoUCP P X l Z)
    (hrY : HasRightContinuousPaths Y P) (hrZ : HasRightContinuousPaths Z P) :
    Indistinguishable Y Z P :=
  IsModification.indistinguishable_of_rightContinuous
    (fun t ↦ tendstoInMeasure_ae_unique (hY.fixedTime t) (hZ.fixedTime t)) hrY hrZ

theorem tendsto_compactDeviation_iff_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω} :
    Tendsto (fun i ↦ compactDeviation (X i) Y T ω) l (𝓝 0) ↔
      TendstoUniformlyOn (fun i t ↦ X i t ω) (fun t ↦ Y t ω) l (Icc 0 T) := by
  constructor
  · intro h
    apply EMetric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h.eventually_lt_const hε] with i hi
    intro t ht
    rw [edist_comm, edist_dist, dist_eq_norm_sub]
    exact (enorm_sub_le_compactDeviation ht.2 ω).trans_lt hi
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [EMetric.tendstoUniformlyOn_iff.mp h ε hε] with i hi
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have hh := (hi t ⟨bot_le, ht⟩).le
    simpa only [edist_dist, dist_eq_norm_sub, norm_sub_rev] using hh

theorem tendstoUCP_of_ae_compactDeviation [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, Measurable (compactDeviation (X n) Y T))
    (hXY : ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X n) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := P) (As := fun n ↦ {ω | ε ≤ compactDeviation (X n) Y T ω})
    atTop (A := ∅) MeasurableSet.empty
    (fun n ↦ measurableSet_le measurable_const (hm n T))
    (hXY.mono fun ω hω ↦ ((hω T).eventually_lt_const hε).mono fun n hn ↦ by
      exact iff_of_false (not_le_of_gt hn) (Set.notMem_empty ω))
  simpa only [measure_empty] using h

theorem tendstoUCP_of_subseq_ae_compactDeviation [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, Measurable (compactDeviation (X n) Y T))
    (hXY : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ k : ℕ → ℕ,
      ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X (ns (k n))) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨k, hk⟩ := hXY ns hns
  exact ⟨k, tendstoUCP_of_ae_compactDeviation (fun n T ↦ hm (ns (k n)) T) hk T ε hε⟩

theorem tendstoUCP_of_ae_compactDeviation_of_aemeasurable [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, AEMeasurable (compactDeviation (X n) Y T) P)
    (hXY : ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X n) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  let d (n : ℕ) := (hm n T).mk (compactDeviation (X n) Y T)
  have hd : ∀ᵐ ω ∂P, ∀ n, compactDeviation (X n) Y T ω = d n ω :=
    ae_all_iff.mpr (fun n ↦ (hm n T).ae_eq_mk)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ d n ω) atTop (𝓝 0) := by
    filter_upwards [hd, hXY] with ω hdω hω
    simpa only [hdω] using hω T
  have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := P) (As := fun n ↦ {ω | ε ≤ d n ω})
    atTop (A := ∅) MeasurableSet.empty
    (fun n ↦ measurableSet_le measurable_const (hm n T).measurable_mk)
    (hlim.mono fun ω hω ↦ (hω.eventually_lt_const hε).mono fun n hn ↦ by
      exact iff_of_false (not_le_of_gt hn) (Set.notMem_empty ω))
  have heq (n : ℕ) : P {ω | ε ≤ compactDeviation (X n) Y T ω} = P {ω | ε ≤ d n ω} := by
    apply measure_congr
    filter_upwards [hd] with ω hω
    change (ε ≤ compactDeviation (X n) Y T ω) = (ε ≤ d n ω)
    rw [hω]
  simpa only [heq, measure_empty] using h

theorem tendstoUCP_of_subseq_ae_compactDeviation_of_aemeasurable [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, AEMeasurable (compactDeviation (X n) Y T) P)
    (hXY : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ k : ℕ → ℕ,
      ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X (ns (k n))) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨k, hk⟩ := hXY ns hns
  exact ⟨k, tendstoUCP_of_ae_compactDeviation_of_aemeasurable
    (fun n T ↦ hm (ns (k n)) T) hk T ε hε⟩

end ProbabilityTheory

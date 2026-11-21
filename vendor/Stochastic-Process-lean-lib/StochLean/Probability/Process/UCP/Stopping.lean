/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.DeviationEvents
public import StochLean.Probability.Process.Stopping.IntegrandAE
public import StochLean.Probability.Process.Path.Stopping

/-! # Stopping and cutting off preserve UCP convergence

The event bounds hold for arbitrary possibly infinite random times, even without
a stopping-time hypothesis. The evaluation time of a stopped process is always finite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem TendstoUCP.stoppedProcess (h : TendstoUCP P X l Y) (τ : Ω → WithTop ℝ≥0) :
    TendstoUCP P (fun i ↦ stoppedProcess (X i) τ) l (stoppedProcess Y τ) := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoUCP_iff_measure_exists_norm_lt.mp h T ε hε) (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  cases hτ : τ ω with
  | top =>
    refine ⟨t, ht, ?_⟩
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe S =>
    refine ⟨min t S, (min_le_left _ _).trans ht, ?_⟩
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using hω

theorem TendstoUCP.cutoffIntegrand (h : TendstoUCP P X l Y) (τ : Ω → WithTop ℝ≥0) :
    TendstoUCP P (fun i ↦ cutoffIntegrand (X i) τ) l (cutoffIntegrand Y τ) := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoUCP_iff_measure_exists_norm_lt.mp h T ε hε) (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  by_cases hτ : (t : WithTop ℝ≥0) ≤ τ ω
  · exact ⟨t, ht, by simpa only [ProbabilityTheory.cutoffIntegrand, if_pos hτ] using hω⟩
  · simp only [ProbabilityTheory.cutoffIntegrand, if_neg hτ, sub_self, norm_zero] at hω
    exact (not_lt_of_ge hε.le hω).elim

end ProbabilityTheory

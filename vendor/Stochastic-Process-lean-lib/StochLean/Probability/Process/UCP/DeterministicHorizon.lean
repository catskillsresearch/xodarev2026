/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP

/-! # UCP convergence for deterministic horizons escaping to infinity

No path regularity or measurability is needed: on each fixed horizon the
processes agree everywhere eventually.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

theorem tendstoUCP_min_deterministic_horizon {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {l : Filter ι} {S : ι → ℝ≥0} (hS : Tendsto S l atTop)
    (X : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun i t ω ↦ X (min (S i) t) ω) l X := by
  intro T ε hε
  apply (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0)).congr'
  filter_upwards [hS.eventually (eventually_ge_atTop T)] with i hi
  have he (ω : Ω) : compactDeviation (fun t v ↦ X (min (S i) t) v) X T ω = 0 := by
    apply le_antisymm _ bot_le
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    simp only [min_eq_right (ht.trans hi), sub_self, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  simp only [he, not_le_of_gt hε, ofPred_false, measure_empty]

end ProbabilityTheory

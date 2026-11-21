/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP

/-! # Strict real-threshold event characterization of UCP

Strict exceedance events avoid assuming that a compact maximum is attained.
The comparison with the canonical extended compact deviation is order-theoretic;
it needs neither path regularity nor measurability of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ} {l : Filter ι}

theorem tendstoUCP_iff_measure_exists_norm_lt :
    TendstoUCP P X l Y ↔ ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun i ↦ P {ω | ∃ t ≤ T, ε < ‖X i t ω - Y t ω‖}) l (𝓝 0) := by
  constructor
  · intro h T ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h T (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)) (fun _ ↦ bot_le)
    intro i
    apply measure_mono
    rintro ω ⟨t, ht, hω⟩
    exact (ENNReal.ofReal_le_ofReal hω.le).trans (enorm_sub_le_compactDeviation ht ω)
  · intro h T ε hε
    obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have hr : 0 < (r : ℝ) := by exact_mod_cast hr0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h T r hr) (fun _ ↦ bot_le)
    intro i
    apply measure_mono
    intro ω hω
    have hlt : (r : ℝ≥0∞) < compactDeviation (X i) Y T ω := hrε.trans_le hω
    simp only [compactDeviation, lt_iSup_iff] at hlt
    obtain ⟨t, ht, htr⟩ := hlt
    refine ⟨t, ht, ?_⟩
    by_contra hn
    have hle := ENNReal.ofReal_le_ofReal (le_of_not_gt hn)
    exact (not_le_of_gt htr) (by simpa using hle)

end ProbabilityTheory

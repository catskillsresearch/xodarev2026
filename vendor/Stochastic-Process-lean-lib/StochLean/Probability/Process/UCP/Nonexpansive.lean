/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Nonexpansive scalar maps act continuously in UCP

The event comparison works for outer measures; no path measurability or
finite-measure premise is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem compactDeviation_comp_nonexpansive_le {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (T : ℝ≥0) (ω : Ω) :
    compactDeviation (fun t ω ↦ f (X t ω)) (fun t ω ↦ f (Y t ω)) T ω ≤
      compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hb : ‖f (X t ω) - f (Y t ω)‖ ≤ ‖X t ω - Y t ω‖ := by
    simpa only [dist_eq_norm_sub, NNReal.coe_one, one_mul] using hf.dist_le_mul (X t ω) (Y t ω)
  exact (ENNReal.ofReal_le_ofReal hb).trans (enorm_sub_le_compactDeviation ht ω)

theorem TendstoUCP.comp_nonexpansive {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    TendstoUCP P (fun n t ω ↦ f (Z n t ω)) l (fun t ω ↦ f (Y t ω)) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  intro ω hω
  exact hω.trans (compactDeviation_comp_nonexpansive_le hf T ω)

end ProbabilityTheory

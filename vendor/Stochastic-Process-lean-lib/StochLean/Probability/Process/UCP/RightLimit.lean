/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP
public import StochLean.Probability.Process.Path.RightLimit

/-! # Right-limit transformation is continuous in UCP on caglad paths

A slightly larger input horizon controls the right limit at the target horizon.
The transformation need not preserve the original initial value or give a
modification. Its continuity is proved by pathwise deviation comparison.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem compactDeviation_rightLimitProcess_le {ω : Ω}
    (hX : IsCagladPath (X · ω)) (hY : IsCagladPath (Y · ω)) (T : ℝ≥0) :
    compactDeviation (rightLimitProcess X) (rightLimitProcess Y) T ω ≤
      compactDeviation X Y (T + 1) ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hX.tendsto_rightLimitProcess t).sub (hY.tendsto_rightLimitProcess t)).norm)
  filter_upwards [(eventually_lt_nhds (ht.trans_lt (lt_add_one T))).filter_mono
    nhdsWithin_le_nhds] with u hu
  exact enorm_sub_le_compactDeviation hu.le ω

theorem TendstoUCP.rightLimitProcess_of_caglad {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) (hrZ : ∀ n, HasCagladPaths (Z n) P)
    (hrY : HasCagladPaths Y P) :
    TendstoUCP P (fun n ↦ rightLimitProcess (Z n)) l (rightLimitProcess Y) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu (T + 1) ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hrZ n, hrY] with ω hZ hY hω
  exact hω.trans (compactDeviation_rightLimitProcess_le hZ hY T)

end ProbabilityTheory

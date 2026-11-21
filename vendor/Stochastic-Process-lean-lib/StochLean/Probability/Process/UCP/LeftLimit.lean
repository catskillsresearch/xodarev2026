/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Source left limits are a UCP contraction on cadlag paths

The source left limit is zero at the lower endpoint. No measurable-version,
integrability or finite-measure assumption is needed for the event comparison.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem compactDeviation_leftLimitProcess_le {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (hY : IsCadlagPath (Y · ω)) (T : ℝ≥0) :
    compactDeviation (leftLimitProcess X) (leftLimitProcess Y) T ω ≤
      compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  by_cases ht0 : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, sub_self, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht0⟩
    apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hX.tendsto_leftLimitProcess ht0).sub (hY.tendsto_leftLimitProcess ht0)).norm)
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact enorm_sub_le_compactDeviation ((show u < t from hu).le.trans ht) ω

theorem TendstoUCP.leftLimitProcess_of_cadlag {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) (hrZ : ∀ n, HasCadlagPaths (Z n) P)
    (hrY : HasCadlagPaths Y P) :
    TendstoUCP P (fun n ↦ leftLimitProcess (Z n)) l (leftLimitProcess Y) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hrZ n, hrY] with ω hZ hY hω
  exact hω.trans (compactDeviation_leftLimitProcess_le hZ hY T)

end ProbabilityTheory

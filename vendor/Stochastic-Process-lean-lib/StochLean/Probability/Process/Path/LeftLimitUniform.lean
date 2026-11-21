/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.ForMathlib.Topology.UniformLimitValues
public import Mathlib.Topology.Order.DenselyOrdered

/-! # Uniform cadlag convergence passes to left limits and jumps

Time zero uses the source left-limit convention zero. Positive times use actual
strict-left limits; their convergence follows from uniform control, not pointwise
convergence alone.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {l : Filter ι}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0}

theorem tendsto_leftLimitProcess_of_uniformlyOn
    (hX : ∀ i, IsCadlagPath (X i · ω)) (hY : IsCadlagPath (Y · ω))
    (hu : TendstoUniformlyOn (fun i s ↦ X i s ω) (Y · ω) l (Icc 0 t)) :
    Tendsto (fun i ↦ leftLimitProcess (X i) t ω) l (𝓝 (leftLimitProcess Y t ω)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [leftLimitProcess_zero, Pi.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    have hq : 𝓝[<] t ≤ 𝓟 (Icc 0 t) := by
      apply le_principal_iff.mpr
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ⟨bot_le, hs.le⟩
    exact hu.tendsto_limit_values hq (fun i ↦ (hX i).tendsto_leftLimitProcess ht)
      (hY.tendsto_leftLimitProcess ht)

theorem tendsto_jumpProcess_of_uniformlyOn
    (hX : ∀ i, IsCadlagPath (X i · ω)) (hY : IsCadlagPath (Y · ω))
    (hu : TendstoUniformlyOn (fun i s ↦ X i s ω) (Y · ω) l (Icc 0 t)) :
    Tendsto (fun i ↦ jumpProcess (X i) t ω) l (𝓝 (jumpProcess Y t ω)) :=
  (hu.tendsto_at ⟨bot_le, le_rfl⟩).sub (tendsto_leftLimitProcess_of_uniformlyOn hX hY hu)

end ProbabilityTheory

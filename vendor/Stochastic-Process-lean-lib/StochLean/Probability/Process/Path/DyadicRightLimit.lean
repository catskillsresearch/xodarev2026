/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.DyadicSkeleton
public import StochLean.Probability.Process.Path.Cadlag
public import StochLean.ForMathlib.Topology.DenseRightLimitExtension
public import Mathlib.Topology.Order.IsLUB

/-! # Right-limit extension from the canonical dyadic skeleton

The native filter-limit selector is applied only to existing dyadic endpoints
strictly after the time. This is distinct from the full-time right-limit process
of an arbitrary unregularized input. The extension is cadlag when the skeleton
has finite one-sided limits, but need not be a modification of its input.
-/

@[expose] public section

open StochLean MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem dyadicSkeleton_right_neBot (t : ℝ≥0) :
    (nhdsWithin t (dyadicSkeleton ∩ Ioi t)).NeBot := by
  obtain ⟨e, _, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have ht : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  exact ht.neBot

theorem dyadicSkeleton_left_neBot {t : ℝ≥0} (ht : t ≠ 0) :
    (nhdsWithin t (dyadicSkeleton ∩ Iio t)).NeBot := by
  obtain ⟨e, _, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictMono_tendsto_of_lt
    (pos_iff_ne_zero.mpr ht)
  have he : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Iio t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1.2⟩⟩
  exact he.neBot

noncomputable def dyadicRightLimitProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (fun s ↦ X s ω)

theorem tendsto_dyadicRightLimitProcess {ω : Ω} {t : ℝ≥0}
    (h : ∃ z : ℝ, Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) :
    Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t))
      (𝓝 (dyadicRightLimitProcess X t ω)) := tendsto_nhds_limUnder h

theorem IsRightContinuousPath.dyadicRightLimitProcess_eq {ω : Ω}
    (hr : IsRightContinuousPath (X · ω)) (t : ℝ≥0) : dyadicRightLimitProcess X t ω = X t ω := by
  let := dyadicSkeleton_right_neBot t
  have hsub : dyadicSkeleton ∩ Ioi t ⊆ Ici t :=
    fun s hx ↦ show t ≤ s from le_of_lt hx.2
  apply Tendsto.limUnder_eq
  exact (hr t).tendsto.mono_left (nhdsWithin_mono t hsub)

theorem isCadlagPath_dyadicRightLimitProcess_of_limits {ω : Ω}
    (h : ∀ t : ℝ≥0,
      (∃ z : ℝ, Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) ∧
      (t ≠ 0 → ∃ z : ℝ,
        Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Iio t)) (𝓝 z))) :
    IsCadlagPath (dyadicRightLimitProcess X · ω) := by
  have hr (t) := tendsto_dyadicRightLimitProcess (h t).1
  refine ⟨continuousWithinAt_of_right_limits_on_subset dyadicSkeleton_right_neBot hr, ?_⟩
  intro t ht
  obtain ⟨z, hz⟩ := (h t).2 ht
  exact ⟨z, tendsto_right_limits_on_subset_from_left dyadicSkeleton_right_neBot hr hz⟩

theorem hasCadlagPaths_dyadicRightLimitProcess_of_limits
    (h : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∃ z : ℝ, Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) ∧
      (t ≠ 0 → ∃ z : ℝ,
        Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Iio t)) (𝓝 z))) :
    HasCadlagPaths (dyadicRightLimitProcess X) P :=
  h.mono fun _ hω ↦ isCadlagPath_dyadicRightLimitProcess_of_limits hω

theorem Indistinguishable.dyadicRightLimitProcess (hXY : Indistinguishable X Y P) :
    Indistinguishable (dyadicRightLimitProcess X) (dyadicRightLimitProcess Y) P := by
  filter_upwards [hXY] with ω hω t
  simp only [ProbabilityTheory.dyadicRightLimitProcess, hω]

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.RegularizationSequenceLimits
public import StochLean.ForMathlib.Topology.OneSidedSequenceLimits
public import StochLean.Probability.Process.Path.DyadicRightLimit

/-! # Simultaneous one-sided limits along the dyadic skeleton

Local boundedness and convergence of every monotone sample give actual filter
limits from both sides at every time, on one common event. This supplies the
pathwise input for regularization, without assuming right-continuous expectations.
The modification identity still needs that additional hypothesis.
-/

@[expose] public section

open StochLean MeasureTheory Filter Set
open scoped NNReal Topology

private theorem exists_dyadic_one_sided_limits_of_samples
    {x : ℝ≥0 → ℝ}
    (hb : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ∈ dyadicSkeleton, t ≤ T → ‖x t‖ ≤ C)
    (hl : ∀ e : ℕ → ℝ≥0, (Monotone e ∨ Antitone e) →
      (∀ n, e n ∈ dyadicSkeleton) → (∃ T : ℝ≥0, ∀ n, e n ≤ T) →
      ∃ z : ℝ, Tendsto (fun n ↦ x (e n)) atTop (𝓝 z)) (t : ℝ≥0) :
    (∃ z : ℝ, Tendsto x (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) ∧
      (t ≠ 0 → ∃ z : ℝ, Tendsto x (nhdsWithin t (dyadicSkeleton ∩ Iio t)) (𝓝 z)) := by
  constructor
  · obtain ⟨C, hC⟩ := hb (t + 1)
    apply exists_limit_nhdsWithin_Ioi_of_antitone_limits (lt_add_one t)
      (fun s hs _ hst ↦ hC s hs hst.le)
    intro e he hm
    exact hl e (Or.inr he) (fun n ↦ (hm n).2.2) ⟨t + 1, fun n ↦ (hm n).2.1.le⟩
  · intro ht
    obtain ⟨C, hC⟩ := hb t
    apply exists_limit_nhdsWithin_Iio_of_monotone_limits (pos_iff_ne_zero.mpr ht)
      (fun s hs hst _ ↦ hC s hs hst.le)
    intro e he hm
    exact hl e (Or.inl he) (fun n ↦ (hm n).2.2) ⟨t, fun n ↦ (hm n).1.le⟩

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.ae_exists_dyadic_one_sided_limits (hX : Supermartingale X F P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∃ z : ℝ, Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) ∧
      (t ≠ 0 → ∃ z : ℝ,
        Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Iio t)) (𝓝 z)) := by
  filter_upwards [hX.ae_locally_bounded_dyadicSkeleton,
    hX.ae_exists_limits_monotone_dyadic_samples] with ω hb hl
  exact exists_dyadic_one_sided_limits_of_samples hb hl

theorem Submartingale.ae_exists_dyadic_one_sided_limits (hX : Submartingale X F P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∃ z : ℝ, Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) (𝓝 z)) ∧
      (t ≠ 0 → ∃ z : ℝ,
        Tendsto (fun s ↦ X s ω) (nhdsWithin t (dyadicSkeleton ∩ Iio t)) (𝓝 z)) := by
  filter_upwards [hX.ae_locally_bounded_dyadicSkeleton,
    hX.ae_exists_limits_monotone_dyadic_samples] with ω hb hl
  exact exists_dyadic_one_sided_limits_of_samples hb hl

/-- Cadlag construction alone, before the modification identity is proved. -/
theorem Supermartingale.hasCadlagPaths_dyadicRightLimitProcess (hX : Supermartingale X F P) :
    ProbabilityTheory.HasCadlagPaths (ProbabilityTheory.dyadicRightLimitProcess X) P :=
  ProbabilityTheory.hasCadlagPaths_dyadicRightLimitProcess_of_limits
    hX.ae_exists_dyadic_one_sided_limits

theorem Submartingale.hasCadlagPaths_dyadicRightLimitProcess (hX : Submartingale X F P) :
    ProbabilityTheory.HasCadlagPaths (ProbabilityTheory.dyadicRightLimitProcess X) P :=
  ProbabilityTheory.hasCadlagPaths_dyadicRightLimitProcess_of_limits
    hX.ae_exists_dyadic_one_sided_limits

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.RegularizationSkeleton
public import StochLean.Analysis.PathVariation.DyadicSkeleton
public import StochLean.Analysis.PathVariation.DenseUpcrossingSampling

/-! # Simultaneous convergence along monotone dyadic samples

One common event of local skeleton boundedness and finite crossings works for
every bounded monotone or antitone sample sequence. The universal sequence
quantifier is inside the almost-sure event, not an uncountable intersection.
This establishes sequence limits but does not yet identify different sequences'
limits or construct a cadlag modification.
-/

@[expose] public section

open StochLean MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.ae_locally_bounded_dyadicSkeleton (hX : Supermartingale X F P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ∈ dyadicSkeleton, t ≤ T → ‖X t ω‖ ≤ C := by
  obtain ⟨e, he⟩ := dyadicSkeleton_countable.exists_eq_range ⟨0, zero_mem_dyadicSkeleton⟩
  filter_upwards [hX.ae_locally_bddAbove_norm_sample e] with ω hω T
  obtain ⟨C, hC⟩ := hω T
  refine ⟨C, fun t ht htT ↦ ?_⟩
  rw [he] at ht
  obtain ⟨n, rfl⟩ := ht
  exact hC n htT

theorem Submartingale.ae_locally_bounded_dyadicSkeleton (hX : Submartingale X F P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ∈ dyadicSkeleton, t ≤ T → ‖X t ω‖ ≤ C := by
  simpa only [Pi.neg_apply, norm_neg] using hX.neg.ae_locally_bounded_dyadicSkeleton

theorem Supermartingale.ae_exists_limits_monotone_dyadic_samples
    (hX : Supermartingale X F P) :
    ∀ᵐ ω ∂P, ∀ e : ℕ → ℝ≥0, (Monotone e ∨ Antitone e) →
      (∀ n, e n ∈ dyadicSkeleton) → (∃ T : ℝ≥0, ∀ n, e n ≤ T) →
      ∃ z : ℝ, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 z) := by
  filter_upwards [hX.ae_locally_bounded_dyadicSkeleton,
    hX.ae_all_rat_denseUpcrossings_neg_min_lt_top] with ω hb hu e he hmem hT
  obtain ⟨T, hT⟩ := hT
  obtain ⟨N, hN⟩ := exists_nat_ge T
  obtain ⟨C, hC⟩ := hb T
  have hbounded : BddAbove (Set.range fun n ↦ ‖X (e n) ω‖) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hC (e n) (hmem n) (hT n)
  have hm (n) := mem_dyadicSkeleton_iff.mp (hmem n)
  let Y : ℝ≥0 → Ω → ℝ := fun t ↦ X (min t (N : ℝ≥0))
  have heval (n) : Y (e n) ω = X (e n) ω := by
    dsimp only [Y]
    rw [min_eq_left ((hT n).trans hN)]
  have hY : BddAbove (Set.range fun n ↦ ‖Y (e n) ω‖) := by
    simpa only [heval] using hbounded
  rcases he with he | he
  · have hYn : BddAbove (Set.range fun n ↦ ‖-Y (e n) ω‖) := by
      simpa only [norm_neg] using hY
    obtain ⟨z, hz⟩ := exists_limit_monotone_dense_sample he hm hYn (hu N)
    refine ⟨-z, ?_⟩
    have hepoint (n) : X (min (e n) (N : ℝ≥0)) ω = X (e n) ω := heval n
    simpa only [hepoint, neg_neg] using hz.neg
  · obtain ⟨z, hz⟩ := exists_limit_antitone_dense_sample he hm hY (hu N)
    exact ⟨z, by simpa only [heval] using hz⟩

theorem Submartingale.ae_exists_limits_monotone_dyadic_samples
    (hX : Submartingale X F P) :
    ∀ᵐ ω ∂P, ∀ e : ℕ → ℝ≥0, (Monotone e ∨ Antitone e) →
      (∀ n, e n ∈ dyadicSkeleton) → (∃ T : ℝ≥0, ∀ n, e n ≤ T) →
      ∃ z : ℝ, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 z) := by
  filter_upwards [hX.neg.ae_exists_limits_monotone_dyadic_samples] with ω hω e he hm hb
  obtain ⟨z, hz⟩ := hω e he hm hb
  refine ⟨-z, ?_⟩
  simpa only [Pi.neg_apply, neg_neg] using hz.neg

end MeasureTheory

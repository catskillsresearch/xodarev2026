/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpSequence
public import StochLean.Probability.Process.Stopping.JumpCoefficients
public import StochLean.ForMathlib.Topology.Algebra.InfiniteSum.LifetimeReindex
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Actual large-jump sums through the existing lifetime enumeration

The canonical large-jump sequence escapes each finite horizon. Consequently
only finitely many of its closed steps are active by that horizon, and their
actual coefficient series is summable. Unique finite lifetimes and complete
large-jump coverage reindex this series as the literal positive-time jump sum.

An arbitrary real transformation is allowed at each jump. In particular, no
zero-preservation condition is imposed: the lifetime indicator remains outside
the transformation, so an infinite lifetime never contributes a finite-time
term, even when the transformation is nonzero at zero. Signed and norm sums
are the identity and norm specializations of the same result.

Adaptedness follows from the existing stopped-jump measurability and native
measurability of a countable sum. No new process, sum, or sampling owner is
introduced, and no integrability or jump-count moment is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

/-- Only finitely many indexed large-jump lifetimes are active at a finite
horizon. This is finiteness of the actual activation set, not only its support. -/
theorem IsCadlagPath.finite_largeJumpSequence_le (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (T : ℝ≥0) :
    {n : ℕ | largeJumpSequence X b n ω ≤ (T : WithTop ℝ≥0)}.Finite := by
  obtain ⟨N, hN⟩ := hX.exists_gt_largeJumpSequence hb T
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact (not_le_of_gt hN)
    ((monotone_largeJumpSequence X b ω (le_of_not_gt h)).trans hn)

/-- The original transformed stopped-jump closed-step series is genuinely
summable at each finite horizon, regardless of the value of the transform at zero. -/
theorem IsCadlagPath.summable_largeJumpSequence_indicator (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (φ : ℝ → ℝ) (T : ℝ≥0) :
    Summable (fun n : ℕ ↦ {v | largeJumpSequence X b n v ≤ (T : WithTop ℝ≥0)}.indicator
      (fun v ↦ φ (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
        (largeJumpSequence X b n) v)) ω) := by
  classical
  apply summable_of_hasFiniteSupport
  apply (hX.finite_largeJumpSequence_le hb T).subset
  intro n hn
  by_contra h
  exact hn (indicator_of_notMem
    (show ω ∉ {v | largeJumpSequence X b n v ≤ (T : WithTop ℝ≥0)} from h) _)

/-- The existing enumeration gives exactly the literal transformed sum of
all positive-time strict large jumps, with no repetition or omitted endpoint. -/
theorem IsCadlagPath.tsum_largeJumpSequence_indicator_eq_tsum_Ioc
    (hX : IsCadlagPath (X · ω)) (hb : 0 < b) (φ : ℝ → ℝ) (T : ℝ≥0) :
    (∑' n : ℕ, {v | largeJumpSequence X b n v ≤ (T : WithTop ℝ≥0)}.indicator
      (fun v ↦ φ (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
        (largeJumpSequence X b n) v)) ω) =
      ∑' s : Ioc 0 T, if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0 := by
  classical
  symm
  rw [tsum_subtype (Ioc 0 T)
    (fun s ↦ if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0)]
  apply StochLean.tsum_eq_tsum_of_disjoint_finite_lifetimes
    (τ := fun n ↦ largeJumpSequence X b n ω)
  · intro i j t hi hj
    have hjfin : largeJumpSequence X b j ω ≠ ⊤ := hj ▸ WithTop.coe_ne_top
    exact (hX.largeJumpSequence_eq_iff_of_ne_top hb hjfin).mp (hi.trans hj.symm)
  · intro i hi
    apply indicator_of_notMem
    change ¬ largeJumpSequence X b i ω ≤ (T : WithTop ℝ≥0)
    rw [hi]
    exact WithTop.not_top_le_coe T
  · intro i t hi
    have ht := hX.largeJumpSequence_mem_of_eq_coe hb hi
    simp only [indicator_apply, mem_ofPred_eq, mem_Ioc]
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe hi]
    simp only [hi, WithTop.coe_le_coe, ht.1, ht.2, true_and, if_true]
  · intro t ht
    have hmem : t ∈ Ioc 0 T := by
      by_contra h
      exact ht (indicator_of_notMem h _)
    have hj : b < ‖jumpProcess X t ω‖ := by
      by_contra h
      rw [indicator_of_mem hmem, if_neg h] at ht
      exact ht rfl
    exact hX.exists_largeJumpSequence_eq hb hmem.1 hj

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- The actual literal cumulative large-jump sum is strongly adapted for a
measurable real transform, using only the original stopping-time enumeration. -/
theorem Adapted.stronglyAdapted_tsum_Ioc_large_jumps_of_cadlag [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : Measurable φ) :
    StronglyAdapted F (fun (t : ℝ≥0) ω ↦
      ∑' s : Ioc 0 t, if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0) := by
  have hτ (n : ℕ) : IsStoppingTime F (largeJumpSequence X b n) :=
    ha.isStoppingTime_largeJumpSequence hc hb n
  have hm (n : ℕ) : StronglyMeasurable[(hτ n).measurableSpace]
      (fun ω ↦ φ (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
        (largeJumpSequence X b n) ω)) :=
    (hφ.comp (ha.stronglyMeasurable_stopped_jump hc (hτ n)).measurable).stronglyMeasurable
  intro T
  let : MeasurableSpace Ω := F T
  have he : (fun ω ↦ ∑' n : ℕ,
      {v | largeJumpSequence X b n v ≤ (T : WithTop ℝ≥0)}.indicator
        (fun v ↦ φ (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
          (largeJumpSequence X b n) v)) ω) =
      (fun ω ↦ ∑' s : Ioc 0 T,
        if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0) :=
    funext fun ω ↦ (hc ω).tsum_largeJumpSequence_indicator_eq_tsum_Ioc hb φ T
  change StronglyMeasurable[F T] (fun ω ↦ ∑' s : Ioc 0 T,
    if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0)
  rw [← he]
  exact StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ)
    (fun n ↦ (hm n).indicator_stoppingTime_le (hτ n) T)

end MeasureTheory

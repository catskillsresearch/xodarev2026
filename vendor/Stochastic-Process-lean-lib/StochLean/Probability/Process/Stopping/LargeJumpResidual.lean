/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpCoverage
public import StochLean.Probability.Process.Stopping.JumpCoefficients
public import StochLean.Probability.Process.Path.FiniteJumpRemoval
public import StochLean.Probability.Process.Path.CadlagWindowMoments

/-! # Actual finite-prefix large-jump residuals

The residual removes exactly the first `K` entries of the actual large-jump sequence.
At infinite entries the coefficient is explicitly zero. On the measurable coverage
event all its positive-time jumps on the horizon are small. Fixed-cap short-window
moments are derived from this event, whose complement tends to zero in probability.
No integrability of a random total jump count is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- Remove a deterministic finite prefix of the actual large-jump enumeration. -/
noncomputable def largeJumpResidual (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (K : ℕ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ X t ω -
  ∑ i ∈ Finset.range K, {v | largeJumpSequence X b i v ≤ (t : WithTop ℝ≥0)}.indicator
    (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
      (largeJumpSequence X b i)) ω

variable {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

theorem IsCadlagPath.isCadlag_largeJumpResidual (hX : IsCadlagPath (X · ω)) (b : ℝ) (K : ℕ) :
    IsCadlagPath (fun t ↦ largeJumpResidual X b K t ω) :=
  hX.sub_finset_lifetime_steps (Finset.range K) (largeJumpSequence X b)
    (fun i ↦ stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
      (largeJumpSequence X b i))

theorem IsCadlagPath.largeJumpResidual_initial (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (K : ℕ) : largeJumpResidual X b K 0 ω = X 0 ω := by
  classical
  have hz : ∀ i, ¬ largeJumpSequence X b i ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    intro i hi
    have he : largeJumpSequence X b i ω = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      le_antisymm hi bot_le
    exact lt_irrefl _ (hX.largeJumpSequence_mem_of_eq_coe hb he).1
  unfold largeJumpResidual
  have he : (∑ i ∈ Finset.range K,
      {v | largeJumpSequence X b i v ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
          (largeJumpSequence X b i)) ω) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ indicator_of_notMem
      (s := {v | largeJumpSequence X b i v ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}) (hz i) _
  rw [he, sub_zero]

theorem IsCadlagPath.norm_jump_largeJumpResidual_le_on_coverageEvent
    (hX : IsCadlagPath (X · ω)) (hb : 0 < b) {T : ℝ≥0} {K : ℕ}
    (hgood : ω ∈ largeJumpCoverageEvent X b T K) :
    ∀ t, 0 < t → t ≤ T → ‖jumpProcess (largeJumpResidual X b K) t ω‖ ≤ b := by
  apply hX.norm_jump_sub_finset_lifetime_steps_le (Finset.range K)
    (largeJumpSequence X b)
    (fun i ↦ stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
      (largeJumpSequence X b i)) T hb.le
  · exact fun _ _ _ ht ↦ stoppedValueWithTerminal_jump_eq_of_eq_coe ht
  · exact hX.largeJumpSequence_prefix_distinct hb K
  · exact hX.largeJumpSequence_prefix_covers_on_coverageEvent hb hgood

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

theorem Adapted.stronglyAdapted_largeJumpResidual [F.IsRightContinuous]
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (K : ℕ) :
    StronglyAdapted F (largeJumpResidual X b K) :=
  hX.stronglyAdapted_sub_finset_stopped_jumps hc (Finset.range K)
    (largeJumpSequence X b) (fun i _ ↦ hX.isStoppingTime_largeJumpSequence hc hb i)

/-- The actual residual satisfies the fixed-cap moment estimate on its proved
finite-prefix coverage event. The event and all coefficient measurability are derived. -/
theorem Adapted.eventually_integral_sq_largeJumpResidual_window_le
    {P : Measure Ω} [IsFiniteMeasure P] [F.IsRightContinuous]
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b)
    (T : ℝ≥0) (K : ℕ) {C : ℝ} (hC : 0 ≤ C)
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (∫ ω, (cappedDenseWindowOscillation (largeJumpResidual X b K) T (δ n) C ω) ^ 2 ∂P) ≤
        b ^ 2 * P.real (largeJumpCoverageEvent X b T K) +
          C ^ 2 * P.real (largeJumpCoverageEvent X b T K)ᶜ + ε := by
  have ha := hX.stronglyAdapted_largeJumpResidual hc hb K
  apply eventually_integral_sq_cappedDenseWindowOscillation_le
    (fun t ↦ (ha t).measurable.mono (F.le t) le_rfl)
    (Eventually.of_forall fun ω ↦ (hc ω).isCadlag_largeJumpResidual b K) T hC hb.le
    (F.le T _ (hX.measurableSet_largeJumpCoverageEvent hc hb T K))
    (Eventually.of_forall fun ω hω ↦ (hc ω).norm_jump_largeJumpResidual_le_on_coverageEvent hb hω)
    hδ hε

end MeasureTheory

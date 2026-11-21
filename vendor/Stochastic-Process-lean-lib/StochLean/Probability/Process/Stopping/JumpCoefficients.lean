/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AfterCoefficient
public import StochLean.Probability.Process.Measurability.Predictable

/-! # Actual jump coefficients at stopping times

Jump sampling uses `stoppedValueWithTerminal` with explicitly zero terminal
coefficient. A finite lifetime samples the actual source jump; infinity gives
zero and never invokes an arbitrary finite-time fallback.

The jump process of an adapted cadlag process is optional, as the difference
between an optional process and its predictable left limit. Its stopped jump
is measurable at the native stopped sigma-algebra and is revealed only at
and after that time. Common path bounds control an arbitrary family of these
coefficients on one common event, without intersecting uncountably many
coordinate exceptional events and without any jump-count moment assumption.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {N : ℝ}

theorem IsCadlagPath.norm_leftLimitProcess_le_of_bound (hX : IsCadlagPath (X · ω))
    (hb : ∀ t, ‖X t ω‖ ≤ N) (t : ℝ≥0) : ‖leftLimitProcess X t ω‖ ≤ N := by
  by_cases ht : t = 0
  · subst t
    simpa only [leftLimitProcess_zero, Pi.zero_apply, norm_zero] using
      (norm_nonneg (X 0 ω)).trans (hb 0)
  · let : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    exact le_of_tendsto (hX.tendsto_leftLimitProcess ht).norm (Eventually.of_forall hb)

/-- The source initial jump is included; its value is `X 0`, not zero. -/
theorem IsCadlagPath.norm_jumpProcess_le_of_bound (hX : IsCadlagPath (X · ω))
    (hb : ∀ t, ‖X t ω‖ ≤ N) (t : ℝ≥0) : ‖jumpProcess X t ω‖ ≤ 2 * N := by
  change ‖X t ω - leftLimitProcess X t ω‖ ≤ 2 * N
  have h := (norm_sub_le (X t ω) (leftLimitProcess X t ω)).trans
    (add_le_add (hb t) (hX.norm_leftLimitProcess_le_of_bound hb t))
  simpa only [two_mul] using h

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem HasCadlagPaths.ae_norm_jumpProcess_le_of_bound (hc : HasCadlagPaths X P)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∀ᵐ ω ∂P, ∀ t, ‖jumpProcess X t ω‖ ≤ 2 * N := by
  filter_upwards [hc, hb] with ω hω hbω
  exact hω.norm_jumpProcess_le_of_bound hbω

/-- Any family of explicitly zero-terminal stopped jumps has the same bound
on one path event; the family index need not be countable. -/
theorem HasCadlagPaths.ae_forall_norm_stopped_jump_le_of_bound {ι : Type*}
    (hc : HasCadlagPaths X P) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (τ : ι → Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i,
      ‖stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i) ω‖ ≤ 2 * N := by
  filter_upwards [hc.ae_norm_jumpProcess_le_of_bound hb, hb] with ω hj hbω i
  by_cases ht : τ i ω = ⊤
  · rw [stoppedValueWithTerminal_of_top ht, norm_zero]
    exact mul_nonneg (by norm_num) ((norm_nonneg (X 0 ω)).trans (hbω 0))
  · rw [stoppedValueWithTerminal_of_ne_top ht]
    exact hj (τ i ω).untopA

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem stoppedValueWithTerminal_jump_eq_of_eq_coe {ω : Ω} {t : ℝ≥0}
    (ht : τ ω = (t : WithTop ℝ≥0)) :
    stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω = jumpProcess X t ω := by
  have hne : τ ω ≠ ⊤ := ht ▸ WithTop.coe_ne_top
  rw [stoppedValueWithTerminal_of_ne_top hne]
  change jumpProcess X (τ ω).untopA ω = jumpProcess X t ω
  rw [ht]
  rfl

theorem stoppedValueWithTerminal_jump_eq_zero_of_top {ω : Ω} (ht : τ ω = ⊤) :
    stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω = 0 :=
  stoppedValueWithTerminal_of_top ht

theorem Adapted.isStronglyOptional_jumpProcess_of_cadlag (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) : IsStronglyOptional F (jumpProcess X) := by
  have ho : StronglyMeasurable[F.optional] (Function.uncurry X) :=
    hX.isStronglyOptional_of_cadlag hc
  have hl : StronglyMeasurable[F.optional] (Function.uncurry (leftLimitProcess X)) :=
    (hX.isStronglyPredictable_leftLimitProcess_of_cadlag hc).isStronglyOptional
  change StronglyMeasurable[F.optional]
    (fun p : ℝ≥0 × Ω ↦ X p.1 p.2 - leftLimitProcess X p.1 p.2)
  exact ho.sub hl

theorem Adapted.stronglyMeasurable_stopped_jump (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace]
      (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) :=
  (hX.isStronglyOptional_jumpProcess_of_cadlag hc).stronglyMeasurable_stoppedValueWithTerminal
    stronglyMeasurable_const hτ

theorem Adapted.isStronglyOptional_stopped_jump_step (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hτ : IsStoppingTime F τ) :
    IsStronglyOptional F (fun t : ℝ≥0 ↦
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ)) :=
  (hX.stronglyMeasurable_stopped_jump hc hτ).isStronglyOptional_indicator_stoppingTime_le hτ

/-- Finite removal of the actual stopped jumps preserves optionality, without
requiring the finite lifetimes to be distinct or requiring any moment. -/
theorem Adapted.isStronglyOptional_sub_finset_stopped_jumps {ι : Type*}
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i ∈ s, IsStoppingTime F (τ i)) :
    IsStronglyOptional F (fun t ω ↦ X t ω -
      ∑ i ∈ s, {ω | τ i ω ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i)) ω) := by
  have ho : StronglyMeasurable[F.optional] (Function.uncurry X) :=
    hX.isStronglyOptional_of_cadlag hc
  change StronglyMeasurable[F.optional] (fun p : ℝ≥0 × Ω ↦ X p.1 p.2 -
    ∑ i ∈ s, {ω | τ i ω ≤ (p.1 : WithTop ℝ≥0)}.indicator
      (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i)) p.2)
  apply ho.sub
  convert Finset.stronglyMeasurable_sum s (fun i hi ↦
    hX.isStronglyOptional_stopped_jump_step hc (hτ i hi)) using 1
  funext p
  simp only [Finset.sum_apply, Function.uncurry]

theorem Adapted.stronglyAdapted_sub_finset_stopped_jumps {ι : Type*}
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i ∈ s, IsStoppingTime F (τ i)) :
    StronglyAdapted F (fun t ω ↦ X t ω -
      ∑ i ∈ s, {ω | τ i ω ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i)) ω) :=
  (hX.isStronglyOptional_sub_finset_stopped_jumps hc s τ hτ).stronglyAdapted

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalJumpRemoval
public import StochLean.Probability.Process.Stopping.LargeJumpResidual

/-! # Conditional control by the actual finite large-jump residual

The residual is the existing finite prefix of the actual large-jump
enumeration, with explicitly zero coefficients at infinity. Its actual
fixed-cap dense-window envelope is measurable and square integrable. The
double-width path bridge proves clipped-residual domination, and the
original common path bound proves all coefficient bounds.

Thus the conditional estimate has no supplied residual-domination or jump
coefficient-bound premise. Small-window convergence is not assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

theorem IsCadlagPath.min_norm_largeJumpResidual_increment_le_capped_window
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (b : ℝ) (K : ℕ) (C : ℝ)
    {T δ t u : ℝ≥0} (hδ : 0 < δ) (htu : t ≤ u) (huT : u ≤ T) (huδ : u ≤ t + δ) :
    min C ‖largeJumpResidual X b K u ω - largeJumpResidual X b K t ω‖ ≤
      cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ) C ω := by
  exact min_le_min_left C (norm_sub_le_toReal_denseWindowOscillation_double_width
    (hX.isCadlag_largeJumpResidual b K) hδ htu huT huδ)

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- A fixed nonnegative cap makes the actual residual envelope square
integrable, without a moment assumption on the number of jumps. -/
theorem Adapted.memLp_capped_largeJumpResidual_window (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (T δ : ℝ≥0) (K : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    MemLp (cappedDenseWindowOscillation (largeJumpResidual X b K) T δ C) 2 P := by
  have ha := hX.stronglyAdapted_largeJumpResidual hc hb K
  have hm := measurable_cappedDenseWindowOscillation
    (fun t ↦ (ha t).measurable.mono (F.le t) le_rfl) T δ C
  apply MemLp.of_bound hm.aestronglyMeasurable C
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg
    (cappedDenseWindowOscillation_nonneg (largeJumpResidual X b K) T δ hC ω)]
  exact cappedDenseWindowOscillation_le_cap (largeJumpResidual X b K) T δ C ω

/-- Actual finite-prefix conditional bounds. The only supplied representatives
are the conditional expectation of the actual capped envelope and the actual
stopping-window probabilities at the fixed conditioning time. -/
theorem Adapted.condExp_increment_bounds_of_largeJumpResidual (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (T : ℝ≥0) (K : ℕ)
    {N : ℝ} (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {t u δ : ℝ≥0} (hδ : 0 < δ) (htu : t ≤ u) (huT : u ≤ T) (huδ : u ≤ t + δ)
    (M : Ω → ℝ) (R : ℕ → Ω → ℝ)
    (hM : M =ᵐ[P]
      P[cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ) (2 * N) | F t])
    (hR : ∀ i ∈ Finset.range K, R i =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < largeJumpSequence X b i ω ∧
          largeJumpSequence X b i ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) :
    ∀ᵐ ω ∂P,
      P[(fun v ↦ ‖X t v - X u v‖) | F t] ω ≤
          M ω + 2 * N * ∑ i ∈ Finset.range K, R i ω ∧
        ‖P[X t - X u | F t] ω‖ ≤ M ω + 2 * N * ∑ i ∈ Finset.range K, R i ω ∧
          P[X t - X u | F t] ω ≤ M ω + 2 * N * ∑ i ∈ Finset.range K, R i ω := by
  have hiX (r : ℝ≥0) : Integrable (X r) P := by
    have hp : MemLp (X r) 1 P := MemLp.of_bound
      ((hX r).mono (F.le r) le_rfl).aestronglyMeasurable N (hbound.mono fun _ hω ↦ hω r)
    exact hp.integrable le_rfl
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hiD := (hX.memLp_capped_largeJumpResidual_window (P := P) hc hb T (2 * δ) K hC).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcad : HasCadlagPaths X P := Eventually.of_forall hc
  have hcoeff := hcad.ae_forall_norm_stopped_jump_le_of_bound hbound (largeJumpSequence X b)
  apply condExp_increment_bounds_of_finite_jump_removal X (Finset.range K)
    (largeJumpSequence X b)
    (fun i ↦ stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
      (largeJumpSequence X b i))
    (cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ) (2 * N)) M R
    htu huδ hN (fun i _ ↦ hX.isStoppingTime_largeJumpSequence hc hb i)
    (hiX t) (hiX u) hiD _ _ hM hR
  · filter_upwards [hbound, hcoeff] with ω hω hz
    exact ⟨hω t, hω u, fun i _ ↦ hz i⟩
  · apply Eventually.of_forall
    intro ω
    change min (2 * N) ‖largeJumpResidual X b K u ω - largeJumpResidual X b K t ω‖ ≤ _
    exact (hc ω).min_norm_largeJumpResidual_increment_le_capped_window b K (2 * N)
      hδ htu huT huδ

end MeasureTheory

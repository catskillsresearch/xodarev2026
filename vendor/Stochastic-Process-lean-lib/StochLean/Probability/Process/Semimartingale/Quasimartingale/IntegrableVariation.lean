/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale
public import StochLean.Probability.Process.FiniteVariation.Integrable
public import StochLean.Analysis.PathVariation.FiniteVariation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Integrable variation implies finite conditional variation

The actual full-half-line variation bounds the sum of the absolute increments
of every existing `TimePartition`. Conditional expectation is an L1
contraction. The artificial terminal-zero tail is bounded by the initial
absolute value plus that same actual variation. Consequently conditional
variation is at most the initial first absolute moment plus twice the expected
full variation.

The initial value is required to be integrable separately. Actual variation
measurability and finiteness come from `HasIntegrableVariation`; neither is
inferred merely from a domination inequality. Adaptedness gives measurability
of each actual coordinate. No usual-filtration, finite-measure, compensator,
semimartingale, or actual terminal-limit hypothesis is needed.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

private theorem ae_norm_le_initial_add_variation (hv : HasIntegrableVariation X P) :
    ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ ‖X 0 ω‖ + (eVariationOn (X · ω) univ).toReal := by
  filter_upwards [hv.ae_forall_norm_sub_le] with ω hω t
  calc
    ‖X t ω‖ ≤ ‖X t ω - X 0 ω‖ + ‖X 0 ω‖ := by
      simpa only [sub_add_cancel] using norm_add_le (X t ω - X 0 ω) (X 0 ω)
    _ ≤ (eVariationOn (X · ω) univ).toReal + ‖X 0 ω‖ :=
      add_le_add (hω 0 t) le_rfl
    _ = ‖X 0 ω‖ + (eVariationOn (X · ω) univ).toReal := add_comm _ _

private theorem integrable_coordinate_of_initial_and_variation
    (hv : HasIntegrableVariation X P) (ha : Adapted F X)
    (hi0 : Integrable (X 0) P) (t : ℝ≥0) : Integrable (X t) P := by
  apply (hi0.norm.add hv.integrable_eVariationOn_toReal).mono'
    ((ha.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
  exact (ae_norm_le_initial_add_variation hv).mono fun _ hω ↦ hω t

private theorem integral_conditionalVariationSum_le_initial_add_twice_variation
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hi0 : Integrable (X 0) P)
    {T : ℝ≥0} (π : TimePartition T) :
    (∫ ω, conditionalVariationSum X F P π ω ∂P) ≤
      (∫ ω, |X 0 ω| ∂P) + 2 * ∫ ω, (eVariationOn (X · ω) univ).toReal ∂P := by
  have hi (t : ℝ≥0) := integrable_coordinate_of_initial_and_variation hv ha hi0 t
  have hiInc (i : Fin π.size) :
      Integrable (fun ω ↦ |X (π.left i) ω - X (π.right i) ω|) P :=
    ((hi (π.left i)).sub (hi (π.right i))).abs
  have hiCE (i : Fin π.size) :
      Integrable (fun ω ↦ |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) P :=
    integrable_condExp.abs
  have hsum : ∀ᵐ ω ∂P,
      (∑ i, |X (π.left i) ω - X (π.right i) ω|) ≤
        (eVariationOn (X · ω) univ).toReal := by
    filter_upwards [hv.ae_eVariationOn_ne_top] with ω hω
    have hBV : BoundedVariationOn (X · ω) univ := hω
    have hs := π.sum_abs_increment_le (hBV.mono (subset_univ (Icc 0 T)))
    have hm := ENNReal.toReal_mono hω (eVariationOn.mono (X · ω) (subset_univ (Icc 0 T)))
    simpa only [TimePartition.increment, abs_sub_comm] using hs.trans hm
  have hIntInc : (∑ i, ∫ ω, |X (π.left i) ω - X (π.right i) ω| ∂P) ≤
      ∫ ω, (eVariationOn (X · ω) univ).toReal ∂P := by
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ hiInc i)]
    exact integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ ↦ hiInc i))
      hv.integrable_eVariationOn_toReal hsum
  have hIntCE :
      (∑ i, ∫ ω, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω| ∂P) ≤
        ∫ ω, (eVariationOn (X · ω) univ).toReal ∂P := by
    apply le_trans (Finset.sum_le_sum fun i _ ↦
      integral_abs_condExp_le (μ := P) (m := F (π.left i))
        (X (π.left i) - X (π.right i))) hIntInc
  have hTail : (∫ ω, |X T ω| ∂P) ≤
      (∫ ω, |X 0 ω| ∂P) + ∫ ω, (eVariationOn (X · ω) univ).toReal ∂P := by
    rw [← integral_add hi0.abs hv.integrable_eVariationOn_toReal]
    apply integral_mono_ae (hi T).abs (hi0.abs.add hv.integrable_eVariationOn_toReal)
    change ∀ᵐ ω ∂P, |X T ω| ≤ |X 0 ω| + (eVariationOn (X · ω) univ).toReal
    simpa only [Real.norm_eq_abs] using
      (ae_norm_le_initial_add_variation hv).mono (fun _ hω ↦ hω T)
  change (∫ ω, (∑ i, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) +
    |X T ω - 0| ∂P) ≤ _
  simp only [sub_zero]
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ ↦ hiCE i)) (hi T).abs,
    integral_finsetSum Finset.univ (fun i _ ↦ hiCE i)]
  linarith only [hIntCE, hTail]

/-- A direct quantitative bound for the sole conditional-variation owner.
The finite actual variation is retained before its real conversion is used.
No path regularity or usual-filtration condition is needed for this bound. -/
theorem HasIntegrableVariation.eConditionalVariation_le
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hi0 : Integrable (X 0) P) :
    eConditionalVariation X F P ≤ ENNReal.ofReal
      ((∫ ω, |X 0 ω| ∂P) + 2 * ∫ ω, (eVariationOn (X · ω) univ).toReal ∂P) := by
  unfold eConditionalVariation
  refine iSup_le fun T ↦ iSup_le fun π ↦ ?_
  rw [eConditionalVariationOnPartition_eq_ofReal_integral
    (integrable_coordinate_of_initial_and_variation hv ha hi0)]
  exact ENNReal.ofReal_le_ofReal
    (integral_conditionalVariationSum_le_initial_add_twice_variation hv ha hi0 π)

/-- An adapted cadlag process with integrable whole-half-line variation and
integrable initial value is a quasimartingale. This direct argument does not
use a proposed compensator, Rao decomposition, or semimartingale property. -/
theorem HasIntegrableVariation.isQuasimartingale
    (hv : HasIntegrableVariation X P) (ha : Adapted F X)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) : IsQuasimartingale X F P := by
  refine ⟨ha, hc, integrable_coordinate_of_initial_and_variation hv ha hi0, ?_⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hv.eConditionalVariation_le ha hi0)

end ProbabilityTheory

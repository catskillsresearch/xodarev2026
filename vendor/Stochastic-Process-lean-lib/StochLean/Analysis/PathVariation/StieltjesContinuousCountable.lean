/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VariationJumpSeries
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Continuous variation measures ignore countable jump supports

The actual Stieltjes measure of total variation of a continuous locally-BV
path vanishes on every countable set. Positive-time singleton masses vanish
by the native left-jump formula for variation; the zero singleton is handled
by the existing increment-measure convention. No atomlessness hypothesis or
global finite-variation bound is supplied.

The positive-time jump support of another right-continuous locally-BV path
is countable by the existing jump-support theorem. Consequently both its
measure and every nonnegative indicator-weighted integral against continuous
total variation vanish. These are deterministic fiber statements and do not
assume any process predictability or introduce a new variation measure.
-/

@[expose] public section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace StochLean

variable {x y : ℝ≥0 → ℝ}
  (hy : LocallyBoundedVariationOn y univ)
  (hry : ∀ t, ContinuousWithinAt y (Ici t) t) (hcy : Continuous y)

include hcy

/-- Continuity removes every actual variation atom. At zero this is the
existing increment-measure formula, not an assumption on the initial value. -/
theorem totalVariationStieltjes_measure_singleton_of_continuous (t : ℝ≥0) :
    (totalVariationStieltjes y hy hry).measure {t} = 0 := by
  by_cases ht : t = 0
  · subst t
    exact variationStieltjes_measure_zero _
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    have hl : Tendsto (pathTotalVariation y) (𝓝[<] t) (𝓝 (pathTotalVariation y t)) := by
      have h := variationOnFromTo.tendsto_left (mem_univ 0) (mem_univ t) hy
        (hcy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      simpa only [univ_inter, dist_self, sub_zero, pathTotalVariation] using h
    have he : leftLim (totalVariationStieltjes y hy hry) t =
        totalVariationStieltjes y hy hry t := leftLim_eq_of_tendsto hl
    rw [StieltjesFunction.measure_singleton, he, sub_self, ENNReal.ofReal_zero]

/-- The native null-singleton class is derived from continuity of the path. -/
theorem nullSingletonClass_totalVariationStieltjes_of_continuous :
    NullSingletonClass (totalVariationStieltjes y hy hry).measure :=
  ⟨totalVariationStieltjes_measure_singleton_of_continuous hy hry hcy⟩

/-- No measurability premise on the countable set is necessary. -/
theorem totalVariationStieltjes_measure_countable_of_continuous
    {S : Set ℝ≥0} (hS : S.Countable) :
    (totalVariationStieltjes y hy hry).measure S = 0 := by
  let := nullSingletonClass_totalVariationStieltjes_of_continuous hy hry hcy
  exact hS.measure_zero _

/-- Every nonnegative weight supported on a countable set has zero integral,
including weights with infinite values. No integrability or measurability
of the weight is needed on this null support. -/
theorem lintegral_indicator_totalVariationStieltjes_eq_zero_of_countable
    {S : Set ℝ≥0} (hS : S.Countable) (f : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ t, S.indicator f t ∂(totalVariationStieltjes y hy hry).measure) = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ ∫⁻ t in S, f t ∂(totalVariationStieltjes y hy hry).measure :=
      lintegral_indicator_le f S
    _ = 0 := by
      rw [Measure.restrict_eq_zero.mpr
        (totalVariationStieltjes_measure_countable_of_continuous hy hry hcy hS),
        lintegral_zero_measure]

/-- Continuous total variation gives zero mass to all positive-time jumps
of an actual right-continuous locally-BV path. -/
theorem totalVariationStieltjes_measure_jumpSupport_of_continuous
    (hx : LocallyBoundedVariationOn x univ)
    (hrx : ∀ t, ContinuousWithinAt x (Ici t) t) :
    (totalVariationStieltjes y hy hry).measure
      {t | 0 < t ∧ x t - leftLim x t ≠ 0} = 0 := by
  apply totalVariationStieltjes_measure_countable_of_continuous hy hry hcy
  exact (countable_support_jump_of_locallyBoundedVariation hx hrx).mono
    (fun _ ht ↦ ht.2)

/-- Weighted positive-time jump support of another locally-BV path is null
for the actual continuous variation measure. -/
theorem lintegral_indicator_jumpSupport_totalVariationStieltjes_eq_zero
    (hx : LocallyBoundedVariationOn x univ)
    (hrx : ∀ t, ContinuousWithinAt x (Ici t) t) (f : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ t, {t | 0 < t ∧ x t - leftLim x t ≠ 0}.indicator f t
      ∂(totalVariationStieltjes y hy hry).measure) = 0 := by
  exact lintegral_indicator_totalVariationStieltjes_eq_zero_of_countable hy hry hcy
    ((countable_support_jump_of_locallyBoundedVariation hx hrx).mono (fun _ ht ↦ ht.2)) f

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Approximation
public import StochLean.Analysis.PathVariation.Exponent
public import StochLean.Analysis.PathVariation.FiniteVariation

/-!
# Total variation and refinement

Klenke 21.60: the one-variation sums increase under refinement and tend to the
canonical Mathlib total variation, which may be infinite. The limit theorem is
stronger than the source nested-partition statement: continuity and vanishing
mesh suffice. Finiteness is required before any conversion to a real number.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0}

theorem TimePartition.eVariationOn_range (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    eVariationOn f (Set.range π.point) = ENNReal.ofReal (pVariationSum 1 π f) := by
  rw [← π.image_pointNat_Iic, eVariationOn.image_range_of_monotone f π.pointNat_mono,
    Finset.sum_range, pVariationSum_one, ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)]
  apply sum_congr rfl
  intro i _
  have hl : π.pointNat i = π.left i := π.pointNat_fin i.castSucc
  have hr : π.pointNat (i + 1) = π.right i := π.pointNat_fin i.succ
  rw [hl, hr, edist_comm, edist_dist, Real.dist_eq]
  rfl

/-- Refinement is inclusion of endpoint sets, independent of their chosen enumeration. -/
def TimePartition.Refines (π ρ : TimePartition T) : Prop :=
  Set.range ρ.point ⊆ Set.range π.point

theorem TimePartition.Refines.pVariationSum_one_le {π ρ : TimePartition T}
    (h : π.Refines ρ) (f : ℝ≥0 → ℝ) : pVariationSum 1 ρ f ≤ pVariationSum 1 π f := by
  apply (ENNReal.ofReal_le_ofReal_iff (pVariationSum_nonneg 1 π f)).mp
  rw [← π.eVariationOn_range, ← ρ.eVariationOn_range]
  exact eVariationOn.mono f h

/-- Convergence of upper endpoint evaluations suffices, even for discontinuous paths. -/
theorem tendsto_oneVariationSum_of_ceiling_tendsto {f : ℝ≥0 → ℝ} {π : ℕ → TimePartition T}
    (happrox : ∀ t ∈ Icc 0 T,
      Tendsto (fun n ↦ f ((π n).ceilingPoint t)) atTop (𝓝 (f t))) :
    Tendsto (fun n ↦ ENNReal.ofReal (pVariationSum 1 (π n) f)) atTop
      (𝓝 (eVariationOn f (Icc 0 T))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eVariationOn.lowerSemicontinuous_aux happrox ha] with n hn
    apply hn.trans_le
    rw [← (π n).eVariationOn_range]
    exact eVariationOn.comp_le_of_monotoneOn f (π n).ceilingPoint
      ((π n).ceilingPoint_mono.monotoneOn _) (fun t _ ↦ (π n).ceilingPoint_mem t)
  · intro b hb
    apply Eventually.of_forall
    intro n
    rw [← (π n).eVariationOn_range]
    exact (eVariationOn.mono f (by
      rintro t ⟨i, rfl⟩
      exact ⟨bot_le, (π n).point_le_horizon i⟩)).trans_lt hb

/-- The one-variation limit can be infinite; no real-valued fallback is used. -/
theorem tendsto_oneVariationSum_of_continuous {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ENNReal.ofReal (pVariationSum 1 (π n) f)) atTop
      (𝓝 (eVariationOn f (Icc 0 T))) := by
  apply tendsto_oneVariationSum_of_ceiling_tendsto
  intro t ht
  apply (hf t ht).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨TimePartition.ceilingPoint_tendsto hmesh ht.2,
    Eventually.of_forall fun n ↦ ⟨bot_le, (π n).ceilingPoint_le_horizon t⟩⟩

/-- Right continuity suffices for one-variation sums; continuity across jumps is not needed. -/
theorem tendsto_oneVariationSum_of_rightContinuous {f : ℝ≥0 → ℝ}
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ENNReal.ofReal (pVariationSum 1 (π n) f)) atTop
      (𝓝 (eVariationOn f (Icc 0 T))) := by
  apply tendsto_oneVariationSum_of_ceiling_tendsto
  intro t ht
  apply (hf t).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨TimePartition.ceilingPoint_tendsto hmesh ht.2, Eventually.of_forall (fun n ↦ ?_)⟩
  have h := (π n).min_le_ceilingPoint t
  rw [min_eq_left ht.2] at h
  exact h

theorem hasPVariationAlong_one_of_continuous_boundedVariation {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hfv : BoundedVariationOn f (Icc 0 T))
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    HasPVariationAlong 1 π f (eVariationOn f (Icc 0 T)).toReal := by
  have h := (ENNReal.continuousAt_toReal hfv).tendsto.comp
    (tendsto_oneVariationSum_of_continuous hf hmesh)
  simpa only [HasPVariationAlong, Function.comp_def,
    ENNReal.toReal_ofReal (pVariationSum_nonneg _ _ _)] using h

theorem hasPVariationAlong_zero_of_continuous_boundedVariation {q : ℝ} (hq : 1 < q)
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hfv : BoundedVariationOn f (Icc 0 T)) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    HasPVariationAlong q π f 0 :=
  (hasPVariationAlong_one_of_continuous_boundedVariation hf hfv hmesh).of_exponent_lt
    zero_lt_one hq hf hmesh

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Stieltjes
public import StochLean.Probability.Process.FiniteVariation.Integrable
public import StochLean.ForMathlib.Probability.Kernel.PointwiseFinite

/-! # Total mass and s-finiteness of the actual variation kernel

The kernel already constructed from path variation has precisely the extended
variation as its total mass. Compact finiteness supplies s-finiteness even when
the whole-halfline mass is infinite. Integrable variation then bounds its
expected total mass, without silently replacing infinite mass by `toReal`.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

/-- Exhaustion by integer compact intervals retains infinite total variation. -/
theorem totalVariationKernel_univ (ha : Adapted F X)
    (hv : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hr : ∀ ω, IsRightContinuousPath (X · ω)) (ω : Ω) :
    totalVariationKernel X ha hv hr ω univ = eVariationOn (X · ω) univ := by
  have hcover : (⋃ n : ℕ, Icc 0 (n : ℝ≥0)) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨n, bot_le, hn⟩
  have hmono : Monotone (fun n : ℕ ↦ Icc 0 (n : ℝ≥0)) := by
    intro n m hnm
    exact Icc_subset_Icc le_rfl (Nat.cast_le.mpr hnm)
  rw [eVariationOn_univ_eq_iSup_Icc_nat, ← hcover, hmono.measure_iUnion]
  congr 1
  funext n
  exact totalVariationStieltjes_measure_Icc_zero (X · ω) (hv ω) (hr ω) n

/-- Compactly finite fibers provide the genuine kernel class needed by native
measure composition; global finite variation is not assumed. -/
theorem isSFiniteKernel_totalVariationKernel (ha : Adapted F X)
    (hv : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hr : ∀ ω, IsRightContinuousPath (X · ω)) :
    IsSFiniteKernel (totalVariationKernel X ha hv hr) := by
  apply Kernel.isSFiniteKernel_of_finite_Iic
  intro ω n
  change (totalVariationStieltjes (X · ω) (hv ω) (hr ω)).measure (Iic (n : ℝ≥0)) ≠ ∞
  rw [← Icc_bot]
  change (totalVariationStieltjes (X · ω) (hv ω) (hr ω)).measure (Icc 0 (n : ℝ≥0)) ≠ ∞
  rw [totalVariationStieltjes_measure_Icc_zero (X · ω) (hv ω) (hr ω) n]
  simpa only [BoundedVariationOn, univ_inter] using
    hv ω 0 (n : ℝ≥0) (mem_univ 0) (mem_univ _)

/-- This is the expected total mass of the actual kernel, not an assumed
finite measure on predictable sets. No finiteness of the ambient measure is needed. -/
theorem HasIntegrableVariation.lintegral_totalVariationKernel_univ_lt_top
    {P : Measure Ω} (hX : HasIntegrableVariation X P) (ha : Adapted F X)
    (hv : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hr : ∀ ω, IsRightContinuousPath (X · ω)) :
    (∫⁻ ω, totalVariationKernel X ha hv hr ω univ ∂P) < ∞ := by
  simp_rw [totalVariationKernel_univ]
  exact hX.lintegral_eVariationOn_lt_top

end ProbabilityTheory

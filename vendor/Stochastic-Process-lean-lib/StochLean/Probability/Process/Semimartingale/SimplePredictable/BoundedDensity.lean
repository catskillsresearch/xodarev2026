/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Density
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Algebra
public import StochLean.Probability.Process.UCP.Nonexpansive
public import StochLean.Probability.Process.UCP.Algebra

/-! # Bounded simple approximation with the original bound

Scalar interval projection fixes zero, so it preserves the full source simple
class. Its nonexpansiveness retains UCP convergence. The input bound may hold
only on one full-measure path event; every approximant is bounded everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

theorem IsSimplePredictable.clamp (hH : IsSimplePredictable H F) (C : ℝ≥0) :
    IsSimplePredictable (fun t ω ↦ max (-(C : ℝ)) (min (C : ℝ) (H t ω))) F := by
  exact hH.map₂ (IsSimplePredictable.zero F) (fun x _ ↦ max (-(C : ℝ)) (min (C : ℝ) x))
    (measurable_const.max (measurable_const.min measurable_fst))
    (by simp only [min_eq_right C.coe_nonneg, max_eq_right (neg_nonpos.mpr C.coe_nonneg)])

theorem norm_clamp_le (C : ℝ≥0) (x : ℝ) : ‖max (-(C : ℝ)) (min (C : ℝ) x)‖ ≤ C := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (neg_le_self C.coe_nonneg) (min_le_left _ _)⟩

theorem clamp_eq_of_norm_le {C : ℝ≥0} {x : ℝ} (hx : ‖x‖ ≤ C) :
    max (-(C : ℝ)) (min (C : ℝ) x) = x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (show |x| ≤ C from hx)
  rw [min_eq_right hhi, max_eq_right hlo]

theorem exists_bounded_simplePredictable_tendstoUCP [IsFiniteMeasure P]
    (ha : Adapted F H) (hF : F.IsUsual P) (hr : HasCagladPaths H P)
    (C : ℝ≥0) (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) :
    ∃ S : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, IsSimplePredictable (S n) F) ∧
      (∀ n t ω, ‖S n t ω‖ ≤ C) ∧ TendstoUCP P S atTop H := by
  obtain ⟨A, hA, huA⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  let f : ℝ → ℝ := fun x ↦ max (-(C : ℝ)) (min (C : ℝ) x)
  have hf : LipschitzWith 1 f := (LipschitzWith.id.const_min (C : ℝ)).const_max (-(C : ℝ))
  refine ⟨fun n t ω ↦ f (A n t ω), fun n ↦ (hA n).clamp C,
    fun n t ω ↦ norm_clamp_le C (A n t ω), ?_⟩
  apply (huA.comp_nonexpansive hf).congr_right
  exact hb.mono fun ω hω t ↦ clamp_eq_of_norm_le (hω t)

end ProbabilityTheory

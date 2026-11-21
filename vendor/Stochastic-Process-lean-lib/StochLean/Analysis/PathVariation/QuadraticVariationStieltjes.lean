/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeIntegralLimit
public import StochLean.Analysis.PathVariation.RestrictionConvergence

/-! # The actual Stieltjes integral of a deterministic quadratic-variation limit

The zero initial value and monotonicity of the limit follow from the square
sums. No extra bracket owner or weighted-convergence certificate is introduced.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean

theorem tendsto_completedQuadraticVariationSum_restrict {π : ℕ → LocallyFinitePartition}
    {T : ℝ≥0} {x A : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    (hm : Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hQ : ∀ s ≤ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict s) x (A s))
    {s : ℝ≥0} (hs : s ≤ T) :
    Tendsto (fun n ↦ completedQuadraticVariationSum ((π n).restrict T) x s)
      atTop (𝓝 (A s)) :=
  tendsto_completedQuadraticVariationSum_of_partial hx hm hs
    ((hQ s hs).congr' (Eventually.of_forall
      fun n ↦ (π n).quadraticVariationSum_restrict_eq_stop hs x))

theorem quadraticVariation_restrict_limit_zero {π : ℕ → LocallyFinitePartition}
    {x A : ℝ≥0 → ℝ}
    (hQ : ∀ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) x (A T)) :
    A 0 = 0 := by
  have hz (n : ℕ) : quadraticVariationSum ((π n).restrict 0) x = 0 := by
    rw [← completedQuadraticVariationSum_horizon, completedQuadraticVariationSum_zero]
  exact tendsto_nhds_unique ((hQ 0).congr hz) tendsto_const_nhds

theorem monotone_quadraticVariation_restrict_limit {π : ℕ → LocallyFinitePartition}
    {x A : ℝ≥0 → ℝ} (hx : Continuous x)
    (hm : ∀ T, Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hQ : ∀ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) x (A T)) :
    Monotone A := by
  intro s t hst
  exact le_of_tendsto_of_tendsto
    (tendsto_completedQuadraticVariationSum_restrict hx.continuousOn (hm t)
      (fun u _ ↦ hQ u) hst)
    (tendsto_completedQuadraticVariationSum_restrict hx.continuousOn (hm t)
      (fun u _ ↦ hQ u) le_rfl)
    (Eventually.of_forall fun n ↦
      completedQuadraticVariationSum_mono ((π n).restrict t) x hst)

theorem locallyBoundedVariationOn_quadraticVariation_restrict_limit
    {π : ℕ → LocallyFinitePartition} {x A : ℝ≥0 → ℝ} (hx : Continuous x)
    (hm : ∀ T, Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hQ : ∀ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) x (A T)) :
    LocallyBoundedVariationOn A univ :=
  ((monotone_quadraticVariation_restrict_limit hx hm hQ).monotoneOn univ).locallyBoundedVariationOn

theorem tendsto_weightedQuadraticVariationSum_right {π : ℕ → LocallyFinitePartition}
    {T : ℝ≥0} {x A : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    (hm : Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hQ : ∀ s ≤ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict s) x (A s))
    {hv : LocallyBoundedVariationOn A univ} {hr : ∀ t, ContinuousWithinAt A (Ici t) t}
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    Tendsto (fun n ↦ ∑ i : Fin ((π n).restrict T).size,
      f (((π n).restrict T).right i) * (((π n).restrict T).increment x i) ^ 2) atTop
      (𝓝 (pathStieltjesIntegral A hv hr f T)) :=
  tendsto_weighted_cumulativeStepSum
    (fun n ↦ ((π n).restrict T).right) (fun n i ↦ (((π n).restrict T).increment x i) ^ 2)
    (fun n _ ↦ ((π n).restrict T).point_le_horizon _) (fun _ _ ↦ sq_nonneg _)
    (fun _ ht ↦ tendsto_completedQuadraticVariationSum_restrict hx hm hQ ht.2) hf

end StochLean

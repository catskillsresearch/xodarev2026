/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Restriction
public import StochLean.Analysis.PathVariation.DenseConvergence
public import StochLean.Analysis.PathVariation.CovariationVariation

/-! # Infinite-partition convergence and all-times extraction

Exact stopping/restriction transport closes the deterministic interface between source
infinite partitions and the completed-cell approximation on a fixed compact horizon.
-/

@[expose] public section

open Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean

/-- Countably tested convergence extends to every time through monotone completed cells.
The partial-cell square sum is never assumed monotone. Nesting is not needed for this step. -/
theorem hasQuadraticVariationAlong_restrict_of_dense
    {π : ℕ → LocallyFinitePartition}
    (hmesh : ∀ T, Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    {f A : ℝ≥0 → ℝ} (hf : Continuous f) (hA : Continuous A) (hA0 : A 0 = 0)
    {D : Set ℝ≥0} (hD : Dense D)
    (hd : ∀ q ∈ D, HasQuadraticVariationAlong (fun n ↦ (π n).restrict q) f (A q))
    (hn : ∀ N : ℕ, HasQuadraticVariationAlong (fun n ↦ (π n).restrict N) f (A N))
    (s : ℝ≥0) : HasQuadraticVariationAlong (fun n ↦ (π n).restrict s) f (A s) := by
  obtain ⟨N, hs⟩ := exists_nat_ge s
  have hpartial {q : ℝ≥0} (hq : q ≤ N)
      (hqlim : HasQuadraticVariationAlong (fun n ↦ (π n).restrict q) f (A q)) :
      HasQuadraticVariationAlong (fun n ↦ (π n).restrict N)
        (fun t ↦ f (min t q)) (A q) :=
    hqlim.congr' (Eventually.of_forall (fun n ↦ (π n).quadraticVariationSum_restrict_eq_stop hq f))
  have hcompleted : Tendsto (fun n ↦ completedQuadraticVariationSum ((π n).restrict N) f s)
      atTop (𝓝 (A s)) := by
    apply tendsto_monotone_of_dense hD
      (fun n ↦ (completedQuadraticVariationSum_mono ((π n).restrict N) f).monotoneOn _)
      hA.continuousOn _ _ _ hs
    · simpa only [completedQuadraticVariationSum_zero, hA0] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
    · simpa only [HasQuadraticVariationAlong, completedQuadraticVariationSum_horizon] using hn N
    · intro q hq hqN
      exact tendsto_completedQuadraticVariationSum_of_partial hf.continuousOn
        (hmesh N) hqN (hpartial hqN (hd q hq))
  have herror := tendsto_partialQuadraticVariation_error_zero hf.continuousOn (hmesh N) hs
  have hlim : HasQuadraticVariationAlong (fun n ↦ (π n).restrict N)
      (fun t ↦ f (min t s)) (A s) := by
    simpa only [HasQuadraticVariationAlong, sub_add_cancel, zero_add] using herror.add hcompleted
  exact hlim.congr' (Eventually.of_forall
    (fun n ↦ ((π n).quadraticVariationSum_restrict_eq_stop hs f).symm))

/-- Klenke 21.61(ii) for the actual infinite-partition restriction convention. -/
theorem eVariationOn_covariation_restrict_limit_le {π : ℕ → LocallyFinitePartition}
    {T : ℝ≥0} {f g C : ℝ≥0 → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hfv : HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) f a)
    (hgv : HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) g b)
    (hC : ∀ s ≤ T, HasCovariationAlong (fun n ↦ (π n).restrict s) f g (C s)) :
    eVariationOn C (Icc 0 T) ≤ ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
  apply eVariationOn_covariation_limit_le hf hg hmesh hfv hgv
  intro s hs
  exact (hC s hs).congr' (Eventually.of_forall
    (fun n ↦ (π n).covariationSum_restrict_eq_stop hs f g))

theorem boundedVariationOn_covariation_restrict_limit {π : ℕ → LocallyFinitePartition}
    {T : ℝ≥0} {f g C : ℝ≥0 → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hfv : HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) f a)
    (hgv : HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) g b)
    (hC : ∀ s ≤ T, HasCovariationAlong (fun n ↦ (π n).restrict s) f g (C s)) :
    BoundedVariationOn C (Icc 0 T) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (eVariationOn_covariation_restrict_limit_le hf hg hmesh hfv hgv hC)

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StoppedVectorPairLimit
public import StochLean.Analysis.PathVariation.VectorTaylorJumpSeries
public import StochLean.Analysis.PathVariation.VectorTaylorSums

/-! # Cadlag Frechet Taylor errors converge to their actual jump series -/

@[expose] public section

open Set Filter Function ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem tendsto_frechetTaylorErrorSum_cadlag {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → E} (hx : IsCadlagPath x)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, normSquareVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsq : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2)) :
    Tendsto (fun n ↦ frechetTaylorErrorSum (π n) f x T) atTop
      (𝓝 (∑' s : Ioc 0 T, frechetSecondOrderRemainder f (leftLim x s) (x s))) := by
  have hΦ := continuous_frechetTaylorErrorCoefficient_of_contDiff hf
  have hs := (summable_abs_vector_pair_weighted_sq_jumps hx hsq hΦ).of_abs
  have h := tendsto_normSquarePairSum_stopped_cadlag_jump_series π hx hΦ
    (frechetTaylorErrorCoefficient_self f) hmesh hT hB hb hs
  simpa only [frechetTaylorErrorSum, frechetTaylorErrorCoefficient_mul_norm_sq] using h

end StochLean

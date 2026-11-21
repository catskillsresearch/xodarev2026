/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Stieltjes
public import StochLean.Probability.Process.Path.Cadlag

/-! # Right-continuous locally BV paths have finite left limits -/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem isCadlagPath_of_locallyBoundedVariation {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) : IsCadlagPath x := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  refine ⟨hr, fun t _ ↦ ⟨x 0 + Function.leftLim p t - Function.leftLim n t, ?_⟩⟩
  apply ((tendsto_const_nhds.add (p.mono.tendsto_leftLim t)).sub
    (n.mono.tendsto_leftLim t)).congr
  intro u
  change x 0 + pathPositiveVariation x u - pathNegativeVariation x u = x u
  linarith [pathPositiveVariation_sub_negative x u]

end StochLean

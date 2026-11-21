/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.FiniteProduct

/-! # Positive-time source left limits of continuous coordinate functions

No zero-preserving condition is imposed on the function. The equality is
deliberately restricted to positive times, since source left limits start at zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem leftLimitProcess_continuous_comp_coordinates_of_pos
    {Ω ι : Type*} {X : ι → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : ∀ i, IsCadlagPath (X i · ω)) {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    {t : ℝ≥0} (ht : 0 < t) :
    leftLimitProcess (fun s v ↦ f (fun i ↦ X i s v)) t ω =
      f (fun i ↦ leftLimitProcess (X i) t ω) := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  rw [leftLimitProcess, if_neg (ne_of_gt ht)]
  exact leftLim_eq_of_tendsto (hf.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun i ↦ (hX i).tendsto_leftLimitProcess (ne_of_gt ht))))

end ProbabilityTheory

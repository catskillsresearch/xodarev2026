/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import StochLean.Probability.Brownian.QuadraticVariationStrong
import StochLean.Analysis.PathVariation.RestrictionConvergence

/-! # Brownian quadratic variation on one event for all times

For each prescribed admissible partition sequence, one event supports continuity and convergence
at every deterministic time. The event is obtained from a fixed countable dense set and integer
horizons. Monotonicity is used only for completed-cell sums, never for moving partial sums.
-/

open MeasureTheory Filter Set StochLean TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Klenke 21.64: strong quadratic variation on one common event, for every time, along any
prescribed admissible nested sequence. The null event may depend on that sequence. -/
theorem IsBrownianReal.ae_forall_quadraticVariationAlong_restrict
    (hB : IsBrownianReal B P) {π : ℕ → LocallyFinitePartition}
    (hπ : IsAdmissiblePartitionSequence π) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) (B · ω) T := by
  have hgrid (k : ℕ) := hB.toIsPreBrownianReal.ae_quadraticVariationAlong_restrict
    hπ (denseSeq ℝ≥0 k)
  have hint (N : ℕ) := hB.toIsPreBrownianReal.ae_quadraticVariationAlong_restrict hπ N
  filter_upwards [hB.cont, ae_all_iff.mpr hgrid, ae_all_iff.mpr hint] with ω hcont hd hn
  apply hasQuadraticVariationAlong_restrict_of_dense _ hcont NNReal.continuous_coe rfl
    (denseRange_denseSeq ℝ≥0) _ hn
  · intro T
    simpa only [Function.comp_def, NNReal.coe_zero] using
      NNReal.continuous_coe.continuousAt.tendsto.comp (hπ.restrict_mesh_tendsto (fun _ ↦ T))
  · rintro q ⟨k, rfl⟩
    exact hd k

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import StochLean.Probability.Brownian.QuadraticVariationPaths
import StochLean.Analysis.PathVariation.UniformPartition

/-! # Brownian paths have infinite variation on every nondegenerate interval

The argument uses the explicit dyadic admissible sequence and strong square variation.
Countably many deterministic shifts suffice to obtain one event for all subintervals.
-/

open MeasureTheory Filter Set StochLean TopologicalSpace
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem IsBrownianReal.ae_forall_not_boundedVariationOn_zero
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → ¬ BoundedVariationOn (B · ω) (Icc 0 T) := by
  filter_upwards [hB.cont,
    hB.ae_forall_quadraticVariationAlong_restrict LocallyFinitePartition.dyadic_admissible]
      with ω hcont hq
  intro T hT hfv
  have hmesh : Tendsto (fun n ↦ ((LocallyFinitePartition.dyadic n).restrict T).mesh)
      atTop (𝓝 0) := LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T)
  have hm : Tendsto (fun n ↦ (((LocallyFinitePartition.dyadic n).restrict T).mesh : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, NNReal.coe_zero] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hmesh
  have hzero := hasQuadraticVariationAlong_zero_of_continuous_boundedVariation
    hcont.continuousOn hfv hm
  have heq : (T : ℝ) = 0 := tendsto_nhds_unique (hq T) hzero
  exact (ne_of_gt (show (0 : ℝ) < T by exact_mod_cast hT)) heq

/-- Protter I.29, with one event for every nondegenerate compact interval. -/
theorem IsBrownianReal.ae_forall_not_boundedVariationOn
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t → ¬ BoundedVariationOn (B · ω) (Icc s t) := by
  have hshift (k : ℕ) := (hB.shift (denseSeq ℝ≥0 k)).ae_forall_not_boundedVariationOn_zero
  filter_upwards [ae_all_iff.mpr hshift] with ω hω
  intro s t hst hfv
  obtain ⟨a, ⟨k, rfl⟩, hsa, hat⟩ := (denseRange_denseSeq ℝ≥0).exists_between hst
  let a := denseSeq ℝ≥0 k
  have hpos : 0 < t - a := tsub_pos_of_lt hat
  apply hω k (t - a) hpos
  have hvar : eVariationOn (fun u ↦ B (a + u) ω - B a ω) (Icc 0 (t - a)) =
      eVariationOn ((B · ω) ∘ (fun u ↦ a + u)) (Icc 0 (t - a)) := by
    simp only [eVariationOn, Function.comp_apply, edist_dist, Real.dist_eq,
      sub_sub_sub_cancel_right]
  change eVariationOn (fun u ↦ B (a + u) ω - B a ω) (Icc 0 (t - a)) ≠ ∞
  rw [hvar]
  apply ne_top_of_le_ne_top hfv
  apply eVariationOn.comp_le_of_monotoneOn
  · exact (monotone_const.add monotone_id).monotoneOn _
  · intro u hu
    refine ⟨hsa.le.trans (le_add_of_nonneg_right hu.1), ?_⟩
    exact (add_le_add (le_refl a) hu.2).trans_eq (add_tsub_cancel_of_le hat.le)

theorem IsBrownianReal.ae_forall_eVariationOn_eq_top (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t → eVariationOn (B · ω) (Icc s t) = ∞ := by
  filter_upwards [hB.ae_forall_not_boundedVariationOn] with ω hω
  intro s t hst
  exact not_ne_iff.mp (hω s t hst)

end ProbabilityTheory

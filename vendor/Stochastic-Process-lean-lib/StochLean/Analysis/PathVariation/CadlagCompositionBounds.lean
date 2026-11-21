/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagBounded
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Compact range bounds including left limits and C1 preservation of BV -/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem range_leftLim_mem_Icc_of_cadlag {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    {T : ℝ≥0} {R : ℝ} (hR : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ R)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) :
    x t ∈ Icc (-R) R ∧ Function.leftLim x t ∈ Icc (-R) R := by
  have hm (u : ℝ≥0) (hu : u ∈ Icc 0 T) : x u ∈ Icc (-R) R := by
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hR u hu
  refine ⟨hm t ht, ?_⟩
  by_cases ht0 : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
    exact hm 0 ht
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht0
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    apply isClosed_Icc.mem_of_tendsto (tendsto_leftLim_of_tendsto (hx.2 t ht0))
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hm u ⟨bot_le, (show u < t from hu).le.trans ht.2⟩

theorem exists_compact_pair_bound_of_cadlag {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    (T : ℝ≥0) {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2)) :
    ∃ C : ℝ, (∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, ‖Φ (x a) (x b)‖ ≤ C) ∧
      (∀ t ∈ Icc 0 T, ‖Φ (Function.leftLim x t) (x t)‖ ≤ C) := by
  obtain ⟨R, _, hR⟩ := hx.exists_norm_bound_Icc T
  have hm {t : ℝ≥0} (ht : t ∈ Icc 0 T) := range_leftLim_mem_Icc_of_cadlag hx hR ht
  have hK : IsCompact ((Icc (-R) R) ×ˢ (Icc (-R) R)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := (hK.image hΦ).isBounded.exists_norm_le
  refine ⟨C, ?_, ?_⟩
  · intro a ha b hb
    exact hC _ (mem_image_of_mem (fun p : ℝ × ℝ ↦ Φ p.1 p.2)
      (show (x a, x b) ∈ (Icc (-R) R) ×ˢ (Icc (-R) R) from ⟨(hm ha).1, (hm hb).1⟩))
  · intro t ht
    exact hC _ (mem_image_of_mem (fun p : ℝ × ℝ ↦ Φ p.1 p.2)
      (show (Function.leftLim x t, x t) ∈ (Icc (-R) R) ×ˢ (Icc (-R) R) from
        ⟨(hm ht).2, (hm ht).1⟩))

theorem locallyBoundedVariationOn_contDiff_comp_of_cadlag {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) : LocallyBoundedVariationOn (f ∘ x) univ := by
  intro a b ha hb
  obtain ⟨R, _, hR⟩ := hx.exists_norm_bound_Icc b
  obtain ⟨C, hC⟩ := hf.contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_Icc (-R) R) isCompact_Icc
  apply hC.comp_boundedVariationOn (s := univ ∩ Icc a b) ?_ (hv a b ha hb)
  intro t ht
  exact (range_leftLim_mem_Icc_of_cadlag hx hR ⟨bot_le, ht.2.2⟩).1

end StochLean

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralRiemann
public import StochLean.Analysis.PathVariation.StieltjesIntegralRegularity
public import StochLean.Analysis.PathVariation.UniformPartition
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Pseudo.Real

/-! # C1 change of variables along a continuous finite-variation path

The first-order remainders are bounded by their derivative oscillation times
the path variation. Actual left Riemann sums identify the Stieltjes integral.
The increment formula excludes the separately owned source initial term.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

theorem norm_firstOrderRemainder_le {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z)
    {a b C : ℝ} (hb : ∀ z ∈ uIcc a b, ‖φ' z - φ' a‖ ≤ C) :
    ‖φ b - φ a - φ' a * (b - a)‖ ≤ C * ‖b - a‖ := by
  have hd (z : ℝ) : HasDerivAt (fun u ↦ φ u - φ' a * u) (φ' z - φ' a) z := by
    have hl : HasDerivAt (fun u ↦ φ' a * u) (φ' a) z := by
      simpa only [mul_one, id_eq] using (hasDerivAt_id z).const_mul (φ' a)
    exact (hφ z).sub hl
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc a b) ↦ (hd z).hasDerivWithinAt) hb (convex_uIcc a b)
    left_mem_uIcc right_mem_uIcc
  convert h using 1
  congr 1
  ring

theorem tendsto_derivativeSum_of_continuous_bv {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) (hv : BoundedVariationOn x (Icc 0 T))
    {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hc : Continuous φ')
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size, φ' (x ((π n).left i)) * (π n).increment x i)
      atTop (𝓝 (φ (x T) - φ (x 0))) := by
  obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn hx).isBounded.exists_norm_le
  have hxR (t : ℝ≥0) (ht : t ∈ Icc 0 T) : x t ∈ Icc (-R) R := by
    have h := hR _ (mem_image_of_mem x ht)
    change -R ≤ x t ∧ x t ≤ R
    simpa only [Real.norm_eq_abs, abs_le] using h
  let V : ℝ := (eVariationOn x (Icc 0 T)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hη : 0 < ε / (V + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (hc.continuousOn (s := Icc (-R) R)))
    (ε / (V + 1)) hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((TimePartition.maxIncrement_tendsto_zero hx hmesh).eventually_lt_const hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hi (i : Fin (π n).size) :
      ‖φ (x ((π n).right i)) - φ (x ((π n).left i)) -
        φ' (x ((π n).left i)) * (π n).increment x i‖ ≤
          ε / (V + 1) * |(π n).increment x i| := by
    apply norm_firstOrderRemainder_le hφ
    intro z hz
    have hl := hxR ((π n).left i) ⟨bot_le, (π n).point_le_horizon _⟩
    have hr := hxR ((π n).right i) ⟨bot_le, (π n).point_le_horizon _⟩
    have hzR := uIcc_subset_Icc hl hr hz
    have hd : dist z (x ((π n).left i)) < δ := by
      calc
        _ = dist (x ((π n).left i)) z := dist_comm _ _
        _ ≤ dist (x ((π n).left i)) (x ((π n).right i)) := Real.dist_left_le_of_mem_uIcc hz
        _ = |(π n).increment x i| := by rw [dist_comm, Real.dist_eq, TimePartition.increment]
        _ ≤ ((π n).maxIncrement x : ℝ) := (π n).abs_increment_le_maxIncrement x i
        _ < δ := hN n hn
    exact (hmod z hzR (x ((π n).left i)) hl hd).le
  have hsum : ‖(φ (x T) - φ (x 0)) -
      ∑ i : Fin (π n).size, φ' (x ((π n).left i)) * (π n).increment x i‖ ≤ ε / (V + 1) * V := by
    rw [← (π n).sum_increment (fun t ↦ φ (x t)), ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (π n).size, ‖(π n).increment (fun t ↦ φ (x t)) i -
          φ' (x ((π n).left i)) * (π n).increment x i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (π n).size, ε / (V + 1) * |(π n).increment x i| :=
        Finset.sum_le_sum fun i _ ↦ hi i
      _ = ε / (V + 1) * ∑ i : Fin (π n).size, |(π n).increment x i| := by rw [Finset.mul_sum]
      _ ≤ ε / (V + 1) * V := mul_le_mul_of_nonneg_left ((π n).sum_abs_increment_le hv) hη.le
  rw [dist_comm, dist_eq_norm_sub]
  apply hsum.trans_lt
  calc
    _ < ε / (V + 1) * (V + 1) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ _ (by linarith)

theorem pathStieltjesIncrementIntegral_chain_rule {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T))
    {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hc : Continuous φ') :
    pathStieltjesIncrementIntegral x hv hr (fun t ↦ φ' (x t)) 0 T = φ (x T) - φ (x 0) := by
  let π : ℕ → TimePartition T := fun n ↦ (LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T))
  have hfv : BoundedVariationOn x (Icc 0 T) := by
    simpa only [univ_inter] using hv 0 T (mem_univ _) (mem_univ _)
  have hi := tendsto_stieltjesLeftSum_terminal (x := x) (hx := hv) (hr := hr)
    (hc.comp_continuousOn hx) hm
  have hs := tendsto_derivativeSum_of_continuous_bv hx hfv hφ hc hm
  have heq := tendsto_nhds_unique hi
    ((tendsto_const_nhds (x := φ' (x 0) * x 0)).add hs)
  change φ' (x 0) * x 0 + pathStieltjesIncrementIntegral x hv hr (fun t ↦ φ' (x t)) 0 T =
    φ' (x 0) * x 0 + (φ (x T) - φ (x 0)) at heq
  exact add_left_cancel heq

theorem pathStieltjesIntegral_chain_rule {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T))
    {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hc : Continuous φ') :
    pathStieltjesIntegral x hv hr (fun t ↦ φ' (x t)) T =
      φ' (x 0) * x 0 + (φ (x T) - φ (x 0)) := by
  rw [pathStieltjesIntegral, pathStieltjesIncrementIntegral_chain_rule hx hφ hc]

theorem pathStieltjesIncrementIntegral_contDiff {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T)) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    pathStieltjesIncrementIntegral x hv hr (fun t ↦ deriv φ (x t)) 0 T = φ (x T) - φ (x 0) :=
  pathStieltjesIncrementIntegral_chain_rule hx (fun z ↦ (hφ.differentiable_one z).hasDerivAt)
    hφ.continuous_deriv_one

theorem pathStieltjesIntegral_self_of_continuous {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T)) :
    pathStieltjesIntegral x hv hr x T = (x T ^ 2 + x 0 ^ 2) / 2 := by
  have hd (z : ℝ) : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) z z := by
    have h := ((hasDerivAt_id z).pow 2).div_const 2
    change HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) ((2 * z ^ (2 - 1) * 1) / 2) z at h
    convert h using 1
    ring
  have h := pathStieltjesIntegral_chain_rule (hv := hv) (hr := hr) hx hd continuous_id
  change pathStieltjesIntegral x hv hr x T = x 0 * x 0 + (x T ^ 2 / 2 - x 0 ^ 2 / 2) at h
  rw [h]
  ring

/-- The substitution corollary of Protter I.54, with oriented real interval endpoints. -/
theorem pathStieltjesIncrementIntegral_substitution {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T)) {g : ℝ → ℝ} (hg : Continuous g) :
    pathStieltjesIncrementIntegral x hv hr (fun t ↦ g (x t)) 0 T = ∫ u in x 0..x T, g u := by
  have hd (z : ℝ) : HasDerivAt (fun v ↦ ∫ u in x 0..v, g u) (g z) z :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have h := pathStieltjesIncrementIntegral_chain_rule (hv := hv) (hr := hr) hx hd hg
  simpa only [intervalIntegral.integral_same, sub_zero] using h

theorem locallyBoundedVariationOn_contDiff_comp {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : Continuous x)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) : LocallyBoundedVariationOn (φ ∘ x) univ := by
  have hr (t : ℝ≥0) : ContinuousWithinAt x (Ici t) t := hx.continuousWithinAt
  have hi : ∀ T, IntegrableOn (fun t ↦ deriv φ (x t)) (Ioc 0 T)
      (totalVariationStieltjes x hv hr).measure :=
    fun _ ↦ integrableOn_variationStieltjes_of_continuousOn
      ((hφ.continuous_deriv_one.comp hx).continuousOn)
  have hb := locallyBoundedVariationOn_pathStieltjesIntegral hi
  have hconst : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ φ (x 0) - deriv φ (x 0) * x 0) univ :=
    (monotone_const.monotoneOn univ).locallyBoundedVariationOn
  have heq : φ ∘ x = fun t ↦ (φ (x 0) - deriv φ (x 0) * x 0) +
      pathStieltjesIntegral x hv hr (fun t ↦ deriv φ (x t)) t := by
    funext t
    rw [pathStieltjesIntegral, pathStieltjesIncrementIntegral_contDiff hx.continuousOn hφ]
    simp only [Function.comp_apply]
    ring
  rw [heq]
  exact locallyBoundedVariationOn_add hconst hb

end StochLean

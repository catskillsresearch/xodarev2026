/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.DisjointPredictableJumps
public import StochLean.Probability.Process.FiniteVariation.IntegrableJumps
public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpIntegrableTerminal
public import StochLean.Analysis.PathVariation.LifetimeJumpSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Zero expectation of the actual predictable-IV mixed bracket

The predictable jump cover is constructed from the original process and made
positive and disjoint by actual predictable restrictions. At each covering
time, the integrable jump of the predictable FV process, cut off at the fixed
horizon, is measurable in that same time's before-field. The weighted UI jump
identity makes each actual mixed-jump term integrable with zero expectation.

The actual pure-jump bracket formula is reindexed along these finite graphs.
Every partial sum is dominated by twice the martingale bound times the actual
whole-halfline variation. Its integrability justifies dominated convergence;
there is no jump-count moment, candidate bracket martingale, or supplied jump
cover in the statement. The raw initial product vanishes only through `h0`.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter Set Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 1200000 in
-- Actual jump-series reindexing and dominated convergence elaborate many dependent path proofs.
/-- A bounded cadlag test martingale has an integrable actual raw bracket of
zero expectation with a zero-initial predictable integrable-variation process. -/
theorem
  IsStronglyPredictable.integrable_quadraticCovariation_and_integral_eq_zero_of_integrableVariation
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hv : HasIntegrableVariation A P) (h0 : A 0 =ᵐ[P] 0)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) (T : ℝ≥0) :
    let hSM := hM.isSemimartingale_of_bound hF hcM C hb
    let hSA := hv.hasFiniteVariationPaths.isSemimartingale hA.stronglyAdapted.adapted hF hcA
    Integrable (hSM.quadraticCovariation hSA hF T) P ∧
      (∫ ω, hSM.quadraticCovariation hSA hF T ω ∂P) = 0 := by
  classical
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSA := hv.hasFiniteVariationPaths.isSemimartingale hA.stronglyAdapted.adapted hF hcA
  let Q := hSM.quadraticCovariation hSA hF
  change Integrable (Q T) P ∧ (∫ ω, Q T ω ∂P) = 0
  obtain ⟨σ, hσ, hpos, hdisj, hcover⟩ :=
    hA.exists_positive_disjoint_predictableStoppingTime_cover_jumps hF hcA
      hv.hasFiniteVariationPaths
  let JA (n : ℕ) := stoppedValueWithTerminal (jumpProcess A) (fun _ ↦ (0 : ℝ)) (σ n)
  let JM (n : ℕ) := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (σ n)
  let E (n : ℕ) : Set Ω := {ω | σ n ω ≤ (T : WithTop ℝ≥0)}
  let K (n : ℕ) := (E n).indicator (JA n)
  let g (n : ℕ) : Ω → ℝ := K n * JM n
  have hE (n : ℕ) : MeasurableSet[(hσ n).1.measurableSpaceBefore] (E n) :=
    (hσ n).1.measurable_before measurableSet_Iic
  have hiK (n : ℕ) : Integrable (K n) P :=
    (hv.integrable_stopped_jump hA.stronglyAdapted.adapted hF hcA (hσ n).1
      (Eventually.of_forall (hpos n))).indicator
        ((hσ n).1.measurableSpaceBefore_le_ambient _ (hE n))
  have hmK (n : ℕ) : StronglyMeasurable[(hσ n).1.measurableSpaceBefore] (K n) :=
    (hA.stronglyMeasurable_stopped_jump_before_of_finiteVariation hF hcA
      hv.hasFiniteVariationPaths (hσ n).1).indicator (hE n)
  have hig (n : ℕ) : Integrable (g n) P :=
    hM.integrable_mul_stopped_jumpWithTerminal_of_integrable_of_bounded_martingale
      hF hcM C hC hb (hσ n) (Eventually.of_forall (hpos n)) (hiK n)
  have hmg (n : ℕ) : (∫ ω, g n ω ∂P) = 0 :=
    hM.integral_mul_stopped_jumpWithTerminal_eq_zero_of_integrable_of_bounded_martingale
      hF hcM C hC hb (hσ n) (Eventually.of_forall (hpos n)) (hmK n) (hiK n)
  have hd (ω : Ω) : ∀ i j (t : ℝ≥0),
      σ i ω = (t : WithTop ℝ≥0) → σ j ω = (t : WithTop ℝ≥0) → i = j := by
    intro i j t hi hj
    by_contra hij
    have hgi : (t, ω) ∈ stoppingTimeGraph (σ i) := hi
    have hgj : (t, ω) ∈ stoppingTimeGraph (σ j) := hj
    exact Set.disjoint_left.mp (hdisj hij) hgi hgj
  have htop (ω : Ω) (i : ℕ) (hi : σ i ω = ⊤) : g i ω = 0 := by
    change K i ω * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (σ i) ω = 0
    rw [stoppedValueWithTerminal_jump_eq_zero_of_top hi, mul_zero]
  have hcoe (ω : Ω) (i : ℕ) (t : ℝ≥0) (hi : σ i ω = (t : WithTop ℝ≥0)) :
      g i ω = (Ioc 0 T).indicator
        (fun u ↦ (M u ω - leftLim (M · ω) u) * (A u ω - leftLim (A · ω) u)) t := by
    have ht : 0 < t := by
      have hh := hpos i ω
      rw [hi] at hh
      exact WithTop.coe_lt_coe.mp hh
    have he : ω ∈ E i ↔ t ≤ T := by
      simp only [E, mem_ofPred_eq, hi, WithTop.coe_le_coe]
    by_cases htT : t ≤ T
    · have htmem : t ∈ Ioc 0 T := ⟨ht, htT⟩
      simp only [g, Pi.mul_apply, K, indicator_of_mem (he.mpr htT), indicator_of_mem htmem]
      rw [show JA i ω = jumpProcess A t ω from
          stoppedValueWithTerminal_jump_eq_of_eq_coe (X := A) hi,
        show JM i ω = jumpProcess M t ω from
          stoppedValueWithTerminal_jump_eq_of_eq_coe (X := M) hi]
      simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne']
      exact mul_comm (A t ω - leftLim (A · ω) t) (M t ω - leftLim (M · ω) t)
    · have htmem : t ∉ Ioc 0 T := fun h ↦ htT h.2
      simp only [g, Pi.mul_apply, K, indicator_of_notMem (mt he.mp htT), zero_mul,
        indicator_of_notMem htmem]
  let S (N : ℕ) (ω : Ω) := ∑ n ∈ Finset.range N, g n ω
  have hiS (N : ℕ) : Integrable (S N) P :=
    integrable_finsetSum (Finset.range N) (fun n _ ↦ hig n)
  have hmS (N : ℕ) : (∫ ω, S N ω ∂P) = 0 := by
    rw [show (∫ ω, S N ω ∂P) = ∑ n ∈ Finset.range N, ∫ ω, g n ω ∂P from
      integral_finsetSum _ (fun n _ ↦ hig n)]
    simp only [hmg, Finset.sum_const_zero]
  have hpath : ∀ᵐ ω ∂P,
      (∀ N, ‖S N ω‖ ≤ 2 * C * (eVariationOn (A · ω) univ).toReal) ∧
        Tendsto (fun N ↦ S N ω) atTop (𝓝 (Q T ω)) := by
    filter_upwards [hv.hasFiniteVariationPaths, hv.ae_eVariationOn_ne_top, hcA, hcM,
      hb, hcover, hSM.quadraticCovariation_of_finiteVariation_right hSA hF
        hv.hasFiniteVariationPaths, h0] with ω hvω hfin hcAω hcMω hbω hcoverω hQω h0ω
    have hcover' (t : ℝ≥0) (ht : 0 < t) (hj : A t ω - leftLim (A · ω) t ≠ 0) :
        ∃ i, σ i ω = (t : WithTop ℝ≥0) := by
      apply hcoverω t ht
      simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne'] using hj
    have hweight (t : ℝ≥0) (ht : t ∈ Ioc 0 T) :
        ‖M t ω - leftLim (M · ω) t‖ ≤ 2 * C := by
      simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.1.ne'] using
        hcMω.norm_jumpProcess_le_of_bound hbω t
    have hsabs := summable_abs_weighted_jumps_of_locallyBoundedVariation
      (x := (A · ω)) (f := fun t ↦ M t ω - leftLim (M · ω) t) hvω hcAω.1 T hweight
    have hsnorm : Summable (fun t : Ioc 0 T ↦
        ‖(M t ω - leftLim (M · ω) t) * (A t ω - leftLim (A · ω) t)‖) := by
      simpa only [Real.norm_eq_abs] using hsabs
    have hsum : Summable ((Ioc 0 T).indicator (fun t : ℝ≥0 ↦
        (M t ω - leftLim (M · ω) t) * (A t ω - leftLim (A · ω) t))) :=
      (summable_subtype_iff_indicator (s := Ioc 0 T)
        (f := fun t : ℝ≥0 ↦
          (M t ω - leftLim (M · ω) t) * (A t ω - leftLim (A · ω) t))).mp hsnorm.of_norm
    have hgSum : Summable (fun n ↦ g n ω) :=
      summable_of_disjoint_finite_lifetimes (hd ω) (htop ω) (hcoe ω) hsum
    have hseries := tsum_weighted_jumps_eq_tsum_of_disjoint_finite_lifetimes
      T (hd ω) (htop ω) (hcoe ω) hcover'
    have heQ : Q T ω = ∑' n, g n ω := by
      rw [show Q T ω = M 0 ω * A 0 ω +
        ∑' t : Ioc 0 T, jumpProcess M t ω * jumpProcess A t ω from hQω T,
        h0ω, Pi.zero_apply, mul_zero, zero_add]
      calc
        _ = ∑' t : Ioc 0 T,
            (M t ω - leftLim (M · ω) t) * (A t ω - leftLim (A · ω) t) := by
          apply tsum_congr
          intro t
          simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg t.property.1.ne']
        _ = _ := hseries
    refine ⟨fun N ↦ ?_, ?_⟩
    · simpa only [Real.norm_eq_abs, S] using
        abs_sum_mixed_jumps_le_of_disjoint_finite_lifetimes hcMω hvω hcAω.1 hfin T
          hC hbω (hd ω) (htop ω) (hcoe ω) (Finset.range N)
    · rw [heQ]
      exact hgSum.hasSum.tendsto_sum_nat
  have hiBound : Integrable (fun ω ↦ 2 * C * (eVariationOn (A · ω) univ).toReal) P :=
    hv.integrable_eVariationOn_toReal.const_mul (2 * C)
  have haQ : Adapted F Q := hSM.adapted_quadraticCovariation hSA hF
  have hmQ : Measurable (Q T) := (haQ T).mono (F.le T) le_rfl
  have hiQ : Integrable (Q T) P := by
    apply hiBound.mono' hmQ.aestronglyMeasurable
    filter_upwards [hpath] with ω hω
    exact le_of_tendsto hω.2.norm (Eventually.of_forall hω.1)
  have hmean := tendsto_integral_of_dominated_convergence
    (fun ω ↦ 2 * C * (eVariationOn (A · ω) univ).toReal)
    (fun N ↦ (hiS N).aestronglyMeasurable) hiBound
    (fun N ↦ hpath.mono fun _ hω ↦ hω.1 N) (hpath.mono fun _ hω ↦ hω.2)
  refine ⟨hiQ, tendsto_nhds_unique hmean ?_⟩
  simpa only [hmS] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LifetimeStepSeriesJump
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # First-moment budget for actual nonnegative jump corrections

If every actual finite corrected sum remains a supermartingale, its expected
correction is bounded by the initial expectation minus the current source
expectation. An original uniform lower bound on expectations therefore gives
one budget independent of the number of corrections.

The coefficients are nonnegative and vanish at infinite lifetimes. Dominated
convergence of each actual finite collection at integer times turns the
finite-time bound into a bound on the full coefficient moments. Nonnegative
real series then give absolute first-moment summability. This is a budget
lemma: it does not assume that arbitrary jump corrections preserve the
supermartingale property, nor assert a source decomposition from that premise.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual finite corrected supermartingales give a summable first-moment
budget for all nonnegative coefficients, with no chosen terminal process.
Infinite-lifetime coefficients must genuinely vanish for this conclusion. -/
theorem Supermartingale.summable_integral_norm_of_nonnegative_step_corrections
    (hX : Supermartingale X F P) (τ : ℕ → Ω → WithTop ℝ≥0) (K : ℕ → Ω → ℝ)
    (hi : ∀ n, Integrable (K n) P) (hn : ∀ n, 0 ≤ᵐ[P] K n)
    (hp : ∀ n ω, 0 < τ n ω) (htop : ∀ n, ∀ᵐ ω ∂P, τ n ω = ⊤ → K n ω = 0)
    (hM : ∀ N : ℕ, Supermartingale
      (X + fun (t : ℝ≥0) ω ↦ ∑ n ∈ Finset.range N,
        {v | τ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) F P)
    (C : ℝ) (hC : ∀ t, -(∫ ω, X t ω ∂P) ≤ C) :
    Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P) ∧
      (∑' n, ∫ ω, ‖K n ω‖ ∂P) ≤ (∫ ω, X 0 ω ∂P) + C := by
  classical
  let A : ℕ → ℝ≥0 → Ω → ℝ := fun N t ω ↦ ∑ n ∈ Finset.range N,
    {v | τ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  have hAi (N : ℕ) (t : ℝ≥0) : Integrable (A N t) P := by
    have hh := ((hM N).integrable t).sub (hX.integrable t)
    have he : (X + A N) t - X t = A N t := by
      funext ω
      exact add_sub_cancel_left (X t ω) (A N t ω)
    rwa [he] at hh
  have hA0 (N : ℕ) : A N 0 = 0 := by
    funext ω
    apply Finset.sum_eq_zero
    intro n _
    apply indicator_of_notMem
    exact not_le_of_gt (hp n ω)
  have hbound (N : ℕ) (t : ℝ≥0) :
      (∫ ω, A N t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) + C := by
    have he := integral_mono_ae integrable_condExp ((hM N).integrable 0)
      ((hM N).condExp_ae_le (show (0 : ℝ≥0) ≤ t from bot_le))
    rw [integral_condExp (F.le 0)] at he
    change (∫ ω, X t ω + A N t ω ∂P) ≤ ∫ ω, X 0 ω + A N 0 ω ∂P at he
    rw [hA0] at he
    simp only [Pi.zero_apply, add_zero] at he
    rw [integral_add (hX.integrable t) (hAi N t)] at he
    linarith [hC t]
  have hpartial (N : ℕ) :
      (∑ n ∈ Finset.range N, ∫ ω, ‖K n ω‖ ∂P) ≤ (∫ ω, X 0 ω ∂P) + C := by
    let G : Ω → ℝ := fun ω ↦ ∑ n ∈ Finset.range N, ‖K n ω‖
    have hiG : Integrable G P :=
      integrable_finsetSum _ (fun n _ ↦ (hi n).norm)
    have hb (m : ℕ) : ∀ᵐ ω ∂P, ‖A N (m : ℝ≥0) ω‖ ≤ G ω := by
      filter_upwards with ω
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ norm_indicator_le_norm_self _ _)
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun m : ℕ ↦ A N (m : ℝ≥0) ω) atTop (𝓝 (G ω)) := by
      filter_upwards [ae_all_iff.mpr hn, ae_all_iff.mpr htop] with ω hnω htω
      apply tendsto_finsetSum
      intro n _
      have hkn : ‖K n ω‖ = K n ω := Real.norm_of_nonneg (hnω n)
      rw [hkn]
      by_cases ht : τ n ω = ⊤
      · have hz := htω n ht
        have he (m : ℕ) :
            {v | τ n v ≤ ((m : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω = 0 := by
          apply indicator_of_notMem
          simpa only [mem_ofPred_eq, ht] using WithTop.not_top_le_coe (a := (m : ℝ≥0))
        simpa only [he, hz] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
      · obtain ⟨M, hMbound⟩ := exists_nat_ge (τ n ω).untopA
        apply tendsto_atTop_of_eventually_const (i₀ := M)
        intro m hm
        apply indicator_of_mem
        change τ n ω ≤ ((m : ℝ≥0) : WithTop ℝ≥0)
        have he : ((τ n ω).untopA : WithTop ℝ≥0) = τ n ω := by
          rw [WithTop.untopA_eq_untop ht, WithTop.coe_untop]
        rw [← he]
        exact WithTop.coe_le_coe.mpr (hMbound.trans (Nat.cast_le.mpr hm))
    have hconv := tendsto_integral_of_dominated_convergence G
      (fun m ↦ (hAi N (m : ℝ≥0)).aestronglyMeasurable) hiG hb hlim
    have hh := le_of_tendsto hconv (Eventually.of_forall fun m ↦ hbound N (m : ℝ≥0))
    rwa [integral_finsetSum _ (fun n _ ↦ (hi n).norm)] at hh
  have hnonneg (n : ℕ) : 0 ≤ ∫ ω, ‖K n ω‖ ∂P := integral_nonneg fun _ ↦ norm_nonneg _
  exact ⟨summable_of_sum_range_le hnonneg hpartial,
    Real.tsum_le_of_sum_range_le hnonneg hpartial⟩

end MeasureTheory

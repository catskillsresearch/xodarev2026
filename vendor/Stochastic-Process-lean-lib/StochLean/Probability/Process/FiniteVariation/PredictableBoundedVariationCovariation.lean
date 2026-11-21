/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.DisjointPredictableJumps
public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpBudget
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Probability.Process.Semimartingale.LocalMartingale
public import StochLean.Probability.Process.LocalMartingale.Congr
public import StochLean.Analysis.PathVariation.LifetimeJumpBudget

/-! # UI compensation of mixed jumps with a deterministic variation budget

The predictable jump cover and its actual jump coefficients are constructed
from the original FV process. A deterministic whole-half-line variation
bound gives the finite coefficient budgets required by the proved UI jump
series theorem. Reindexing the actual raw bracket identifies that series.

Only the centered raw bracket is asserted UI: the original initial product
is retained explicitly and need not be integrable. The test martingale is
UI, not bounded or square integrable. This is the bounded-variation step
toward local Yoeurp, not the general localization theorem itself.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter Set Function
open scoped NNReal ENNReal

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

/-- A UI martingale and a predictable FV process with a deterministic
variation budget have a UI centered actual raw covariation. -/
theorem isUIMartingale_centered_quadraticCovariation_of_variation_bound
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hv : HasFiniteVariationPaths A P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, eVariationOn (A · ω) univ ≤ ENNReal.ofReal C)
    (hM : IsUIMartingale M F P) (hcM : HasCadlagPaths M P) :
    IsUIMartingale
      (((hM.isLocalMartingale hcM).isSemimartingale hF).quadraticCovariation
        (hv.isSemimartingale hA.stronglyAdapted.adapted hF hcA) hF -
          fun _ ω ↦ M 0 ω * A 0 ω) F P := by
  classical
  let hSM := (hM.isLocalMartingale hcM).isSemimartingale hF
  let hSA := hv.isSemimartingale hA.stronglyAdapted.adapted hF hcA
  let Q := hSM.quadraticCovariation hSA hF
  change IsUIMartingale (Q - fun _ ω ↦ M 0 ω * A 0 ω) F P
  obtain ⟨σ, hσ, hpos, hdisj, hcover⟩ :=
    hA.exists_positive_disjoint_predictableStoppingTime_cover_jumps hF hcA hv
  let JA (n : ℕ) := stoppedValueWithTerminal (jumpProcess A) (fun _ ↦ (0 : ℝ)) (σ n)
  let JM (n : ℕ) := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (σ n)
  have hd (ω : Ω) : ∀ i j (t : ℝ≥0),
      σ i ω = (t : WithTop ℝ≥0) → σ j ω = (t : WithTop ℝ≥0) → i = j := by
    intro i j t hi hj
    by_contra hij
    have hgi : (t, ω) ∈ stoppingTimeGraph (σ i) := hi
    have hgj : (t, ω) ∈ stoppingTimeGraph (σ j) := hj
    exact Set.disjoint_left.mp (hdisj hij) hgi hgj
  have hmJA (n : ℕ) : StronglyMeasurable[(hσ n).1.measurableSpaceBefore] (JA n) :=
    hA.stronglyMeasurable_stopped_jump_before_of_finiteVariation hF hcA hv (hσ n).1
  have hbudget : ∀ᵐ ω ∂P, ∀ s : Finset ℕ, ∑ n ∈ s, ‖JA n ω‖ ≤ C := by
    filter_upwards [hv, hcA, hb] with ω hvω hcω hbω s
    have hfin : eVariationOn (A · ω) univ ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbω
    have h := sum_abs_jumps_le_global_variation_of_disjoint_finite_lifetimes
      hvω hcω.1 hfin (fun n ↦ hpos n ω) (hd ω)
      (fun n hn ↦ stoppedValueWithTerminal_jump_eq_zero_of_top (X := A) hn)
      (g := fun n ↦ JA n ω) (fun n t hn ↦ by
        have ht : 0 < t := WithTop.coe_lt_coe.mp (hn ▸ hpos n ω)
        rw [show JA n ω = jumpProcess A t ω from
          stoppedValueWithTerminal_jump_eq_of_eq_coe (X := A) hn]
        simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne']) s
    have hreal : (eVariationOn (A · ω) univ).toReal ≤ C := by
      simpa only [ENNReal.toReal_ofReal hC] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbω
    have h' : (∑ n ∈ s, ‖JA n ω‖) ≤ (eVariationOn (A · ω) univ).toReal := by
      simpa only [Real.norm_eq_abs] using h
    exact h'.trans hreal
  let J : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' n,
    {ω | σ n ω ≤ (t : WithTop ℝ≥0)}.indicator (JA n * JM n) ω
  have huJ : IsUIMartingale J F P :=
    hM.1.isUIMartingale_tsum_mul_stopped_jumpWithTerminal_of_predictable_budget
      hM.2 hF hcM hσ (fun n ↦ Eventually.of_forall (hpos n)) hmJA C hbudget
  have he : Indistinguishable J (Q - fun _ ω ↦ M 0 ω * A 0 ω) P := by
    filter_upwards [hcover, hSM.quadraticCovariation_of_finiteVariation_right hSA hF hv]
      with ω hcoverω hQω T
    let g (n : ℕ) :=
      {ω | σ n ω ≤ (T : WithTop ℝ≥0)}.indicator (JA n * JM n) ω
    have htop (n : ℕ) (hn : σ n ω = ⊤) : g n = 0 := by
      simp only [g, mem_ofPred_eq, hn, WithTop.top_le_iff,
        WithTop.coe_ne_top, not_false_eq_true, indicator_of_notMem]
    have hcoe (n : ℕ) (t : ℝ≥0) (hn : σ n ω = (t : WithTop ℝ≥0)) :
        g n = (Ioc 0 T).indicator
          (fun u ↦ (M u ω - leftLim (M · ω) u) * (A u ω - leftLim (A · ω) u)) t := by
      have ht : 0 < t := WithTop.coe_lt_coe.mp (hn ▸ hpos n ω)
      by_cases hbT : t ≤ T
      · rw [show g n = JA n ω * JM n ω from by
          simp only [g, mem_ofPred_eq, hn, WithTop.coe_le_coe, hbT,
            indicator_of_mem, Pi.mul_apply]]
        rw [show JA n ω = jumpProcess A t ω from
            stoppedValueWithTerminal_jump_eq_of_eq_coe (X := A) hn,
          show JM n ω = jumpProcess M t ω from
            stoppedValueWithTerminal_jump_eq_of_eq_coe (X := M) hn,
          indicator_of_mem (show t ∈ Ioc 0 T from ⟨ht, hbT⟩)]
        simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne']
        exact mul_comm _ _
      · have hg : g n = 0 := by
          simp only [g, mem_ofPred_eq, hn, WithTop.coe_le_coe, hbT,
            not_false_eq_true, indicator_of_notMem]
        rw [hg, indicator_of_notMem (show t ∉ Ioc 0 T from fun h ↦ hbT h.2)]
    have hseries := tsum_weighted_jumps_eq_tsum_of_disjoint_finite_lifetimes
      T (hd ω) htop hcoe (fun t ht hj ↦ hcoverω t ht (by
        simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne'] using hj))
    change (∑' n, g n) = Q T ω - M 0 ω * A 0 ω
    rw [show Q T ω = M 0 ω * A 0 ω +
      ∑' t : Ioc 0 T, jumpProcess M t ω * jumpProcess A t ω from hQω T,
      add_sub_cancel_left, ← hseries]
    apply tsum_congr
    intro t
    simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg t.property.1.ne']
  apply huJ.congr _ he
  intro t
  exact (hSM.adapted_quadraticCovariation hSA hF t).sub
    (((hSM.adapted 0).mul (hSA.adapted 0)).mono (F.mono bot_le) le_rfl)

end MeasureTheory.IsStronglyPredictable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Expectations of actual finite mixed sums

For two martingales, one bounded and the other only integrable, every raw
deterministic mixed sum is integrable and its expectation equals the terminal
product expectation. No L2 hypothesis on the second martingale is used.
The raw sum includes the initial product; the pure increment sum does not.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter Finset
open scoped NNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}

/-- Known-at-the-earlier-time multipliers preserve the martingale mean when
the actual later product is integrable. The earlier product's L1 is derived. -/
theorem integrable_mul_and_integral_eq_of_stronglyMeasurable
    (hM : Martingale M F P) {s t : ℝ≥0} (hst : s ≤ t) {K : Ω → ℝ}
    (hK : StronglyMeasurable[F s] K) (hi : Integrable (K * M t) P) :
    Integrable (K * M s) P ∧ (∫ ω, K ω * M t ω ∂P) = ∫ ω, K ω * M s ω ∂P := by
  have he : P[K * M t | F s] =ᵐ[P] K * M s :=
    (condExp_mul_of_stronglyMeasurable_left hK hi (hM.integrable t)).trans
      (EventuallyEq.rfl.mul (hM.condExp_ae_eq hst))
  refine ⟨integrable_condExp.congr he, ?_⟩
  exact (integral_condExp (F.le s)).symm.trans (integral_congr_ae he)

/-- The raw finite mixed sum has terminal-product mean, with no second
moment assumption on the second martingale and no zero-initial convention. -/
theorem integrable_raw_covariationSum_and_integral_eq
    (hM : Martingale M F P) (hA : Martingale A F P) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) {T : ℝ≥0} (π : TimePartition T) :
    Integrable (fun ω ↦ M 0 ω * A 0 ω + covariationSum π (M · ω) (A · ω)) P ∧
      (∫ ω, M 0 ω * A 0 ω + covariationSum π (M · ω) (A · ω) ∂P) =
        ∫ ω, M T ω * A T ω ∂P := by
  have hi (s t : ℝ≥0) : Integrable (fun ω ↦ M s ω * A t ω) P := by
    apply ((hA.integrable t).norm.const_mul C).mono'
      ((hM.integrable s).aestronglyMeasurable.mul (hA.integrable t).aestronglyMeasurable)
    filter_upwards [hb] with ω hω
    change ‖M s ω * A t ω‖ ≤ C * ‖A t ω‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hω s) (norm_nonneg _)
  have hm (s t : ℝ≥0) (hst : s ≤ t) :
      (∫ ω, M t ω * A s ω ∂P) = ∫ ω, M s ω * A s ω ∂P := by
    have hprod : Integrable (A s * M t) P := (hi t s).congr
      (Eventually.of_forall fun ω ↦ mul_comm _ _)
    simpa only [mul_comm] using
      (hM.integrable_mul_and_integral_eq_of_stronglyMeasurable hst (hA.stronglyAdapted s) hprod).2
  have ha (s t : ℝ≥0) (hst : s ≤ t) :
      (∫ ω, M s ω * A t ω ∂P) = ∫ ω, M s ω * A s ω ∂P :=
    (hA.integrable_mul_and_integral_eq_of_stronglyMeasurable hst (hM.stronglyAdapted s) (hi s t)).2
  let U (i : Fin π.size) (ω : Ω) := π.increment (M · ω) i * π.increment (A · ω) i
  have he (i : Fin π.size) : U i =
      ((fun ω ↦ M (π.right i) ω * A (π.right i) ω) -
        (fun ω ↦ M (π.right i) ω * A (π.left i) ω) -
        (fun ω ↦ M (π.left i) ω * A (π.right i) ω)) +
        (fun ω ↦ M (π.left i) ω * A (π.left i) ω) := by
    funext ω
    simp only [U, TimePartition.increment, Pi.add_apply, Pi.sub_apply]
    ring
  have hiU (i : Fin π.size) : Integrable (U i) P := by
    rw [he i]
    exact (((hi _ _).sub (hi _ _)).sub (hi _ _)).add (hi _ _)
  have hmean (i : Fin π.size) : (∫ ω, U i ω ∂P) =
      (∫ ω, M (π.right i) ω * A (π.right i) ω ∂P) -
        ∫ ω, M (π.left i) ω * A (π.left i) ω ∂P := by
    have h1 := integral_add
      (((hi (π.right i) (π.right i)).sub (hi (π.right i) (π.left i))).sub
        (hi (π.left i) (π.right i))) (hi (π.left i) (π.left i))
    have h2 := integral_sub
      ((hi (π.right i) (π.right i)).sub (hi (π.right i) (π.left i)))
      (hi (π.left i) (π.right i))
    have h3 := integral_sub (hi (π.right i) (π.right i)) (hi (π.right i) (π.left i))
    simp only [Pi.sub_apply] at h1 h2 h3
    rw [he i]
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [h1, h2, h3, hm _ _ (π.left_le_right i), ha _ _ (π.left_le_right i)]
    ring
  have hiSum : Integrable (fun ω ↦ ∑ i, U i ω) P :=
    integrable_finsetSum univ (fun i _ ↦ hiU i)
  refine ⟨(hi 0 0).add hiSum, ?_⟩
  change (∫ ω, M 0 ω * A 0 ω + ∑ i, U i ω ∂P) = _
  rw [integral_add (hi 0 0) hiSum, integral_finsetSum _ (fun i _ ↦ hiU i)]
  simp_rw [hmean]
  have ht := π.sum_increment (fun t ↦ ∫ ω, M t ω * A t ω ∂P)
  change (∑ i, ((∫ ω, M (π.right i) ω * A (π.right i) ω ∂P) -
    ∫ ω, M (π.left i) ω * A (π.left i) ω ∂P)) = _ at ht
  rw [ht]
  ring

end MeasureTheory.Martingale

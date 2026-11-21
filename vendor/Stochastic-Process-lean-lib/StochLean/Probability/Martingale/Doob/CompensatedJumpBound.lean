/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableCompensatorJump
public import StochLean.Probability.Process.FiniteVariation.DisjointPredictableJumps
public import StochLean.Probability.Process.FiniteVariation.CompensatorIntegrable
public import StochLean.Probability.Process.Path.LeftLimitAddition
public import StochLean.Probability.Process.LocalMartingale.Reducing
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Actual jump bounds after compensating a removed process

For a UI martingale M and an actual predictable IV compensator B of A, the
jump of B at a positive predictable lifetime is the negative before-field
conditional mean of the jump of M - A. Integrability follows first from the
two actual UI jump theorems; it is not inferred from a default integral.

A common bound beta on the positive-time jumps of M - A therefore bounds
the jumps of B by beta. The actual predictable FV jump cover gives this on
one common event for all positive times. The compensated residual M - A + B
then has jump norm at most twice beta. No process-value bound, semimartingale
assumption, section theorem, or initial-jump bound is used. Infinite sampling
lifetimes always contribute the explicit terminal zero.

The final consumer constructs B from the actual integrable-variation source
theorem and also proves that the compensated residual is a true UI martingale.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A B : ℝ≥0 → Ω → ℝ} {γ : Ω → WithTop ℝ≥0}

/-- The actual compensator jump is the negative conditional residual jump.
Only a jump bound is assumed, including no bound on the source values. -/
theorem IsUIMartingale.compensator_stopped_jump_eq_neg_condExp_of_residual_jump_bound
    (hM : IsUIMartingale M F P) (hU : IsUIMartingale (A - B) F P)
    (hF : F.IsUsual P) (hcM : HasCadlagPaths M P) (hcA : HasCadlagPaths A P)
    (hcB : HasCadlagPaths B P) (hpB : IsStronglyPredictable F B)
    (hvB : HasIntegrableVariation B P) (β : ℝ) (hβ : 0 ≤ β)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (M - A) t ω‖ ≤ β)
    (hγ : IsPredictableStoppingTime F γ P) (hpos : ∀ᵐ ω ∂P, 0 < γ ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess (M - A)) (fun _ ↦ (0 : ℝ)) γ) P ∧
      (stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ =ᵐ[P]
        fun ω ↦ -P[stoppedValueWithTerminal (jumpProcess (M - A))
          (fun _ ↦ (0 : ℝ)) γ | hγ.1.measurableSpaceBefore] ω) ∧
      ∀ᵐ ω ∂P,
        ‖stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ ω‖ ≤ β := by
  let JM := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) γ
  let JA := stoppedValueWithTerminal (jumpProcess A) (fun _ ↦ (0 : ℝ)) γ
  let JB := stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ
  let JR := stoppedValueWithTerminal (jumpProcess (M - A)) (fun _ ↦ (0 : ℝ)) γ
  obtain ⟨hiM, hzM⟩ :=
    hM.1.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
      hM.2 hF hcM hγ hpos
  obtain ⟨hiA, hceB⟩ :=
    hU.1.integrable_stopped_jump_and_compensator_condExp_before
      hU.2 hF hcA hcB hpB hvB hγ hpos
  have he : JR =ᵐ[P] JM - JA := by
    filter_upwards [hcM, hcA] with ω hm ha
    by_cases ht : γ ω = ⊤
    · simp only [JR, JM, JA, stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
    · simp only [JR, JM, JA, stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
      exact hm.jumpProcess_sub ha (γ ω).untopA
  have hiR : Integrable JR P := (hiM.sub hiA).congr he.symm
  have hEq : JB =ᵐ[P] fun ω ↦ -P[JR | hγ.1.measurableSpaceBefore] ω := by
    filter_upwards [hceB, hzM, condExp_congr_ae he,
      condExp_sub hiM hiA hγ.1.measurableSpaceBefore] with ω hb hz heω hlin
    have hz' : P[JM | hγ.1.measurableSpaceBefore] ω = 0 := hz
    rw [heω, hlin]
    change JB ω = -(P[JM | hγ.1.measurableSpaceBefore] ω -
      P[JA | hγ.1.measurableSpaceBefore] ω)
    simpa only [hz', zero_sub, neg_neg] using hb
  have hRb : ∀ᵐ ω ∂P, ‖JR ω‖ ≤ β := by
    filter_upwards [hR, hpos] with ω hr hp
    cases ht : γ ω with
    | top =>
      rw [show JR ω = 0 from stoppedValueWithTerminal_jump_eq_zero_of_top ht, norm_zero]
      exact hβ
    | coe t =>
      rw [show JR ω = jumpProcess (M - A) t ω from
        stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
      exact hr t (WithTop.coe_lt_coe.mp (ht ▸ hp))
  have hceBound : ∀ᵐ ω ∂P, ‖P[JR | hγ.1.measurableSpaceBefore] ω‖ ≤ β :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hRb
  refine ⟨hiR, hEq, ?_⟩
  filter_upwards [hEq, hceBound] with ω heω hb
  change ‖JB ω‖ ≤ β
  rw [heω, norm_neg]
  exact hb

/-- Actual predictable jump coverage turns predictable-time conditional
estimates into common all-positive-time bounds for B and M - A + B. -/
theorem IsUIMartingale.ae_norm_jumps_compensator_and_compensated_le
    (hM : IsUIMartingale M F P) (hU : IsUIMartingale (A - B) F P)
    (hF : F.IsUsual P) (hcM : HasCadlagPaths M P) (hcA : HasCadlagPaths A P)
    (hcB : HasCadlagPaths B P) (hpB : IsStronglyPredictable F B)
    (hvB : HasIntegrableVariation B P) (β : ℝ) (hβ : 0 ≤ β)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (M - A) t ω‖ ≤ β) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ‖jumpProcess B t ω‖ ≤ β ∧ ‖jumpProcess ((M - A) + B) t ω‖ ≤ 2 * β := by
  obtain ⟨ρ, hρ, hpρ, _, hcover⟩ :=
    hpB.exists_positive_disjoint_predictableStoppingTime_cover_jumps
      hF hcB hvB.hasFiniteVariationPaths
  have hsample (n : ℕ) : ∀ᵐ ω ∂P,
      ‖stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) (ρ n) ω‖ ≤ β :=
    (hM.compensator_stopped_jump_eq_neg_condExp_of_residual_jump_bound hU hF hcM hcA
      hcB hpB hvB β hβ hR (hρ n) (Eventually.of_forall (hpρ n))).2.2
  have hBound : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess B t ω‖ ≤ β := by
    filter_upwards [hcover, ae_all_iff.mpr hsample] with ω hω hs t ht
    by_cases hj : jumpProcess B t ω = 0
    · rw [hj, norm_zero]
      exact hβ
    · obtain ⟨n, hn⟩ := hω t ht hj
      have hh := hs n
      rwa [stoppedValueWithTerminal_jump_eq_of_eq_coe hn] at hh
  filter_upwards [hcM.sub hcA, hcB, hBound, hR] with ω hr hb hB hRω t ht
  refine ⟨hB t ht, ?_⟩
  rw [hr.jumpProcess_add hb t]
  calc
    ‖jumpProcess (M - A) t ω + jumpProcess B t ω‖ ≤
        ‖jumpProcess (M - A) t ω‖ + ‖jumpProcess B t ω‖ := norm_add_le _ _
    _ ≤ β + β := add_le_add (hRω t ht) (hB t ht)
    _ = 2 * β := (two_mul β).symm

/-- Construct the actual compensator and a bounded-jump true UI residual.
Initial integrability is retained because the uncentered remainder A - B
is asserted to be a true UI martingale, not merely a local martingale. -/
theorem IsUIMartingale.exists_predictable_compensator_with_residual_jump_bound
    (hM : IsUIMartingale M F P) (hF : F.IsUsual P) (hcM : HasCadlagPaths M P)
    (hvA : HasIntegrableVariation A P) (haA : Adapted F A) (hcA : HasCadlagPaths A P)
    (hiA0 : Integrable (A 0) P) (β : ℝ) (hβ : 0 ≤ β)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (M - A) t ω‖ ≤ β) :
    ∃ B : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F B ∧ (∀ ω, IsCadlagPath (B · ω)) ∧ B 0 = 0 ∧
      HasIntegrableVariation B P ∧ IsUIMartingale (A - B) F P ∧
      IsUIMartingale ((M - A) + B) F P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
        ‖jumpProcess B t ω‖ ≤ β ∧ ‖jumpProcess ((M - A) + B) t ω‖ ≤ 2 * β := by
  obtain ⟨B, hpB, hcB, hB0, hvB, hU, _, _⟩ :=
    hvA.exists_unique_predictable_compensator haA hF hcA hiA0
  have he : (M - A) + B = M - (A - B) := by
    funext t ω
    change (M t ω - A t ω) + B t ω = M t ω - (A t ω - B t ω)
    ring
  have hC : IsUIMartingale ((M - A) + B) F P := he.symm ▸ hM.sub hU
  exact ⟨B, hpB, hcB, hB0, hvB, hU, hC,
    hM.ae_norm_jumps_compensator_and_compensated_le hU hF hcM hcA
      (Eventually.of_forall hcB) hpB hvB β hβ hR⟩

end ProbabilityTheory

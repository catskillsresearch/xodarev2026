/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Special
public import StochLean.Probability.Process.FiniteVariation.BoundedJumpLocalization
public import StochLean.Probability.Martingale.Doob.CompensatedJumpBoundLocal

/-! # Protter III.35: bounded-jump classical semimartingales are special

The actual fundamental decomposition first supplies a bounded-jump local
martingale from the original classical martingale part. Subtracting it from
the centered original process produces an adapted cadlag finite-variation
process with bounded jumps, hence actual locally integrable variation.

The existing local compensator construction is applied to its negative.
This gives a predictable part with the original jump bound and a local
martingale part with twice that bound. Both new components start at exactly
zero, and their reconstruction is an exact process equality. The arbitrary
original initial random value stays outside the two components.

No initial moment, proposed predictable decomposition, or converse from the
good-integrator predicate to the classical source predicate is assumed.
All jump estimates exclude time zero and hold on a common path event.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- Actual normalized predictable decomposition with sharp predictable jump
bound `C` and local-martingale jump bound `2 * C`. The predictable part has
locally integrable variation, not merely local finite variation. -/
theorem IsClassicalSemimartingale.exists_predictable_decomposition_of_jump_bound
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P) (hC : 0 ≤ C)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C) :
    ∃ L A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale L F P ∧ IsStronglyPredictable F A ∧
      (∀ ω, IsCadlagPath (A · ω)) ∧ L 0 = 0 ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧ X = (fun _ ↦ X 0) + L + A ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
        ‖jumpProcess A t ω‖ ≤ C ∧ ‖jumpProcess L t ω‖ ≤ 2 * C := by
  obtain ⟨ha, hc, M, A, hM, _, _, hvA, _, _, he⟩ := hX
  obtain ⟨N, D, hN, _, _, _, hvD, hsplit, hjN, _⟩ :=
    hM.exists_fundamental_decomposition_of_pos hF (β := 1) zero_lt_one
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let J := X - I
  have hI : IsContinuousLocalMartingale I F P :=
    isContinuousLocalMartingale_const_initial (ha 0)
  have haJ : Adapted F J := ha.sub hI.1.1
  have hcJ : HasCadlagPaths J P := hc.sub hI.2.hasCadlagPaths
  have hjJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess J t ω‖ ≤ C := by
    filter_upwards [hc, hj] with ω hcω hω t ht
    have hcI : IsCadlagPath (I · ω) :=
      IsContinuousPath.isCadlagPath continuous_const
    have hi : jumpProcess I t ω = 0 :=
      IsContinuousPath.jumpProcess_eq_zero (X := I) (ω := ω)
        (show Continuous (I · ω) from continuous_const) (ne_of_gt ht)
    change ‖jumpProcess (X - I) t ω‖ ≤ C
    rw [hcω.jumpProcess_sub hcI t, hi, sub_zero]
    exact hω t ht
  let E := J - N
  have haE : Adapted F E := haJ.sub hN.1
  have hcE : HasCadlagPaths E P := hcJ.sub hN.2.1
  have hvDA : HasFiniteVariationPaths (D + A) P := by
    filter_upwards [hvD.hasFiniteVariationPaths, hvA] with ω hd haω
    exact StochLean.locallyBoundedVariationOn_add hd haω
  have heE : Indistinguishable (D + A) E P := by
    filter_upwards [he] with ω hω t
    have ht := hω t
    have hm := congrFun (congrFun hsplit t) ω
    change X t ω = (X 0 ω + M t ω) + A t ω at ht
    change M t ω = N t ω + D t ω at hm
    change D t ω + A t ω = (X t ω - X 0 ω) - N t ω
    linarith only [ht, hm]
  have hvE : HasFiniteVariationPaths E P := HasFiniteVariationPaths.congr heE hvDA
  have hjE : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess E t ω‖ ≤ C + 2 := by
    filter_upwards [hcJ, hN.2.1, hjJ, hjN] with ω hcJω hcNω hJω hNω t ht
    change ‖jumpProcess (J - N) t ω‖ ≤ C + 2
    rw [hcJω.jumpProcess_sub hcNω t]
    exact (norm_sub_le _ _).trans (add_le_add (hJω t ht)
      (by simpa only [mul_one] using hNω t ht))
  have hvEi : HasLocallyIntegrableVariation E F P :=
    hvE.hasLocallyIntegrableVariation_of_jump_bound haE hF hcE (by positivity) hjE
  have heN : N - (-E) = J := by
    funext t ω
    change N t ω - - (J t ω - N t ω) = J t ω
    ring
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (N - (-E)) t ω‖ ≤ C := by
    rw [heN]
    exact hjJ
  obtain ⟨B, hpB, hcB, hB0, hvB, _, hL, hjB⟩ :=
    hN.exists_predictable_compensator_with_residual_jump_bound hF hvEi.neg
      (fun t ↦ (haE t).neg) (hcE.continuous_comp continuous_neg) C hC hR
  rw [heN] at hL hjB
  let L := J + B
  have hL0 : L 0 = 0 := by
    change X 0 - X 0 + B 0 = 0
    rw [sub_self, hB0, add_zero]
  have hNeg0 : (-B) 0 = 0 := by
    change -B 0 = 0
    rw [hB0, neg_zero]
  have heExact : X = (fun _ ↦ X 0) + L + -B := by
    funext t ω
    change X t ω = (X 0 ω + (X t ω - X 0 ω + B t ω)) + -B t ω
    ring
  refine ⟨L, -B, hL, hpB.neg, (fun ω ↦ (hcB ω).continuous_comp continuous_neg),
    hL0, hNeg0, hvB.neg, heExact, ?_⟩
  filter_upwards [hjB] with ω hω t ht
  refine ⟨?_, (hω t ht).2⟩
  have hn : jumpProcess (-B) t ω = -jumpProcess B t ω := by
    change jumpProcess (fun s v ↦ -B s v) t ω = -jumpProcess B t ω
    simpa only [neg_one_mul] using (hcB ω).jumpProcess_const_mul (-1) t
  rw [hn, norm_neg]
  exact (hω t ht).1

/-- Protter III.35 for the classical source domain, obtained by the actual
predictable decomposition rather than assuming specialness. -/
theorem IsClassicalSemimartingale.isSpecialSemimartingale_of_jump_bound
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P) (hC : 0 ≤ C)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C) :
    IsSpecialSemimartingale X F P := by
  obtain ⟨L, A, hL, hpA, hcA, hL0, hA0, hvA, he, _⟩ :=
    hX.exists_predictable_decomposition_of_jump_bound hF hC hj
  exact ⟨hX.1, hX.2.1, L, A, hL, hpA, Eventually.of_forall hcA,
    hvA.hasFiniteVariationPaths, Eventually.of_forall (fun ω ↦ congrFun hL0 ω),
    Eventually.of_forall (fun ω ↦ congrFun hA0 ω),
    Eventually.of_forall (fun ω t ↦ congrFun (congrFun he t) ω)⟩

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularConditionalJump
public import StochLean.Probability.Martingale.Doob.PredictableCompensatorJump
public import StochLean.Probability.Process.FiniteVariation.DisjointPredictableJumps
public import StochLean.Probability.Process.Path.LeftLimitAddition
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Bounded jumps after removal from a regular process

Suppose the predictable integrable-variation process `B` compensates `J`, the
original process `X` has zero expected jumps at every positive predictable
lifetime, and the actual residual `X - J` is bounded by `C` on one path event.
At each such lifetime, integrability is first proved for all actual sampled
jumps. The regularity tests then identify the conditional mean of the jump of
`X` as zero. Consequently the jump of `B` is the negative conditional mean of
the residual jump and has norm at most `2 * C`.

The actual predictable FV jump cover upgrades these countably many stopping-
time bounds to one common event supporting the bound at every positive time.
The compensated residual has jump norm at most `4 * C` on the same event.
No amplitude restriction is presumed to preserve centering, and the residual
is not assumed to have totally inaccessible jumps. All lifetime evaluations
use explicit terminal zero at infinity. Martingale, Class D, and regularity
properties of the compensated residual are not asserted in this module.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X J B : ℝ≥0 → Ω → ℝ} {γ : Ω → WithTop ℝ≥0}

/-- Actual sampled-jump integrability precedes the conditional-centering
argument. The bounded residual, not any jump-amplitude restriction, controls
the predictable compensator jump. Infinite lifetimes have terminal value zero. -/
theorem compensator_stopped_jump_eq_neg_condExp_of_regular_residual_bound
    (hM : Martingale (J - B) F P) (hu : UniformIntegrable (J - B) 1 P)
    (hF : F.IsUsual P) (haX : Adapted F X) (haJ : Adapted F J)
    (hcX : HasCadlagPaths X P) (hcJ : HasCadlagPaths J P) (hcB : HasCadlagPaths B P)
    (hpB : IsStronglyPredictable F B) (hvB : HasIntegrableVariation B P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (C : ℝ) (hb : ∀ᵐ ω ∂P, ∀ t, ‖(X - J) t ω‖ ≤ C)
    (hγ : IsPredictableStoppingTime F γ P) (hpos : ∀ᵐ ω ∂P, 0 < γ ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ) P ∧
      (stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ =ᵐ[P]
        fun ω ↦ -P[stoppedValueWithTerminal (jumpProcess (X - J))
          (fun _ ↦ (0 : ℝ)) γ | hγ.1.measurableSpaceBefore] ω) ∧
      ∀ᵐ ω ∂P,
        ‖stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ ω‖ ≤ 2 * C := by
  let R : ℝ≥0 → Ω → ℝ := X - J
  let JR := stoppedValueWithTerminal (jumpProcess R) (fun _ ↦ (0 : ℝ)) γ
  let JX := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ
  let JJ := stoppedValueWithTerminal (jumpProcess J) (fun _ ↦ (0 : ℝ)) γ
  let JB := stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ
  have haR : Adapted F R := fun t ↦ (haX t).sub (haJ t)
  have hcR : HasCadlagPaths R P := hcX.sub hcJ
  have hRb : ∀ᵐ ω ∂P, ‖JR ω‖ ≤ 2 * C :=
    (hcR.ae_forall_norm_stopped_jump_le_of_bound hb (fun _ : Unit ↦ γ)).mono
      fun _ hω ↦ hω ()
  have hiR : Integrable JR P :=
    (integrable_const (2 * C)).mono'
      (((haR.stronglyMeasurable_stopped_jump_of_usual hF hcR hγ.1).mono
        hγ.1.measurableSpace_le).aestronglyMeasurable) hRb
  obtain ⟨hiJ, hceB⟩ :=
    hM.integrable_stopped_jump_and_compensator_condExp_before hu hF hcJ hcB hpB hvB hγ hpos
  have he : JR =ᵐ[P] JX - JJ := by
    filter_upwards [hcX, hcJ] with ω hx hj
    by_cases ht : γ ω = ⊤
    · simp only [JR, JX, JJ, stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
    · simp only [JR, R, JX, JJ, stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
      exact hx.jumpProcess_sub hj (γ ω).untopA
  have hiX : Integrable JX P := (hiR.add hiJ).congr (by
    filter_upwards [he] with ω hω
    change JR ω + JJ ω = JX ω
    simpa only [Pi.sub_apply, sub_add_cancel] using congrArg (fun x ↦ x + JJ ω) hω)
  have hz := condExp_stopped_jump_before_ae_eq_zero_of_predictable_jump_mean_zero
    hF hreg hγ hpos hiX
  have hEq : JB =ᵐ[P] fun ω ↦ -P[JR | hγ.1.measurableSpaceBefore] ω := by
    filter_upwards [hceB, hz, condExp_congr_ae he,
      condExp_sub hiX hiJ hγ.1.measurableSpaceBefore] with ω hbω hzω heω hlin
    have hz' : P[JX | hγ.1.measurableSpaceBefore] ω = 0 := hzω
    rw [heω, hlin]
    change JB ω = -(P[JX | hγ.1.measurableSpaceBefore] ω -
      P[JJ | hγ.1.measurableSpaceBefore] ω)
    simpa only [hz', zero_sub, neg_neg] using hbω
  refine ⟨hiX, hEq, ?_⟩
  have hceBound : ∀ᵐ ω ∂P, ‖P[JR | hγ.1.measurableSpaceBefore] ω‖ ≤ 2 * C :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hRb
  filter_upwards [hEq, hceBound] with ω heω hbω
  change ‖JB ω‖ ≤ 2 * C
  rw [heω, norm_neg]
  exact hbω

/-- The actual predictable FV jump cover yields a common all-positive-time
bound for both the compensator and the compensated residual. The constants
come from the original residual path bound, not an assumed jump bound. -/
theorem ae_norm_jumps_compensator_and_removed_le_of_regular_residual_bound
    (hM : Martingale (J - B) F P) (hu : UniformIntegrable (J - B) 1 P)
    (hF : F.IsUsual P) (haX : Adapted F X) (haJ : Adapted F J)
    (hcX : HasCadlagPaths X P) (hcJ : HasCadlagPaths J P) (hcB : HasCadlagPaths B P)
    (hpB : IsStronglyPredictable F B) (hvB : HasIntegrableVariation B P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖(X - J) t ω‖ ≤ C) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ‖jumpProcess B t ω‖ ≤ 2 * C ∧ ‖jumpProcess ((X - J) + B) t ω‖ ≤ 4 * C := by
  obtain ⟨ρ, hρ, hpρ, _, hcover⟩ :=
    hpB.exists_positive_disjoint_predictableStoppingTime_cover_jumps
      hF hcB hvB.hasFiniteVariationPaths
  have hsample (n : ℕ) : ∀ᵐ ω ∂P,
      ‖stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) (ρ n) ω‖ ≤ 2 * C :=
    (hM.compensator_stopped_jump_eq_neg_condExp_of_regular_residual_bound
      hu hF haX haJ hcX hcJ hcB hpB hvB hreg C hb (hρ n)
      (ae_of_all _ (hpρ n))).2.2
  have hBbound : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess B t ω‖ ≤ 2 * C := by
    filter_upwards [hcover, ae_all_iff.mpr hsample] with ω hcoverω hsω t ht
    by_cases hj : jumpProcess B t ω = 0
    · rw [hj, norm_zero]
      exact mul_nonneg (by norm_num) hC
    · obtain ⟨n, hn⟩ := hcoverω t ht hj
      have hh := hsω n
      rwa [stoppedValueWithTerminal_jump_eq_of_eq_coe hn] at hh
  have hRbound := (hcX.sub hcJ).ae_norm_jumpProcess_le_of_bound hb
  filter_upwards [hcX.sub hcJ, hcB, hBbound, hRbound] with ω hr hbω hBω hRω t ht
  refine ⟨hBω t ht, ?_⟩
  rw [hr.jumpProcess_add hbω t]
  calc
    ‖jumpProcess (X - J) t ω + jumpProcess B t ω‖ ≤
        ‖jumpProcess (X - J) t ω‖ + ‖jumpProcess B t ω‖ := norm_add_le _ _
    _ ≤ 2 * C + 2 * C := add_le_add (hRω t) (hBω t ht)
    _ = 4 * C := by ring

end MeasureTheory.Martingale

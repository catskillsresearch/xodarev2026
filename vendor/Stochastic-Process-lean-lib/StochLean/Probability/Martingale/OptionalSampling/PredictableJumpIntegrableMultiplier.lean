/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpUI
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import StochLean.Probability.Process.Stopping.JumpCoefficients
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Integrable before-field multipliers of bounded martingale jumps

A globally bounded cadlag martingale is UI by the existing bounded local
martingale theorem. At an almost surely finite positive predictable time,
its actual jump is integrable and has zero conditional mean by the existing
UI predictable sampling theorem.

The common cadlag jump bound gives a `2 * C` bound for that actual stopped
jump. An arbitrary integrable coefficient is therefore enough for product
integrability; no boundedness or L2 assumption on the coefficient is needed.
Before-field measurability then gives zero conditional mean and expectation
by native conditional-expectation pull-out.

The explicit terminal-valued sampling bound is converted to finite stopping
evaluation only on the almost-sure finite event. Nothing here asserts a
finite-time evaluation or zero jump at an infinite stopping time, and these
single-time results do not assert a general Yoeurp theorem.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {K : Ω → ℝ}

/-- The actual jump is bounded by `2 * C` on the common finite-lifetime
event, so an integrable coefficient suffices for an integrable product. -/
theorem integrable_mul_stopped_jump_of_integrable_of_bounded_martingale
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hiK : Integrable K P) :
    Integrable (K * stoppedValue (jumpProcess M) τ) P := by
  have hu : UniformIntegrable M 1 P :=
    ((hM.isLocalMartingale hc).isUIMartingale_of_bound ⟨C, hC⟩ hb).2
  have hiJ := hM.integrable_stopped_jump_of_predictable_of_ae_finite
    hu hF hc hτ hpos hfinite
  have hJb : ∀ᵐ ω ∂P, ‖stoppedValue (jumpProcess M) τ ω‖ ≤ 2 * C := by
    filter_upwards [hc.ae_forall_norm_stopped_jump_le_of_bound hb (fun _ : Unit ↦ τ),
      hfinite] with ω hω hfin
    have hh := hω ()
    rwa [stoppedValueWithTerminal_of_ne_top hfin] at hh
  apply (hiK.norm.const_mul (2 * C)).mono'
    (hiK.aestronglyMeasurable.mul hiJ.aestronglyMeasurable)
  filter_upwards [hJb] with ω hω
  change ‖K ω * stoppedValue (jumpProcess M) τ ω‖ ≤ 2 * C * ‖K ω‖
  rw [norm_mul, mul_comm (2 * C)]
  exact mul_le_mul_of_nonneg_left hω (norm_nonneg _)

/-- An integrable coefficient known before the predictable time preserves
zero conditional jump mean; boundedness is imposed on the martingale only. -/
theorem condExp_mul_stopped_jump_before_ae_eq_zero_of_integrable_of_bounded_martingale
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K) (hiK : Integrable K P) :
    P[K * stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  have hu : UniformIntegrable M 1 P :=
    ((hM.isLocalMartingale hc).isUIMartingale_of_bound ⟨C, hC⟩ hb).2
  have hiJ := hM.integrable_stopped_jump_of_predictable_of_ae_finite
    hu hF hc hτ hpos hfinite
  have hip := hM.integrable_mul_stopped_jump_of_integrable_of_bounded_martingale
    hF hc C hC hb hτ hpos hfinite hiK
  have hout := condExp_mul_of_stronglyMeasurable_left hK hip hiJ
  have hz := hM.condExp_stopped_jump_before_ae_eq_zero_of_predictable_of_ae_finite
    hu hF hc hτ hpos hfinite
  filter_upwards [hout, hz] with ω hp hω
  change P[K * stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] ω = 0
  rw [hp]
  change K ω * P[stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] ω = 0
  rw [hω, Pi.zero_apply, mul_zero]

/-- The genuine integrable weighted jump has zero expectation. -/
theorem integral_mul_stopped_jump_eq_zero_of_integrable_of_bounded_martingale
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K) (hiK : Integrable K P) :
    (∫ ω, K ω * stoppedValue (jumpProcess M) τ ω ∂P) = 0 := by
  have hz := hM.condExp_mul_stopped_jump_before_ae_eq_zero_of_integrable_of_bounded_martingale
    hF hc C hC hb hτ hpos hfinite hK hiK
  calc
    (∫ ω, K ω * stoppedValue (jumpProcess M) τ ω ∂P) =
        ∫ ω, P[K * stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] ω ∂P :=
      (integral_condExp hτ.1.measurableSpaceBefore_le_ambient).symm
    _ = 0 := by
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hz

end MeasureTheory.Martingale

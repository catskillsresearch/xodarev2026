/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Martingale.OptionalSampling.AnnouncingBefore
public import StochLean.Probability.Process.Stopping.AnnouncingStability

/-! # Conditional jump mean at a bounded predictable stopping time

Actual bounded optional sampling identifies the values along an announcing
sequence with conditional expectations of the stopped martingale. Native
Levy upward convergence and the announcing sigma-field identity identify
their limit with the conditional expectation strictly before the target.
The cadlag left limit identifies that same limit pathwise.

This proves integrability of the actual stopped left limit and jump, and
zero conditional mean of the jump. It does not assert that the actual jump
vanishes. Positive lifetime is explicit because the source initial jump is
`jumpProcess X 0 = X 0`. The deterministic bound proves all sampled lifetimes
finite before the native finite-time stopped-value owner is evaluated.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}

/-- The actual left limit at a positive bounded predictable time is the
conditional expectation of the stopped value given the native before-field. -/
theorem stopped_leftLimit_ae_eq_condExp_before_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    stoppedValue (leftLimitProcess M) τ =ᵐ[P]
      P[stoppedValue M τ | hτ.1.measurableSpaceBefore] := by
  obtain ⟨σ, hs, hle⟩ := hτ.exists_announcing_le
  apply hs.stopped_leftLimit_ae_eq_condExp_before hτ.1 hF.complete_initial hc hpos
    (Eventually.of_forall fun ω ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (hb ω))
  intro n
  exact hM.stoppedValue_ae_eq_condExp_of_bounded_le_usual hF hc.hasRightContinuousPaths
    (hs.isStoppingTime n) hτ.1 (hle n) hb

/-- Integrability is a conclusion of the before-field conditional identity. -/
theorem integrable_stopped_leftLimit_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    Integrable (stoppedValue (leftLimitProcess M) τ) P :=
  integrable_condExp.congr
    (hM.stopped_leftLimit_ae_eq_condExp_before_of_predictable_of_bounded
      hF hc hτ hpos hb).symm

/-- The actual jump is integrable, not merely its conditional expectation. -/
theorem integrable_stopped_jump_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    Integrable (stoppedValue (jumpProcess M) τ) P := by
  change Integrable (stoppedValue M τ - stoppedValue (leftLimitProcess M) τ) P
  exact (hM.integrable_stoppedValue_of_bounded_usual hF hc.hasRightContinuousPaths hτ.1 hb).sub
    (hM.integrable_stopped_leftLimit_of_predictable_of_bounded hF hc hτ hpos hb)

/-- Predictability gives zero conditional jump mean, not absence of jumps. -/
theorem condExp_stopped_jump_before_ae_eq_zero_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    P[stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  have hi := hM.integrable_stoppedValue_of_bounded_usual hF hc.hasRightContinuousPaths hτ.1 hb
  have hl := hM.integrable_stopped_leftLimit_of_predictable_of_bounded hF hc hτ hpos hb
  have he := hM.stopped_leftLimit_ae_eq_condExp_before_of_predictable_of_bounded
    hF hc hτ hpos hb
  have hce : P[stoppedValue (leftLimitProcess M) τ | hτ.1.measurableSpaceBefore] =ᵐ[P]
      P[stoppedValue M τ | hτ.1.measurableSpaceBefore] :=
    (condExp_congr_ae he).trans
      (condExp_condExp_of_le le_rfl hτ.1.measurableSpaceBefore_le_ambient)
  change P[stoppedValue M τ - stoppedValue (leftLimitProcess M) τ |
    hτ.1.measurableSpaceBefore] =ᵐ[P] 0
  filter_upwards [condExp_sub hi hl hτ.1.measurableSpaceBefore, hce] with ω hlin hω
  change _ = (0 : ℝ)
  rw [hlin]
  change P[stoppedValue M τ | hτ.1.measurableSpaceBefore] ω -
    P[stoppedValue (leftLimitProcess M) τ | hτ.1.measurableSpaceBefore] ω = 0
  rw [hω, sub_self]

end MeasureTheory.Martingale

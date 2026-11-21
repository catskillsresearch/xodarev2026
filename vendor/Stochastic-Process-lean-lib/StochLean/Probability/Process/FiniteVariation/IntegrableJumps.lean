/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integrable
public import StochLean.Probability.Process.Measurability.PredictableJumps
public import StochLean.Probability.Process.Stopping.JumpExitIntegrability
public import StochLean.Probability.Process.Stopping.PredictableValue

/-! # Integrable actual jump coefficients of IV processes

Every positive-time jump is bounded by the actual whole-halfline variation.
Consequently an integrable-variation process has integrable jump coefficients
at arbitrary positive stopping times, with explicit terminal zero at infinity.
No integrability of the initial random value is required. For predictable FV
inputs, the actual coefficient is measurable before the stopping time even
when the path hypotheses hold only almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Positive jumps are limits of actual increments, each bounded by the
finite extended variation. The initial value does not enter this bound. -/
theorem IsCadlagPath.norm_jumpProcess_le_eVariationOn {ω : Ω}
    (hc : IsCadlagPath (X · ω)) (hv : BoundedVariationOn (X · ω) univ)
    {t : ℝ≥0} (ht : 0 < t) :
    ‖jumpProcess X t ω‖ ≤ (eVariationOn (X · ω) univ).toReal := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hl : Tendsto (fun s : ℝ≥0 ↦ ‖X t ω - X s ω‖) (𝓝[<] t)
      (𝓝 ‖jumpProcess X t ω‖) :=
    (tendsto_const_nhds.sub (hc.tendsto_leftLimitProcess ht.ne')).norm
  apply le_of_tendsto hl
  exact Eventually.of_forall fun s ↦ by
    simpa only [dist_eq_norm] using hv.dist_le (mem_univ t) (mem_univ s)

/-- Explicit terminal zero preserves the variation bound when the stopping
time may be infinite. No finite-time evaluation at infinity is used. -/
theorem HasIntegrableVariation.ae_norm_stopped_jump_le_eVariationOn
    (hv : HasIntegrableVariation X P) (hc : HasCadlagPaths X P)
    (τ : Ω → WithTop ℝ≥0) (hp : ∀ᵐ ω ∂P, 0 < τ ω) :
    ∀ᵐ ω ∂P, ‖stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω‖ ≤
      (eVariationOn (X · ω) univ).toReal := by
  filter_upwards [hv.ae_eVariationOn_ne_top, hc, hp] with ω hvω hcω hpω
  cases ht : τ ω with
  | top =>
    rw [stoppedValueWithTerminal_jump_eq_zero_of_top ht, norm_zero]
    exact ENNReal.toReal_nonneg
  | coe t =>
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
    have hpos : 0 < t := WithTop.coe_lt_coe.mp (ht ▸ hpω)
    exact hcω.norm_jumpProcess_le_eVariationOn hvω hpos

/-- Actual positive stopped jumps are L1 without any assumption on the
initial random value. Finite total variation is checked before `toReal`. -/
theorem HasIntegrableVariation.integrable_stopped_jump
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hp : ∀ᵐ ω ∂P, 0 < τ ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) P := by
  apply hv.integrable_eVariationOn_toReal.mono'
    ((ha.stronglyMeasurable_stopped_jump_of_usual hF hc hτ).mono
      hτ.measurableSpace_le).aestronglyMeasurable
  exact hv.ae_norm_stopped_jump_le_eVariationOn hc τ hp

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual original FV jump coefficient, not only its good-path version,
is measurable in the before field. Completeness restores the original values
on the exceptional initial-null event. -/
theorem IsStronglyPredictable.stronglyMeasurable_stopped_jump_before_of_finiteVariation
    (hX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpaceBefore]
      (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) := by
  obtain ⟨Y, hXY, hpY, hY⟩ :=
    hX.exists_cadlag_finiteVariation_indistinguishable_of_usual hF hc hv
  have hm := IsStronglyPredictable.stronglyMeasurable_stoppedValueWithTerminal_before
    (Z := fun _ ↦ (0 : ℝ)) (hpY.jumpProcess_of_cadlag (fun ω ↦ (hY ω).1))
    stronglyMeasurable_const hτ
  have hcomplete : IsCompleteSubMeasurableSpace P hτ.measurableSpaceBefore := fun s hs ↦
    hτ.le_measurableSpaceBefore s (hF.complete_initial s hs)
  have he := hcomplete.measurable_congr_ae hm.measurable
    (hXY.jumpProcess.stoppedValueWithTerminal (EventuallyEq.refl _ _) τ).symm
  exact he.stronglyMeasurable

end MeasureTheory

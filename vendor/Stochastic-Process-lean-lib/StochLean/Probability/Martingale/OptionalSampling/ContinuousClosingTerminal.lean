/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousClosingProjection
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousInfiniteTerminal

/-! # Optional sampling from an arbitrary closing variable

The native stopping sigma-field at infinity is the supremum of the finite
filtration. Consequently the terminal-valued owner uses the closing variable's
projection onto that field. Its conditional expectation at any stopping time
still equals that of the original closing variable. The unprojected terminal
value is justified when it is measurable for the terminal sigma-field.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Y : Ω → ℝ}

theorem integrable_stoppedValue_closingProjection
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hF : F.IsUsual P)
    (hY : Integrable Y P) (hclose : ∀ t, X t =ᵐ[P] P[Y | F t])
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Integrable (stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ) P :=
  hX.integrable_stoppedValueWithTerminal (uniformIntegrable_of_integrable_closing hY hclose)
    hF hc (hX.tendsto_terminalProjection_of_integrable_closing hc hY hclose).1 hτ

theorem stoppedValue_closingProjection_ae_eq_condExp
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hF : F.IsUsual P)
    (hY : Integrable Y P) (hclose : ∀ t, X t =ᵐ[P] P[Y | F t])
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ =ᵐ[P] P[Y | hτ.measurableSpace] :=
  (hX.stoppedValueWithTerminal_ae_eq_condExp_terminal
    (uniformIntegrable_of_integrable_closing hY hclose) hF hc
    (hX.tendsto_terminalProjection_of_integrable_closing hc hY hclose).1 hτ).trans
      (condExp_condExp_of_le hτ.measurableSpace_le' (iSup_le F.le))

theorem stoppedValue_closingProjection_optionalSampling
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hF : F.IsUsual P)
    (hY : Integrable Y P) (hclose : ∀ t, X t =ᵐ[P] P[Y | F t])
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    stoppedValueWithTerminal X P[Y | ⨆ t, F t] σ =ᵐ[P]
      P[stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ | hσ.measurableSpace] :=
  hX.stoppedValueWithTerminal_ae_eq_condExp_of_ae_le
    (uniformIntegrable_of_integrable_closing hY hclose) hF hc
    (hX.tendsto_terminalProjection_of_integrable_closing hc hY hclose).1 hσ hτ hle

/-- A terminal-measurable closing variable needs no projection. The sigma-field
premise is explicit: ambient measurability alone does not justify this formula
for the native stopping owner when both times can be infinite. -/
theorem stoppedValue_terminalMeasurable_closing_optionalSampling
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) (hF : F.IsUsual P)
    (hY : Integrable Y P) (hm : StronglyMeasurable[⨆ t, F t] Y)
    (hclose : ∀ t, X t =ᵐ[P] P[Y | F t])
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    stoppedValueWithTerminal X Y σ =ᵐ[P]
      P[stoppedValueWithTerminal X Y τ | hσ.measurableSpace] := by
  have h := hX.stoppedValue_closingProjection_optionalSampling hc hF hY hclose hσ hτ hle
  rwa [condExp_of_stronglyMeasurable (iSup_le F.le) hm hY] at h

end MeasureTheory.Martingale

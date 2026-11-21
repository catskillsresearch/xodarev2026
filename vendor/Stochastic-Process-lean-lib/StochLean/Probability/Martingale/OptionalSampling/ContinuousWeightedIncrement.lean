/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousTerminalLp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Bounded stopping-time coefficients and martingale increments

The martingale is capped at a deterministic horizon, but the two original
stopping endpoints may be unbounded. Coefficients are known at the left endpoint.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

theorem condExp_weighted_finiteStoppingTime_increment_min
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (α β : FiniteStoppingTime F) (hαβ : ∀ ω, α ω ≤ β ω) (T : ℝ≥0)
    {Z : Ω → ℝ} (hZ : Measurable[α.measurableSpace] Z)
    (C : ℝ) (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    P[fun ω ↦ Z ω * (X (min (β ω) T) ω - X (min (α ω) T) ω) |
      α.measurableSpace] =ᵐ[P] 0 := by
  let A : Ω → ℝ := fun ω ↦ X (min (α ω) T) ω
  let B : Ω → ℝ := fun ω ↦ X (min (β ω) T) ω
  have hA : A =ᵐ[P] P[X T | α.measurableSpace] :=
    hX.finiteStoppingTime_min_ae_eq_condExp_terminal hF hr α T
  have hB : B =ᵐ[P] P[X T | β.measurableSpace] :=
    hX.finiteStoppingTime_min_ae_eq_condExp_terminal hF hr β T
  have hiA : Integrable A P := integrable_condExp.congr hA.symm
  have hiB : Integrable B P := integrable_condExp.congr hB.symm
  have hle : α.measurableSpace ≤ β.measurableSpace :=
    α.isStoppingTime.measurableSpace_mono β.isStoppingTime
      (fun ω ↦ WithTop.coe_le_coe.mpr (hαβ ω))
  have hd : P[B - A | α.measurableSpace] =ᵐ[P] 0 := by
    calc
      P[B - A | α.measurableSpace] =ᵐ[P]
          P[B | α.measurableSpace] - P[A | α.measurableSpace] := condExp_sub hiB hiA _
      _ =ᵐ[P] P[X T | α.measurableSpace] - P[X T | α.measurableSpace] :=
        ((condExp_congr_ae hB).trans (condExp_condExp_of_le hle β.measurableSpace_le)).sub
          ((condExp_congr_ae hA).trans
            (condExp_condExp_of_le le_rfl α.measurableSpace_le))
      _ = 0 := sub_self _
  have hiZ : Integrable (Z * (B - A)) P :=
    (hiB.sub hiA).bdd_smul C (hZ.mono α.measurableSpace_le le_rfl).aestronglyMeasurable hb
  have hout := condExp_mul_of_aestronglyMeasurable_left hZ.aestronglyMeasurable hiZ (hiB.sub hiA)
  filter_upwards [hout, hd] with ω houtω hdω
  change P[Z * (B - A) | α.measurableSpace] ω = 0
  rw [houtω]
  change Z ω * P[B - A | α.measurableSpace] ω = 0
  rw [hdω, Pi.zero_apply, mul_zero]

theorem condExp_weighted_finiteStoppingTime_increment_min_of_le
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (α β : FiniteStoppingTime F) (hαβ : ∀ ω, α ω ≤ β ω) (T : ℝ≥0)
    {Z : Ω → ℝ} (hZ : Measurable[α.measurableSpace] Z)
    (C : ℝ) (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) {s : ℝ≥0} (hs : ∀ ω, s ≤ α ω) :
    P[fun ω ↦ Z ω * (X (min (β ω) T) ω - X (min (α ω) T) ω) | F s] =ᵐ[P] 0 := by
  have hle : F s ≤ α.measurableSpace := by
    have h := (isStoppingTime_const F s).measurableSpace_mono α.isStoppingTime
      (fun ω ↦ WithTop.coe_le_coe.mpr (hs ω))
    change (isStoppingTime_const F s).measurableSpace ≤ α.measurableSpace at h
    rw [IsStoppingTime.measurableSpace_const] at h
    exact h
  have hz := hX.condExp_weighted_finiteStoppingTime_increment_min hF hr α β hαβ T hZ C hb
  calc
    _ =ᵐ[P] P[P[fun ω ↦ Z ω * (X (min (β ω) T) ω - X (min (α ω) T) ω) |
      α.measurableSpace] | F s] := (condExp_condExp_of_le hle α.measurableSpace_le).symm
    _ =ᵐ[P] P[(0 : Ω → ℝ) | F s] := condExp_congr_ae hz
    _ = 0 := condExp_zero

end MeasureTheory.Martingale

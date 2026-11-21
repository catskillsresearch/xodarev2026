/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.IntegrableJumps
public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpIntegrableTerminal
public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Actual jumps of a predictable integrable-variation compensator

If `J - B` is a UI martingale and `B` is predictable, cadlag, and of integrable
variation, its jump at a positive predictable lifetime is the conditional mean
of the actual jump of `J` before that lifetime. Integrability of the jump of
`J` is derived first from the two genuine integrable jump coefficients.

Every sample uses explicit terminal zero at infinity. The subtraction identity
uses one common cadlag event, with a finite-time evaluation only in the finite
lifetime branch. No total-inaccessibility or boundedness assumption is used.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {J B : ℝ≥0 → Ω → ℝ} {γ : Ω → WithTop ℝ≥0}

/-- The actual predictable compensator jump is the before-field conditional
mean of the actual source jump; source-jump integrability is a conclusion. -/
theorem Martingale.integrable_stopped_jump_and_compensator_condExp_before
    (hM : Martingale (J - B) F P) (hu : UniformIntegrable (J - B) 1 P)
    (hF : F.IsUsual P) (hcJ : HasCadlagPaths J P) (hcB : HasCadlagPaths B P)
    (hpB : IsStronglyPredictable F B) (hvB : HasIntegrableVariation B P)
    (hγ : IsPredictableStoppingTime F γ P) (hpos : ∀ᵐ ω ∂P, 0 < γ ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess J) (fun _ ↦ (0 : ℝ)) γ) P ∧
      stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ =ᵐ[P]
        P[stoppedValueWithTerminal (jumpProcess J) (fun _ ↦ (0 : ℝ)) γ |
          hγ.1.measurableSpaceBefore] := by
  let JJ := stoppedValueWithTerminal (jumpProcess J) (fun _ ↦ (0 : ℝ)) γ
  let JB := stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) γ
  let JM := stoppedValueWithTerminal (jumpProcess (J - B)) (fun _ ↦ (0 : ℝ)) γ
  have hiB : Integrable JB P :=
    hvB.integrable_stopped_jump hpB.stronglyAdapted.adapted hF hcB hγ.1 hpos
  obtain ⟨hiM, hzM⟩ :=
    hM.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
      hu hF (hcJ.sub hcB) hγ hpos
  have he : JM =ᵐ[P] JJ - JB := by
    filter_upwards [hcJ, hcB] with ω hj hb
    by_cases ht : γ ω = ⊤
    · simp only [JM, JJ, JB, stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
    · simp only [JM, JJ, JB, stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
      exact hj.jumpProcess_sub hb (γ ω).untopA
  have hiJ : Integrable JJ P := (hiM.add hiB).congr (by
    filter_upwards [he] with ω hω
    change JM ω + JB ω = JJ ω
    simpa only [Pi.sub_apply, sub_add_cancel] using congrArg (fun x ↦ x + JB ω) hω)
  have hmB : StronglyMeasurable[hγ.1.measurableSpaceBefore] JB :=
    hpB.stronglyMeasurable_stopped_jump_before_of_finiteVariation
      hF hcB hvB.hasFiniteVariationPaths hγ.1
  have hceB : P[JB | hγ.1.measurableSpaceBefore] = JB :=
    condExp_of_stronglyMeasurable hγ.1.measurableSpaceBefore_le_ambient hmB hiB
  refine ⟨hiJ, ?_⟩
  filter_upwards [hzM, condExp_congr_ae he,
    condExp_sub hiJ hiB hγ.1.measurableSpaceBefore] with ω hz heω hlin
  change JB ω = P[JJ | hγ.1.measurableSpaceBefore] ω
  have hz' : P[JM | hγ.1.measurableSpaceBefore] ω = 0 := hz
  rw [heω, hlin] at hz'
  simpa only [Pi.sub_apply, hceB] using (sub_eq_zero.mp hz').symm

end MeasureTheory

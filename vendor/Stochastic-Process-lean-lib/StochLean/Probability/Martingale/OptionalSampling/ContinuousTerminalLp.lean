/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousLp

/-! # Terminal Lp control on finite, unbounded stopping partitions

Stopping the integrator at `T` gives a conditional expectation of `X_T` in the sigma-field
at the original endpoint. The endpoint need not have a deterministic bound.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem finiteStoppingTime_min_ae_eq_condExp_terminal (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) :
    (fun ω ↦ X (min (τ ω) T) ω) =ᵐ[P] P[X T | τ.measurableSpace] := by
  have h := hX.stoppedValue_min_ae_eq_condExp_of_bounded_usual hF hr τ.isStoppingTime
    (isStoppingTime_const F T) (fun _ ↦ le_rfl)
  have heq : MeasureTheory.stoppedValue X (fun ω ↦ min (τ.withTop ω) (T : WithTop ℝ≥0)) =
      fun ω ↦ X (min (τ ω) T) ω := by
    funext ω
    change X (WithTop.untopA (min (τ ω : WithTop ℝ≥0) (T : WithTop ℝ≥0))) ω = _
    rw [← WithTop.coe_min]
    rfl
  change MeasureTheory.stoppedValue X (fun ω ↦ min (τ.withTop ω) (T : WithTop ℝ≥0)) =ᵐ[P]
    P[X T | τ.measurableSpace] at h
  rw [heq] at h
  exact h

theorem memLp_finiteStoppingTime_min (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hXT : MemLp (X T) p P) : MemLp (fun ω ↦ X (min (τ ω) T) ω) p P :=
  (hXT.condExp (m := τ.measurableSpace) hp).ae_eq
    (hX.finiteStoppingTime_min_ae_eq_condExp_terminal hF hr τ T).symm

theorem eLpNorm_finiteStoppingTime_min_le (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun ω ↦ X (min (τ ω) T) ω) p P ≤ eLpNorm (X T) p P := by
  rw [eLpNorm_congr_ae (hX.finiteStoppingTime_min_ae_eq_condExp_terminal hF hr τ T)]
  exact eLpNorm_condExp_le_eLpNorm _ hp

end MeasureTheory.Martingale

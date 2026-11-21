/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Process.LocalMartingale

/-! # Lp control of bounded continuous-time stopping values

Optional sampling identifies the stopping value with a conditional expectation of the
terminal value. Mathlib's conditional-expectation contraction then provides the Lp bound.
In particular, arbitrary stopping preserves finite-time square integrability; no global
L2 bound is assumed or concluded.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem memLp_stoppedValue_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) {p : ℝ≥0∞} (hp : 1 ≤ p) (hXT : MemLp (X T) p P) :
    MemLp (stoppedValue X τ) p P :=
  (hXT.condExp (m := hτ.measurableSpace) hp).ae_eq
    (hX.stoppedValue_ae_eq_condExp_of_bounded_usual hF hr hτ hbound).symm

theorem eLpNorm_stoppedValue_le_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (stoppedValue X τ) p P ≤ eLpNorm (X T) p P := by
  rw [eLpNorm_congr_ae (hX.stoppedValue_ae_eq_condExp_of_bounded_usual hF hr hτ hbound)]
  exact eLpNorm_condExp_le_eLpNorm _ hp

theorem memLp_stoppedProcess_of_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (t : ℝ≥0)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hXt : MemLp (X t) p P) :
    MemLp (stoppedProcess X τ t) p P :=
  hX.memLp_stoppedValue_of_bounded_usual hF hr
    ((isStoppingTime_const F t).min hτ) (fun _ ↦ min_le_left _ _) hp hXt

theorem eLpNorm_stoppedProcess_le_of_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (t : ℝ≥0)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (stoppedProcess X τ t) p P ≤ eLpNorm (X t) p P :=
  hX.eLpNorm_stoppedValue_le_of_bounded_usual hF hr
    ((isStoppingTime_const F t).min hτ) (fun _ ↦ min_le_left _ _) hp

end MeasureTheory.Martingale

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem IsSquareIntegrableMartingale.stoppedProcess_of_usual
    (hX : IsSquareIntegrableMartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsSquareIntegrableMartingale (stoppedProcess X τ) F P :=
  ⟨hX.1.stoppedProcess_of_usual hF hr hτ, fun t ↦
    hX.1.memLp_stoppedProcess_of_usual hF hr hτ t (by norm_num) (hX.2 t)⟩

end ProbabilityTheory

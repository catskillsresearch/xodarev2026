/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra

/-! # Algebra of locally integrable variation

The only local predicate remains Mathlib's `Locally`, through the existing
unmasked stopped-variation criterion. Indistinguishability and negation reuse
the same localizing sequence without any process measurability assumption.

For addition, the native minimum of two localizing sequences retains their
almost-sure monotonicity; no pointwise monotonicity is imposed. Actual stopping
and sum variation are measurable because the processes are adapted and cadlag
on a usual filtration. Variation domination alone is not used to infer that
measurability. Subtraction then follows from addition and exact negation.

None of these results assumes a finite measure, integrable initial random
values, or zero initial values. No new local predicate or selector is defined.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- A common pathwise almost-sure equality transports the original stopped
variation and its integrability, without adaptedness or usuality assumptions. -/
theorem HasLocallyIntegrableVariation.congr (hX : HasLocallyIntegrableVariation X F P)
    (hXY : Indistinguishable X Y P) : HasLocallyIntegrableVariation Y F P := by
  obtain ⟨τ, hτ, hv⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hX
  exact hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    ⟨τ, hτ, fun n ↦ (hv n).congr (hXY.stoppedProcess (τ n))⟩

/-- Exact negation invariance of actual variation requires no additional
measurability, path regularity, or filtration hypotheses. -/
theorem HasLocallyIntegrableVariation.neg (hX : HasLocallyIntegrableVariation X F P) :
    HasLocallyIntegrableVariation (-X) F P := by
  obtain ⟨τ, hτ, hv⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hX
  refine hasLocallyIntegrableVariation_iff_exists_stopped.mpr ⟨τ, hτ, fun n ↦ ?_⟩
  change HasIntegrableVariation (-(stoppedProcess X (τ n))) P
  exact (hv n).neg

/-- Intersecting actual localizers preserves locally integrable variation.
Usual cadlag adaptedness supplies the stopped sum's actual measurability. -/
theorem HasLocallyIntegrableVariation.add (hX : HasLocallyIntegrableVariation X F P)
    (hY : HasLocallyIntegrableVariation Y F P) (haX : Adapted F X) (haY : Adapted F Y)
    (hF : F.IsUsual P) (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    HasLocallyIntegrableVariation (X + Y) F P := by
  obtain ⟨τ, hτ, hvX⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hX
  obtain ⟨σ, hσ, hvY⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hY
  have hρ := hτ.min hσ
  refine hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    ⟨min τ σ, hρ, fun n ↦ ?_⟩
  have haτ : Adapted F (stoppedProcess X (τ n)) :=
    (haX.stronglyAdapted.stoppedProcess_of_usual hF hcX.hasRightContinuousPaths
      (hτ.isStoppingTime n)).adapted
  have haσ : Adapted F (stoppedProcess Y (σ n)) :=
    (haY.stronglyAdapted.stoppedProcess_of_usual hF hcY.hasRightContinuousPaths
      (hσ.isStoppingTime n)).adapted
  have hx := (hvX n).stoppedProcess haτ hF (hcX.stoppedProcess (τ n))
    (hσ.isStoppingTime n)
  have hy := (hvY n).stoppedProcess haσ hF (hcY.stoppedProcess (σ n))
    (hτ.isStoppingTime n)
  have heX : σ n ⊓ τ n = (min τ σ) n := by
    funext ω
    exact min_comm (σ n ω) (τ n ω)
  have heY : τ n ⊓ σ n = (min τ σ) n := rfl
  rw [stoppedProcess_stoppedProcess, heX] at hx
  rw [stoppedProcess_stoppedProcess, heY] at hy
  have haρX : Adapted F (stoppedProcess X ((min τ σ) n)) :=
    (haX.stronglyAdapted.stoppedProcess_of_usual hF hcX.hasRightContinuousPaths
      (hρ.isStoppingTime n)).adapted
  have haρY : Adapted F (stoppedProcess Y ((min τ σ) n)) :=
    (haY.stronglyAdapted.stoppedProcess_of_usual hF hcY.hasRightContinuousPaths
      (hρ.isStoppingTime n)).adapted
  change HasIntegrableVariation
    (stoppedProcess X ((min τ σ) n) + stoppedProcess Y ((min τ σ) n)) P
  exact hx.add hy haρX haρY hF
    (hcX.stoppedProcess ((min τ σ) n)) (hcY.stoppedProcess ((min τ σ) n))

/-- Subtraction uses the same native localization and actual variation
measurability; no initial integrability or normalization is required. -/
theorem HasLocallyIntegrableVariation.sub (hX : HasLocallyIntegrableVariation X F P)
    (hY : HasLocallyIntegrableVariation Y F P) (haX : Adapted F X) (haY : Adapted F Y)
    (hF : F.IsUsual P) (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    HasLocallyIntegrableVariation (X - Y) F P := by
  have hcNegY : HasCadlagPaths (-Y) P := hcY.continuous_comp continuous_neg
  simpa only [sub_eq_add_neg] using
    hX.add hY.neg haX (fun t ↦ (haY t).neg) hF hcX hcNegY

end ProbabilityTheory

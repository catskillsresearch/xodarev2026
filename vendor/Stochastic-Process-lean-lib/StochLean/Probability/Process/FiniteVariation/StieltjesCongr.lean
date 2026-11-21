/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Stieltjes

/-! # Common-path equality preserves the actual variation kernel

Both kernels are the existing pathwise Stieltjes kernels on their original
everywhere-BV, right-continuous domains. A single common event of path equality
identifies their entire measure fibers, not merely each deterministic interval
separately. No new kernel or exceptional-path convention is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- Indistinguishable everywhere-good source paths have the same actual
total-variation kernel almost everywhere. No measure finiteness, total
variation bound, or usual condition is needed for this version comparison. -/
theorem Indistinguishable.totalVariationKernel_ae_eq (hXY : Indistinguishable X Y P)
    (haX : Adapted F X) (hvX : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω))
    (haY : Adapted F Y) (hvY : ∀ ω, LocallyBoundedVariationOn (Y · ω) univ)
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) :
    (fun ω ↦ totalVariationKernel X haX hvX hrX ω) =ᵐ[P]
      fun ω ↦ totalVariationKernel Y haY hvY hrY ω := by
  filter_upwards [hXY] with ω hω
  change (totalVariationStieltjes (X · ω) (hvX ω) (hrX ω)).measure =
    (totalVariationStieltjes (Y · ω) (hvY ω) (hrY ω)).measure
  have he : totalVariationStieltjes (X · ω) (hvX ω) (hrX ω) =
      totalVariationStieltjes (Y · ω) (hvY ω) (hrY ω) := by
    apply StieltjesFunction.ext
    intro t
    change pathTotalVariation (X · ω) t = pathTotalVariation (Y · ω) t
    rw [show (X · ω) = (Y · ω) from funext hω]
  exact congrArg (fun Z : StieltjesFunction ℝ≥0 ↦ Z.measure) he

end ProbabilityTheory

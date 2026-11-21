/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann
public import StochLean.Probability.Process.Semimartingale.InitialMask
public import StochLean.Probability.Process.UCP.InitialMask

/-! # The actual raw mixed bracket commutes with a common initial event mask

Masking both sources by the same event in the initial sigma field masks
their actual raw covariation by that event. This follows from the original
mixed increment sums and uniqueness of their UCP limit, including the raw
initial product. No initial moment or normalization is imposed.

Together with the existing simultaneous raw bracket stopping theorem this
supplies the exact positive-lifetime event masks in native localizations.
It does not silently replace a masked stopped process by an unmasked one,
and it introduces no new bracket or limit selector.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The same initial event mask on both sources is retained once in their
actual raw mixed bracket, including its arbitrary initial product. -/
theorem quadraticCovariation_indicator_initial
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Indistinguishable
      ((hX.indicator_initial hs).quadraticCovariation (hY.indicator_initial hs) hF)
      (fun t ↦ s.indicator (hX.quadraticCovariation hY hF t)) P := by
  apply (hX.indicator_initial hs).quadraticCovariation_indistinguishable_of_limits
    (hY.indicator_initial hs) hF
  · intro π hπ
    apply ((hX.tendstoUCP_quadraticCovariationSumProcess hY hF hπ).indicator s).congr_left
    intro n
    exact Eventually.of_forall fun ω t ↦ by
      by_cases hω : ω ∈ s <;>
        simp [StoppingTimePartition.quadraticCovariationSumProcess,
          StochLean.covariationSum, StochLean.TimePartition.increment, hω]
  · exact ((hX.hasCadlagPaths_quadraticCovariation hY hF).indicator s).hasRightContinuousPaths

end ProbabilityTheory.IsSemimartingale

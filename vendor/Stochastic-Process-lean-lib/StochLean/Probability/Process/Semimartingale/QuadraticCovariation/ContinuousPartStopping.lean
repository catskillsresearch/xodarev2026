/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartStopping

/-! # Simultaneous stopping of continuous quadratic covariation -/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_stoppedProcess_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      ((hX.stoppedProcess hF hτ).continuousQuadraticCovariation (hY.stoppedProcess hF hτ) hF)
      (MeasureTheory.stoppedProcess (hX.continuousQuadraticCovariation hY hF) τ) P := by
  have heq : Indistinguishable
      (MeasureTheory.stoppedProcess X τ + MeasureTheory.stoppedProcess Y τ)
      (MeasureTheory.stoppedProcess (X + Y) τ) P := ae_of_all _ fun _ _ ↦ rfl
  have hsum := IsSemimartingale.continuousQuadraticVariation_congr
    ((hX.stoppedProcess hF hτ).add (hY.stoppedProcess hF hτ))
    ((hX.add hY).stoppedProcess hF hτ) hF heq
  filter_upwards [hsum, (hX.add hY).continuousQuadraticVariation_stoppedProcess hF hτ,
    hX.continuousQuadraticVariation_stoppedProcess hF hτ,
    hY.continuousQuadraticVariation_stoppedProcess hF hτ] with ω hsumω hs hx hy t
  simp only [continuousQuadraticCovariation, hsumω t, hs t, hx t, hy t,
    MeasureTheory.stoppedProcess]

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Subtraction
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping

/-! # The raw bracket of an ordered stopped difference

The mixed identity uses already proved one-sided bracket stopping, not a
false identity of individual mixed partition cells. AE order suffices.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

theorem IsSemimartingale.quadraticCovariation_ordered_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    Indistinguishable
      ((hX.stoppedProcess hF hτ).quadraticCovariation (hX.stoppedProcess hF hσ) hF)
      (MeasureTheory.stoppedProcess (hX.quadraticVariation hF) σ) P := by
  have hc := (hX.quadraticCovariation_stoppedProcess_left hX hF hτ).trans
    ((hX.quadraticCovariation_self hF).stoppedProcess τ)
  filter_upwards [(hX.stoppedProcess hF hτ).quadraticCovariation_stoppedProcess_right hX hF hσ,
    hc.stoppedProcess σ, hle] with ω hr hl ho t
  rw [hr t, hl t, MeasureTheory.stoppedProcess_stoppedProcess']
  simp only [MeasureTheory.stoppedProcess, min_eq_left ho]

theorem IsSemimartingale.quadraticVariation_stopped_difference
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    Indistinguishable
      (((hX.stoppedProcess hF hτ).sub (hX.stoppedProcess hF hσ)).quadraticVariation hF)
      (MeasureTheory.stoppedProcess (hX.quadraticVariation hF) τ -
        MeasureTheory.stoppedProcess (hX.quadraticVariation hF) σ) P := by
  filter_upwards [(hX.stoppedProcess hF hτ).quadraticVariation_sub
      (hX.stoppedProcess hF hσ) hF,
    hX.quadraticVariation_stoppedProcess hF hτ,
    hX.quadraticVariation_stoppedProcess hF hσ,
    hX.quadraticCovariation_ordered_stoppedProcess hF hσ hτ hle]
    with ω hd ht hs hc t
  rw [hd t, ht t, hs t, hc t]
  simp only [Pi.sub_apply]
  ring

end ProbabilityTheory

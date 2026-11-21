/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Stopping

/-! # Stopping the source elementary integral process

The integrator-stopping identity is pathwise even for an arbitrary raw random time,
possibly infinite. The integrand-cutoff identity additionally needs a stopping time
to keep the cutoff in the source simple predictable class. Cutoff is not frozen stopping.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem SimplePredictableRep.integralProcess_stoppedProcess (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    H.integralProcess (stoppedProcess X τ) = stoppedProcess (H.integralProcess X) τ := by
  funext t ω
  cases hτ : τ ω with
  | top =>
    have hs (Y : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : stoppedProcess Y τ s ω = Y s ω :=
      stoppedProcess_eq_of_le (by rw [hτ]; exact le_top)
    rw [hs]
    simp only [integralProcess_apply, hs]
  | coe T =>
    have hs (Y : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
        stoppedProcess Y τ s ω = Y (min s T) ω := by
      change Y (min (s : WithTop ℝ≥0) (τ ω)).untopA ω = _
      rw [hτ, ← WithTop.coe_min]
      rfl
    rw [hs]
    simp only [integralProcess_apply, hs, min_assoc]
    simp

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem elementaryIntegralProcess_stoppedProcess (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    hH.elementaryIntegralProcess (stoppedProcess X τ) =
      stoppedProcess (hH.elementaryIntegralProcess X) τ :=
  hH.choose.integralProcess_stoppedProcess X τ

theorem elementaryIntegralProcess_cutoff (hH : IsSimplePredictable H F)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (X : ℝ≥0 → Ω → ℝ) :
    (hH.cutoff hτ).elementaryIntegralProcess X =
      stoppedProcess (hH.elementaryIntegralProcess X) τ := by
  rw [← hH.elementaryIntegralProcess_stoppedProcess]
  funext t
  rw [(hH.cutoff hτ).elementaryIntegralProcess_eq_elementaryIntegral_stopped,
    hH.elementaryIntegral_cutoff hτ, hH.elementaryIntegralProcess_eq_elementaryIntegral_stopped,
    stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
  apply congrArg (fun σ : Ω → WithTop ℝ≥0 ↦ hH.elementaryIntegral (stoppedProcess X σ))
  funext ω
  exact min_comm (τ ω) (t : WithTop ℝ≥0)

end IsSimplePredictable
end ProbabilityTheory

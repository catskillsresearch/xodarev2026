/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess

/-! # Locality of source elementary integrals on a single sample path -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F G : Filtration ℝ≥0 mΩ}
  {ω : Ω} {X Y H K : ℝ≥0 → Ω → ℝ}

theorem SimplePredictableRep.integral_congr_path (R : SimplePredictableRep F)
    (S : SimplePredictableRep G) (hRS : ∀ t, R.toProcess t ω = S.toProcess t ω)
    (X : ℝ≥0 → Ω → ℝ) : R.integral X ω = S.integral X ω := by
  have hinit : R.initial ω = S.initial ω := by
    simpa only [SimplePredictableRep.toProcess_zero] using hRS 0
  have hsum := StochLean.sum_intervalIncrement_congr
    (fun i : Fin R.partition.size ↦ R.partition.point i.castSucc ω)
    (fun i : Fin R.partition.size ↦ R.partition.point i.succ ω)
    (fun i ↦ R.coefficient i ω)
    (fun i : Fin S.partition.size ↦ S.partition.point i.castSucc ω)
    (fun i : Fin S.partition.size ↦ S.partition.point i.succ ω)
    (fun i ↦ S.coefficient i ω)
    (fun i ↦ (R.partition.path ω).left_le_right i)
    (fun i ↦ (S.partition.path ω).left_le_right i)
    (fun t ht ↦ by
      simpa only [SimplePredictableRep.toProcess, ne_of_gt ht, ↓reduceIte] using hRS t)
    (fun t ↦ X t ω)
  exact congrArg₂ (· + ·) (congrArg (fun a ↦ a * X 0 ω) hinit) hsum

theorem IsSimplePredictable.elementaryIntegralProcess_congr_integrand_path
    (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K G)
    (hHK : ∀ t, H t ω = K t ω) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    hH.elementaryIntegralProcess X t ω = hK.elementaryIntegralProcess X t ω := by
  exact hH.choose.integral_congr_path hK.choose
    (fun s ↦ by simpa only [hH.choose_spec, hK.choose_spec] using hHK s)
    (fun s ω ↦ X (min s t) ω)

theorem IsSimplePredictable.elementaryIntegralProcess_eq_zero_of_zero_path
    (hH : IsSimplePredictable H F) (hz : ∀ t, H t ω = 0)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : hH.elementaryIntegralProcess X t ω = 0 := by
  have h := hH.choose.integral_congr_path (SimplePredictableRep.zero F)
    (fun s ↦ by simpa only [hH.choose_spec, SimplePredictableRep.toProcess_zeroRep,
      Pi.zero_apply] using hz s) (fun s ω ↦ X (min s t) ω)
  change hH.choose.integral (fun s ω ↦ X (min s t) ω) ω = 0
  simpa only [SimplePredictableRep.integral_zero, Pi.zero_apply] using h

theorem IsSimplePredictable.elementaryIntegralProcess_congr_integrator_path
    (hH : IsSimplePredictable H F) (hXY : ∀ t, X t ω = Y t ω) (t : ℝ≥0) :
    hH.elementaryIntegralProcess X t ω = hH.elementaryIntegralProcess Y t ω := by
  rw [hH.elementaryIntegralProcess_eq hH.choose hH.choose_spec X,
    hH.elementaryIntegralProcess_eq hH.choose hH.choose_spec Y]
  simp only [SimplePredictableRep.integralProcess_apply, hXY]

end ProbabilityTheory

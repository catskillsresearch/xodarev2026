/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual

/-! # Measurability of the source elementary integral

Finite stopping endpoints are evaluated using the existing usual-filtration path-version
theorem. Integrator integrability and bounds on the integrand are not needed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem SimplePredictableRep.measurable_integral (H : SimplePredictableRep F)
    (hX : Adapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Measurable (H.integral X) := by
  have hm (τ : FiniteStoppingTime F) : Measurable (fun ω ↦ X (τ ω) ω) :=
    (hX.stronglyAdapted.measurable_stoppedValue_of_usual hF hr τ.isStoppingTime).mono
      τ.measurableSpace_le le_rfl
  apply ((H.measurable_initial.mono (F.le 0) le_rfl).mul
    ((hX 0).mono (F.le 0) le_rfl)).add
  exact Finset.measurable_fun_sum univ fun i _ ↦
    ((H.measurable_coefficient i).mono (H.partition.point i.castSucc).measurableSpace_le le_rfl).mul
      ((hm _).sub (hm _))

theorem IsSimplePredictable.measurable_elementaryIntegral {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) : Measurable (hH.elementaryIntegral X) :=
  hH.choose.measurable_integral hX hF hr

end ProbabilityTheory

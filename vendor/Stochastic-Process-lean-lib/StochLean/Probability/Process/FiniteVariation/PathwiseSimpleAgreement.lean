/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CagladIntegral
public import StochLean.Probability.Process.FiniteVariation.SimpleAgreement

/-! # Finite-variation integration on an individual sample path

The integrator need only have finite variation on the particular path being
compared. Caglad pathwise integrability is obtained by the deterministic,
one-point-space specialization of the existing progressive integration theorem.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

theorem IsCagladPath.integrableOn_variationStieltjes {f x : ℝ≥0 → ℝ}
    (hf : IsCagladPath f) (hx : LocallyBoundedVariationOn x univ)
    (hr : IsRightContinuousPath x) (T : ℝ≥0) :
    IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure :=
  integrableOn_variationStieltjes_of_adapted_caglad
    (Ω := Unit) (mΩ := ⊤) (F := ⊥) (fun t _ ↦ x t) (fun _ ↦ hx) (fun _ ↦ hr)
    (H := fun t _ ↦ f t) (fun _ ↦ measurable_const) (fun _ ↦ hf) T ()

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X H : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem SimplePredictableRep.pathStieltjesIntegral_eq_integralProcess
    (R : SimplePredictableRep F) (hv : LocallyBoundedVariationOn (X · ω) univ)
    (hr : IsRightContinuousPath (X · ω)) (T : ℝ≥0) :
    pathStieltjesIntegral (X · ω) hv hr (R.toProcess · ω) T = R.integralProcess X T ω := by
  have h := pathStieltjesIntegral_finite_step (x := (X · ω)) (hx := hv) (hr := hr)
    (fun i : Fin R.partition.size ↦ R.partition.point i.castSucc ω)
    (fun i : Fin R.partition.size ↦ R.partition.point i.succ ω)
    (fun i ↦ R.coefficient i ω) (fun i ↦ (R.partition.path ω).left_le_right i)
    (R.initial ω) T
  simpa only [SimplePredictableRep.toProcess, SimplePredictableRep.integralProcess_apply,
    Set.indicator, mem_Ioc] using h

theorem IsSimplePredictable.pathStieltjesIntegral_eq_elementaryIntegralProcess
    (hH : IsSimplePredictable H F) (hv : LocallyBoundedVariationOn (X · ω) univ)
    (hr : IsRightContinuousPath (X · ω)) (T : ℝ≥0) :
    pathStieltjesIntegral (X · ω) hv hr (H · ω) T = hH.elementaryIntegralProcess X T ω := by
  have h := hH.choose.pathStieltjesIntegral_eq_integralProcess hv hr T
  rw [hH.choose_spec] at h
  exact h

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralRegularity

/-! # Jumps of pathwise Stieltjes integrals at positive times

The source time-zero convention is dealt with separately at the process layer.
Positive-time jumps are obtained from actual atoms of the two component measures.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

private theorem leftLim_const_add_sub {p q : ℝ≥0 → ℝ} {t : ℝ≥0}
    (ht : 0 < t) (c : ℝ)
    (hp : Tendsto p (𝓝[<] t) (𝓝 (Function.leftLim p t)))
    (hq : Tendsto q (𝓝[<] t) (𝓝 (Function.leftLim q t))) :
    Function.leftLim (fun u ↦ c + p u - q u) t =
      c + Function.leftLim p t - Function.leftLim q t := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact leftLim_eq_of_tendsto ((tendsto_const_nhds.add hp).sub hq)

theorem stieltjesMeasure_real_singleton (A : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    (A.measure {t}).toReal = A t - Function.leftLim A t := by
  rw [StieltjesFunction.measure_singleton,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (A.mono.leftLim_le le_rfl))]

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f : ℝ≥0 → ℝ}

theorem variationStieltjes_measure_singleton_sub {t : ℝ≥0} (ht : 0 < t) :
    ((positiveVariationStieltjes x hx hr).measure {t}).toReal -
      ((negativeVariationStieltjes x hx hr).measure {t}).toReal = x t - Function.leftLim x t := by
  let p := positiveVariationStieltjes x hx hr
  let n := negativeVariationStieltjes x hx hr
  have heq : x = fun u ↦ x 0 + p u - n u := by
    funext u
    have h := pathPositiveVariation_sub_negative x u
    change p u - n u = x u - x 0 at h
    linarith
  have hl : Function.leftLim x t = x 0 + Function.leftLim p t - Function.leftLim n t := by
    calc
      _ = Function.leftLim (fun u ↦ x 0 + p u - n u) t :=
        congrArg (fun z ↦ Function.leftLim z t) heq
      _ = _ := leftLim_const_add_sub ht (x 0) (p.mono.tendsto_leftLim t) (n.mono.tendsto_leftLim t)
  rw [stieltjesMeasure_real_singleton, stieltjesMeasure_real_singleton, hl]
  have h := pathPositiveVariation_sub_negative x t
  change p t - n t = x t - x 0 at h
  change (p t - Function.leftLim p t) - (n t - Function.leftLim n t) = _
  linarith

theorem pathStieltjesIntegral_sub_leftLim
    (hf : ∀ T, IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    {t : ℝ≥0} (ht : 0 < t) :
    pathStieltjesIntegral x hx hr f t - Function.leftLim (pathStieltjesIntegral x hx hr f) t =
      f t * (x t - Function.leftLim x t) := by
  let p : ℝ≥0 → ℝ := fun r ↦ ∫ u in Ioc 0 r, f u ∂(positiveVariationStieltjes x hx hr).measure
  let n : ℝ≥0 → ℝ := fun r ↦ ∫ u in Ioc 0 r, f u ∂(negativeVariationStieltjes x hx hr).measure
  have hp := isCadlagPath_integral_Ioc (fun T ↦ integrableOn_positiveVariationStieltjes (hf T))
  have hn := isCadlagPath_integral_Ioc (fun T ↦ integrableOn_negativeVariationStieltjes (hf T))
  have hIp := integral_Ioc_sub_leftLim (fun T ↦ integrableOn_positiveVariationStieltjes (hf T)) ht
  have hIn := integral_Ioc_sub_leftLim (fun T ↦ integrableOn_negativeVariationStieltjes (hf T)) ht
  have hl : Function.leftLim (pathStieltjesIntegral x hx hr f) t =
      f 0 * x 0 + Function.leftLim p t - Function.leftLim n t := by
    have heq : pathStieltjesIntegral x hx hr f = fun r ↦ f 0 * x 0 + p r - n r := by
      funext r
      change f 0 * x 0 + (p r - n r) = _
      ring
    rw [heq]
    exact leftLim_const_add_sub ht _ (tendsto_leftLim_of_tendsto (hp.2 t (ne_of_gt ht)))
      (tendsto_leftLim_of_tendsto (hn.2 t (ne_of_gt ht)))
  rw [hl]
  change f 0 * x 0 + (p t - n t) -
    (f 0 * x 0 + Function.leftLim p t - Function.leftLim n t) = _
  change p t - Function.leftLim p t =
    ((positiveVariationStieltjes x hx hr).measure {t}).toReal * f t at hIp
  change n t - Function.leftLim n t =
    ((negativeVariationStieltjes x hx hr).measure {t}).toReal * f t at hIn
  have hm := variationStieltjes_measure_singleton_sub (x := x) (hx := hx) (hr := hr) ht
  calc
    _ = (p t - Function.leftLim p t) - (n t - Function.leftLim n t) := by ring
    _ = _ := by rw [hIp, hIn, ← sub_mul, hm, mul_comm]

end StochLean

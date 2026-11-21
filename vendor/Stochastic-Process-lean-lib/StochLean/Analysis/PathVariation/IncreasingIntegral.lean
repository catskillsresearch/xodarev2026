/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.MonotoneIntegralMeasure
public import StochLean.Analysis.PathVariation.StieltjesIntegralRegularity

/-! # Nonnegative Stieltjes integrands give increasing integral paths

The existing signed pathwise integral is used. Its initial product is a
constant in time and need not be positive or integrable in probability.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace StochLean

theorem monotone_pathStieltjesIntegral_of_nonneg {x H : ℝ≥0 → ℝ}
    (hx : Monotone x) (hr : ∀ t, ContinuousWithinAt x (Ici t) t)
    (hv : LocallyBoundedVariationOn x univ)
    (hi : ∀ T, IntegrableOn H (Ioc 0 T) (totalVariationStieltjes x hv hr).measure)
    (hH : ∀ t, 0 ≤ H t) : Monotone (pathStieltjesIntegral x hv hr H) := by
  let A : StieltjesFunction ℝ≥0 := ⟨x, hx, hr⟩
  have hiA : ∀ T, IntegrableOn H (Ioc 0 T) A.measure := by
    intro T
    have h := hi T
    change IntegrableOn H (Ioc 0 T) (totalVariationStieltjes A hv A.right_continuous).measure at h
    rwa [totalVariationStieltjes_measure_of_stieltjes] at h
  have hm := monotone_integral_Ioc_of_nonneg hiA hH
  intro s t hst
  change pathStieltjesIntegral A hv A.right_continuous H s ≤
    pathStieltjesIntegral A hv A.right_continuous H t
  simp only [pathStieltjesIntegral_eq_stieltjesIntegral]
  exact add_le_add le_rfl (hm hst)

end StochLean

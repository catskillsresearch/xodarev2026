/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeJumpSeries
public import StochLean.Probability.Process.Semimartingale.Ito.VectorJumpSummability

/-! # Finite variation of actual vector Ito jump corrections -/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}

theorem hasFiniteVariationPaths_frechet_first_order_jump_remainders
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    HasFiniteVariationPaths (fun t ω ↦ ∑' s : Ioc 0 t,
      (f (fun i ↦ X i s ω) - f (fun i ↦ leftLimitProcess (X i) s ω) -
        fderiv ℝ f (fun i ↦ leftLimitProcess (X i) s ω)
          (fun i ↦ jumpProcess (X i) s ω))) P := by
  filter_upwards [summable_abs_frechet_semimartingale_jump_remainders hX hF hf] with ω hs
  exact locallyBoundedVariationOn_tsum_Ioc
    (g := fun s ↦ f (fun i ↦ X i s ω) - f (fun i ↦ leftLimitProcess (X i) s ω) -
      fderiv ℝ f (fun i ↦ leftLimitProcess (X i) s ω) (fun i ↦ jumpProcess (X i) s ω))
    (fun t ↦ (hs t).1)

theorem hasFiniteVariationPaths_frechet_second_order_jump_remainders
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    HasFiniteVariationPaths (fun t ω ↦ ∑' s : Ioc 0 t,
      frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
        (fun i ↦ X i s ω)) P := by
  filter_upwards [summable_abs_frechet_semimartingale_jump_remainders hX hF hf] with ω hs
  exact locallyBoundedVariationOn_tsum_Ioc
    (g := fun s ↦ frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
      (fun i ↦ X i s ω)) (fun t ↦ (hs t).2)

end ProbabilityTheory

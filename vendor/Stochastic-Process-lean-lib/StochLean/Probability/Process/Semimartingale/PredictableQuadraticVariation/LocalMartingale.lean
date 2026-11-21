/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.GeneralLocalMartingale

/-! # The square characterization of actual predictable quadratic variation

On the proved existence domain, the selected angle process compensates the
square of a general native local martingale. The ordinary raw bracket first
compensates that square, and its actual predictable compensator supplies the
remaining local martingale. Uniqueness is against arbitrary predictable FV
competitors with AE zero initial value.

No locally-L2 or initial-moment assumption is imposed. In particular the
square-minus-angle process retains the original initial square, whereas
square-minus-raw-quadratic-variation starts at zero almost surely.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsLocalMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- The actual angle process compensates the square on its legal existence
domain, even when the original initial square is not integrable. -/
theorem isLocalMartingale_sq_sub_predictableQuadraticVariation
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation ((hM.isSemimartingale hF).quadraticVariation hF) F P) :
    IsLocalMartingale (fun t ω ↦ (M t ω) ^ 2 -
      (hM.isSemimartingale hF).predictableQuadraticVariation hF hQ t ω) F P := by
  let hSM := hM.isSemimartingale hF
  obtain ⟨hpA, _, _, _, _, hR⟩ := hSM.predictableQuadraticVariation_properties hF hQ
  apply ((hM.isLocalMartingale_sq_sub_quadraticVariation hF).add hR hF).congr hF
    (fun t ↦ ((hM.1 t).pow_const 2).sub (hpA.stronglyAdapted.adapted t))
  exact Eventually.of_forall fun ω t ↦ by
    change ((M t ω) ^ 2 - hSM.quadraticVariation hF t ω) +
      (hSM.quadraticVariation hF t ω - hSM.predictableQuadraticVariation hF hQ t ω) =
        (M t ω) ^ 2 - hSM.predictableQuadraticVariation hF hQ t ω
    ring

/-- A normalized predictable FV process compensates the square exactly when
it is indistinguishable from the actual selected angle process. -/
theorem isLocalMartingale_sq_sub_iff_predictableQuadraticVariation
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation ((hM.isSemimartingale hF).quadraticVariation hF) F P)
    {B : ℝ≥0 → Ω → ℝ} (hpB : IsStronglyPredictable F B)
    (hvB : HasFiniteVariationPaths B P) (hB0 : B 0 =ᵐ[P] 0) :
    IsLocalMartingale (fun t ω ↦ (M t ω) ^ 2 - B t ω) F P ↔
      Indistinguishable
        ((hM.isSemimartingale hF).predictableQuadraticVariation hF hQ) B P := by
  let hSM := hM.isSemimartingale hF
  constructor
  · intro hMB
    apply hSM.predictableQuadraticVariation_unique hF hQ hpB hvB hB0
    apply (hMB.sub (hM.isLocalMartingale_sq_sub_quadraticVariation hF) hF).congr hF
      ((hSM.adapted_quadraticVariation hF).sub hpB.stronglyAdapted.adapted)
    exact Eventually.of_forall fun ω t ↦ by
      change ((M t ω) ^ 2 - B t ω) - ((M t ω) ^ 2 - hSM.quadraticVariation hF t ω) =
        hSM.quadraticVariation hF t ω - B t ω
      ring
  · intro he
    apply (hM.isLocalMartingale_sq_sub_predictableQuadraticVariation hF hQ).congr hF
      (fun t ↦ ((hM.1 t).pow_const 2).sub (hpB.stronglyAdapted.adapted t))
    filter_upwards [he] with ω hω t
    change (M t ω) ^ 2 - hSM.predictableQuadraticVariation hF hQ t ω = (M t ω) ^ 2 - B t ω
    rw [hω t]

end ProbabilityTheory.IsLocalMartingale

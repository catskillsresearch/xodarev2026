/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation
public import
StochLean.Probability.Process.Semimartingale.QuadraticCovariation.GeneralLocalMartingale

/-! # The product characterization of actual predictable covariation

On the actual raw-covariation locally-integrable-variation domain, the
selected mixed angle process compensates the product of two general native
local martingales. The proved raw product compensation and the canonical
raw-minus-angle remainder are added, without a locally-L2 hypothesis.

Conversely, every normalized predictable FV process compensating the product
is identified with the selected mixed angle by its full uniqueness theorem.
No cadlag or locally-integrable-variation assumption is imposed on that
competitor. The product-minus-angle process retains the original initial
product; neither initial value nor their product is assumed integrable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsLocalMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M N : ℝ≥0 → Ω → ℝ}

/-- The actual mixed angle compensates a general local-martingale product
on its legal raw-covariation domain, without any additional initial moment. -/
theorem isLocalMartingale_mul_sub_predictableQuadraticCovariation
    (hM : IsLocalMartingale M F P) (hN : IsLocalMartingale N F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation
      ((hM.isSemimartingale hF).quadraticCovariation (hN.isSemimartingale hF) hF) F P) :
    IsLocalMartingale (M * N -
      (hM.isSemimartingale hF).predictableQuadraticCovariation (hN.isSemimartingale hF) hF hQ)
      F P := by
  let hSM := hM.isSemimartingale hF
  let hSN := hN.isSemimartingale hF
  obtain ⟨hpA, _, _, _, hR⟩ := hSM.predictableQuadraticCovariation_properties hSN hF hQ
  apply ((hM.isLocalMartingale_mul_sub_quadraticCovariation hN hF).add hR hF).congr hF
    (fun t ↦ ((hM.1 t).mul (hN.1 t)).sub (hpA.stronglyAdapted.adapted t))
  exact Eventually.of_forall fun ω t ↦ by
    change (M t ω * N t ω - hSM.quadraticCovariation hSN hF t ω) +
      (hSM.quadraticCovariation hSN hF t ω -
        hSM.predictableQuadraticCovariation hSN hF hQ t ω) =
      M t ω * N t ω - hSM.predictableQuadraticCovariation hSN hF hQ t ω
    ring

/-- A normalized predictable FV process compensates the product exactly
when it is indistinguishable from the actual selected mixed angle process. -/
theorem isLocalMartingale_mul_sub_iff_predictableQuadraticCovariation
    (hM : IsLocalMartingale M F P) (hN : IsLocalMartingale N F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation
      ((hM.isSemimartingale hF).quadraticCovariation (hN.isSemimartingale hF) hF) F P)
    {B : ℝ≥0 → Ω → ℝ} (hpB : IsStronglyPredictable F B)
    (hvB : HasFiniteVariationPaths B P) (hB0 : B 0 =ᵐ[P] 0) :
    IsLocalMartingale (M * N - B) F P ↔
      Indistinguishable ((hM.isSemimartingale hF).predictableQuadraticCovariation
        (hN.isSemimartingale hF) hF hQ) B P := by
  let hSM := hM.isSemimartingale hF
  let hSN := hN.isSemimartingale hF
  constructor
  · intro hMB
    apply hSM.predictableQuadraticCovariation_unique hSN hF hQ hpB hvB hB0
    apply (hMB.sub (hM.isLocalMartingale_mul_sub_quadraticCovariation hN hF) hF).congr hF
      ((hSM.adapted_quadraticCovariation hSN hF).sub hpB.stronglyAdapted.adapted)
    exact Eventually.of_forall fun ω t ↦ by
      change (M t ω * N t ω - B t ω) -
        (M t ω * N t ω - hSM.quadraticCovariation hSN hF t ω) =
        hSM.quadraticCovariation hSN hF t ω - B t ω
      ring
  · intro he
    apply (hM.isLocalMartingale_mul_sub_predictableQuadraticCovariation hN hF hQ).congr hF
      (fun t ↦ ((hM.1 t).mul (hN.1 t)).sub (hpB.stronglyAdapted.adapted t))
    filter_upwards [he] with ω hω t
    change M t ω * N t ω - hSM.predictableQuadraticCovariation hSN hF hQ t ω =
      M t ω * N t ω - B t ω
    rw [hω t]

end ProbabilityTheory.IsLocalMartingale

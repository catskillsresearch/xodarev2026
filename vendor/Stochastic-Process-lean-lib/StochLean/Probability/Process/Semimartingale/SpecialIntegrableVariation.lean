/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.CanonicalDecomposition
public import StochLean.Probability.Process.FiniteVariation.PredictableLocallyIntegrable
public import StochLean.Probability.Process.FiniteVariation.CompensatorInitial

/-! # Special decompositions and locally integrable variation

The actual canonical predictable FV part has locally integrable variation.
Conversely, an adapted cadlag decomposition with a locally integrable variation
part is made special by constructing that part's actual predictable compensator
and absorbing its local-martingale remainder into the original martingale part.

Both normalized components retain almost-sure zero initial values, while the
original random initial value stays outside their sum. No initial moment,
proposed compensator, new selector, or converse good-integrator theorem is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}

/-- The selected canonical FV part satisfies the actual local integrability
property; this is derived from predictability and FV, not a field assumed by
the special-semimartingale predicate. -/
theorem IsSpecialSemimartingale.canonicalFiniteVariationPart_hasLocallyIntegrableVariation
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) :
    HasLocallyIntegrableVariation hX.canonicalFiniteVariationPart F P := by
  obtain ⟨_, hp, hc, hv, _, _, _⟩ := hX.canonicalDecomposition_properties hF
  exact hp.hasLocallyIntegrableVariation hF hc hv

/-- Specialness is equivalent to an actual normalized decomposition with an
adapted cadlag locally integrable variation part. The latter need not already
be predictable: its predictable replacement is genuinely constructed. -/
theorem isSpecialSemimartingale_iff_exists_locallyIntegrableVariation_decomposition
    (hF : F.IsUsual P) :
    IsSpecialSemimartingale X F P ↔
      Adapted F X ∧ HasCadlagPaths X P ∧
        ∃ M A : ℝ≥0 → Ω → ℝ,
          IsLocalMartingale M F P ∧ Adapted F A ∧ HasCadlagPaths A P ∧
          HasLocallyIntegrableVariation A F P ∧ M 0 =ᵐ[P] 0 ∧ A 0 =ᵐ[P] 0 ∧
          Indistinguishable X ((fun _ ↦ X 0) + M + A) P := by
  constructor
  · rintro ⟨haX, hcX, M, A, hM, hpA, hcA, hvA, hM0, hA0, he⟩
    exact ⟨haX, hcX, M, A, hM, hpA.stronglyAdapted.adapted, hcA,
      hpA.hasLocallyIntegrableVariation hF hcA hvA, hM0, hA0, he⟩
  · rintro ⟨haX, hcX, M, A, hM, haA, hcA, hvA, hM0, hA0, he⟩
    obtain ⟨B, hpB, hcB, hB0, hvB, hU, _⟩ :=
      hvA.exists_unique_predictable_compensator haA hF hcA
    let N := M + (A - B)
    have hN : IsLocalMartingale N F P := hM.add hU hF
    have hN0 : N 0 =ᵐ[P] 0 := by
      filter_upwards [hM0, hA0] with ω hm ha
      change M 0 ω + (A 0 ω - B 0 ω) = 0
      simp only [hm, ha, hB0, Pi.zero_apply, sub_self, add_zero]
    refine ⟨haX, hcX, N, B, hN, hpB, Eventually.of_forall hcB,
      hvB.hasFiniteVariationPaths, hN0,
      Eventually.of_forall (fun ω ↦ congrFun hB0 ω), ?_⟩
    filter_upwards [he] with ω hω t
    change X t ω = (X 0 ω + (M t ω + (A t ω - B t ω))) + B t ω
    calc
      _ = (X 0 ω + M t ω) + A t ω := hω t
      _ = _ := by ring

end ProbabilityTheory

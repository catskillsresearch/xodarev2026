/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Pulling actual martingales back along a measure-preserving map

The source filtration is required to be the actual inverse-image filtration,
not an arbitrary enlargement. Every source-time event is an inverse image
of an event in the target-time field, so its martingale integral identity
follows from actual restricted pushforward integration.

The natural filtration of a composed process is exactly this inverse
image of the original natural filtration. No injectivity, sample-space
isomorphism, independent extra randomness or completion is assumed.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped NNReal

namespace MeasureTheory

variable {Ω Ξ : Type*} {mΩ : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- Composition of the sample map pulls back each actual natural field. -/
theorem Filtration.natural_comp_eq_comap {φ : Ω → Ξ} (hφ : Measurable φ)
    {E : Type*} [TopologicalSpace E] [MetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ℝ≥0 → Ξ → E} (hX : ∀ t, StronglyMeasurable (X t)) (t : ℝ≥0) :
    Filtration.natural (fun t ω ↦ X t (φ ω))
      (fun t ↦ (hX t).comp_measurable hφ) t =
        MeasurableSpace.comap φ (Filtration.natural X hX t) := by
  change (⨆ s ≤ t, MeasurableSpace.comap (fun ω ↦ X s (φ ω))
      (inferInstance : MeasurableSpace E)) =
    MeasurableSpace.comap φ
      (⨆ s ≤ t, MeasurableSpace.comap (X s) (inferInstance : MeasurableSpace E))
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]

/-- A true real martingale pulls back to the exact inverse-image filtration
along a measure-preserving map. No injectivity of the sample map is needed. -/
theorem Martingale.comp_measurePreserving {P : Measure Ω} {Q : Measure Ξ}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {φ : Ω → Ξ}
    (hφ : MeasurePreserving φ P Q) {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ}
    {X : ℝ≥0 → Ξ → ℝ} (hX : Martingale X G Q)
    (hF : ∀ t, F t = MeasurableSpace.comap φ (G t)) :
    Martingale (fun t ω ↦ X t (φ ω)) F P := by
  have hm : StronglyAdapted F (fun t ω ↦ X t (φ ω)) := by
    intro t
    rw [hF t]
    exact (hX.stronglyMeasurable t).comp_measurable (comap_measurable φ)
  have hi (t : ℝ≥0) : Integrable (fun ω ↦ X t (φ ω)) P :=
    hφ.integrable_comp_of_integrable (hX.integrable t)
  refine ⟨hm, fun s t hst ↦ ?_⟩
  apply EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun _ _ _ ↦ (hi s).integrableOn) ?_ (hm s).aestronglyMeasurable
  intro E hE _
  rw [hF s] at hE
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hE
  have hchange (q : ℝ≥0) :
      (∫ ω in φ ⁻¹' B, X q (φ ω) ∂P) = ∫ ξ in B, X q ξ ∂Q := by
    calc
      (∫ ω in φ ⁻¹' B, X q (φ ω) ∂P) =
          ∫ ξ, X q ξ ∂Measure.map φ (P.restrict (φ ⁻¹' B)) :=
        (integral_map_of_stronglyMeasurable hφ.measurable
          ((hX.stronglyMeasurable q).mono (G.le q))).symm
      _ = ∫ ξ in B, X q ξ ∂Q := by
        rw [(hφ.restrict_preimage (G.le s B hB)).map_eq]
  exact (hchange s).trans ((hX.setIntegral_eq hst hB).trans (hchange t).symm)

end MeasureTheory

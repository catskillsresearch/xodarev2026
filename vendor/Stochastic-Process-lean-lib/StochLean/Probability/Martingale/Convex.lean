/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.Convex.Continuous

/-! # Convex transformations of martingales and submartingales

These process interfaces reuse Mathlib's finite-dimensional conditional
Jensen inequality (Protter I.19 and its two corollaries). Convexity on the
whole finite-dimensional space supplies continuity. Integrability of the
transformed coordinates remains explicit. Monotonicity is needed for a
submartingale input, but not for a true martingale.
-/

@[expose] public section

open Filter Set

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Preorder ι] {F : Filtration ι mΩ} [SigmaFiniteFiltration P F]

theorem Martingale.convex_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {X : ι → Ω → E} {φ : E → ℝ}
    (hX : Martingale X F P) (hφ : ConvexOn ℝ Set.univ φ)
    (hi : ∀ t, Integrable (φ ∘ X t) P) : Submartingale (fun t ↦ φ ∘ X t) F P := by
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  refine ⟨fun t ↦ hc.comp_stronglyMeasurable (hX.stronglyMeasurable t), ?_, hi⟩
  intro s t hst
  filter_upwards [hφ.map_condExp_le_of_finiteDimensional (F.le s) (hX.integrable t) (hi t),
    hX.condExp_ae_eq hst] with ω hj hm
  simpa only [Function.comp_apply, hm] using hj

theorem Submartingale.convex_monotone_comp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    (hX : Submartingale X F P) (hφ : ConvexOn ℝ Set.univ φ) (hm : Monotone φ)
    (hi : ∀ t, Integrable (φ ∘ X t) P) : Submartingale (fun t ↦ φ ∘ X t) F P := by
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  refine ⟨fun t ↦ hc.comp_stronglyMeasurable (hX.stronglyMeasurable t), ?_, hi⟩
  intro s t hst
  filter_upwards [hφ.map_condExp_le_of_finiteDimensional (F.le s) (hX.integrable t) (hi t),
    hX.ae_le_condExp hst] with ω hj hstω
  exact (hm hstω).trans hj

end MeasureTheory

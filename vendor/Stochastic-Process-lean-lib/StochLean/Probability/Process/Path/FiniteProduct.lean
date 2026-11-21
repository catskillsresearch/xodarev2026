/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Cadlag coordinate products and their actual left limits

The deterministic product property holds for arbitrary index types. The
common-event stochastic assertion requires countably many coordinates.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ProbabilityTheory

theorem isCadlagPath_pi_iff {T ι : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)] {x : T → ∀ i, E i} :
    IsCadlagPath x ↔ ∀ i, IsCadlagPath (fun t ↦ x t i) := by
  constructor
  · intro hx i
    refine ⟨fun t ↦ (continuous_apply i).continuousAt.comp_continuousWithinAt (hx.1 t), ?_⟩
    intro t ht
    obtain ⟨y, hy⟩ := hx.2 t ht
    exact ⟨y i, ((continuous_apply i).tendsto y).comp hy⟩
  · intro hx
    refine ⟨fun t ↦ continuousWithinAt_pi.mpr (fun i ↦ (hx i).1 t), ?_⟩
    intro t ht
    choose y hy using fun i ↦ (hx i).2 t ht
    exact ⟨y, tendsto_pi_nhds.mpr hy⟩

theorem HasCadlagPaths.pi {T Ω ι : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
    {mΩ : MeasurableSpace Ω} {E : ι → Type*} [∀ i, TopologicalSpace (E i)] [Countable ι]
    {X : (i : ι) → T → Ω → E i} {P : Measure Ω} (hX : ∀ i, HasCadlagPaths (X i) P) :
    HasCadlagPaths (fun t ω i ↦ X i t ω) P := by
  have h : ∀ᵐ ω ∂P, ∀ i, IsCadlagPath (X i · ω) := ae_all_iff.mpr hX
  exact h.mono fun _ hω ↦ isCadlagPath_pi_iff.mpr hω

theorem IsCadlagPath.leftLim_pi {ι : Type*} {x : ℝ≥0 → ι → ℝ}
    (hx : IsCadlagPath x) (t : ℝ≥0) : Function.leftLim x t = fun i ↦
      Function.leftLim (fun s ↦ x s i) t := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    apply leftLim_eq_of_tendsto
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_leftLim_of_tendsto ((isCadlagPath_pi_iff.mp hx i).2 t ht)

end ProbabilityTheory

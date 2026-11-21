/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Operations on uniformly integrable families -/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞}

theorem UniformIntegrable.reindex {κ : Type*} (hX : UniformIntegrable X p P) (e : κ → ι) :
    UniformIntegrable (fun k ↦ X (e k)) p P := by
  obtain ⟨C, hC⟩ := hX.2.2
  refine ⟨fun k ↦ hX.1 (e k), ?_, C, fun k ↦ hC (e k)⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hX.2.1 hε
  exact ⟨δ, hδ, fun k ↦ hδε (e k)⟩

theorem UniformIntegrable.indicator (hX : UniformIntegrable X p P)
    {s : Set Ω} (hs : MeasurableSet s) :
    UniformIntegrable (fun t ↦ s.indicator (X t)) p P := by
  obtain ⟨C, hC⟩ := hX.2.2
  exact ⟨fun t ↦ (hX.1 t).indicator hs, hX.2.1.indicator s,
    C, fun t ↦ (eLpNorm_indicator_le _).trans (hC t)⟩

theorem UniformIntegrable.add (hX : UniformIntegrable X p P)
    (hY : UniformIntegrable Y p P) (hp : 1 ≤ p) :
    UniformIntegrable (X + Y) p P := by
  obtain ⟨C, hC⟩ := hX.2.2
  obtain ⟨D, hD⟩ := hY.2.2
  refine ⟨fun t ↦ (hX.1 t).add (hY.1 t),
    hX.2.1.add hY.2.1 hp hX.1 hY.1, C + D, fun t ↦ ?_⟩
  exact (eLpNorm_add_le (hX.1 t) (hY.1 t) hp).trans (by
    simpa only [ENNReal.coe_add] using add_le_add (hC t) (hD t))

/-- A measurable family dominated in norm by a UI family is UI. -/
theorem UniformIntegrable.mono_norm (hY : UniformIntegrable Y p P)
    (hX : ∀ i, AEStronglyMeasurable (X i) P)
    (hXY : ∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ ‖Y i ω‖) : UniformIntegrable X p P := by
  obtain ⟨C, hC⟩ := hY.2.2
  refine ⟨hX, ?_, C, fun i ↦ (eLpNorm_mono_ae (hXY i)).trans (hC i)⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hY.2.1 hε
  refine ⟨δ, hδ, fun i s hs hPs ↦ ?_⟩
  apply le_trans (eLpNorm_mono_ae ?_) (hδε i s hs hPs)
  filter_upwards [hXY i] with ω hω
  by_cases hmem : ω ∈ s <;> simp [hmem, hω]

end MeasureTheory

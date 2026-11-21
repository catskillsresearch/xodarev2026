/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Complex
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Martingale.Complex

/-! # Compact integrable envelopes promote complex local martingales -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsComplexLocalMartingale.martingale_of_integrable_envelope
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {Z : ℝ≥0 → Ω → ℂ}
    (hZ : IsComplexLocalMartingale Z F P)
    (hb : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖Z t ω‖ ≤ R ω) : Martingale Z F P := by
  apply martingale_complex_iff.mpr
  constructor
  · apply hZ.1.martingale_of_integrable_envelope
    intro T
    obtain ⟨R, hR, hbound⟩ := hb T
    refine ⟨R, hR, hbound.mono (fun ω h t ht ↦ ?_)⟩
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (Z t ω)).trans (h t ht)
  · apply hZ.2.martingale_of_integrable_envelope
    intro T
    obtain ⟨R, hR, hbound⟩ := hb T
    refine ⟨R, hR, hbound.mono (fun ω h t ht ↦ ?_)⟩
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm (Z t ω)).trans (h t ht)

end ProbabilityTheory

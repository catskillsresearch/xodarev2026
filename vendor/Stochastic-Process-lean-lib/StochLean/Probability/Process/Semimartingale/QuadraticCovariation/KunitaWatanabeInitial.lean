/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.KunitaWatanabe
public import StochLean.Analysis.PathVariation.StieltjesKunitaWatanabeInitial

/-! # Kunita--Watanabe including the original initial product and squares

The initial absolute product is added separately to the increment variation
integral. Both energy terms retain their original initial squares. Initial
variables need not be integrable and weights/energies need not be bounded.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.exists_kunitaWatanabe_with_initial
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P,
      ∃ (hv : LocallyBoundedVariationOn (fun t ↦ hX.quadraticCovariation hY hF t ω) univ)
        (hr : ∀ t, ContinuousWithinAt (fun u ↦ hX.quadraticCovariation hY hF u ω) (Ici t) t)
        (B C : StieltjesFunction ℝ≥0),
        (∀ t, B t = hX.quadraticVariation hF t ω) ∧
        (∀ t, C t = hY.quadraticVariation hF t ω) ∧
        ∀ (f g : ℝ≥0 → ℝ≥0∞), Measurable f → Measurable g →
          ((‖X 0 ω‖₊ * ‖Y 0 ω‖₊ : ℝ≥0) : ℝ≥0∞) * (f 0 * g 0) +
            (∫⁻ t, f t * g t ∂(totalVariationStieltjes _ hv hr).measure) ≤
          (((‖X 0 ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * (f 0) ^ 2 +
            (∫⁻ t, (f t) ^ 2 ∂B.measure)) ^ (1 / 2 : ℝ) *
          (((‖Y 0 ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * (g 0) ^ 2 +
            (∫⁻ t, (g t) ^ 2 ∂C.measure)) ^ (1 / 2 : ℝ) := by
  filter_upwards [hX.exists_kunitaWatanabe_stieltjes hY hF,
    hX.abs_quadraticCovariation_increment_le hY hF] with ω hdata hinc
  obtain ⟨hv, hr, B, C, hB, hC, _⟩ := hdata
  refine ⟨hv, hr, B, C, hB, hC, ?_⟩
  intro f g hf hg
  apply stieltjes_lintegral_mul_le_with_initial_atom hv hr B C ?_ ‖X 0 ω‖₊ ‖Y 0 ω‖₊ hf hg
  intro s t hst
  simpa only [hB, hC] using hinc s t hst

end ProbabilityTheory

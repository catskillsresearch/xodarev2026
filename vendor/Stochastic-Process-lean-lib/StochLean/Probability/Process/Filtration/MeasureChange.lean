/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Usual
public import StochLean.ForMathlib.MeasureTheory.Measure.ProbabilityMixture

/-! # Usual filtrations under dominating measures

If `P ≪ Q`, every `Q`-null set is `P`-null. Thus `P`-usual conditions imply
`Q`-usual conditions, not conversely. A probability mixture dominates each of
its positive-weight components; at least one such component exists.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [PartialOrder ι] [OrderBot ι]
  {F : Filtration ι mΩ} {P Q : Measure Ω}

theorem IsUsual.of_absolutelyContinuous (hF : F.IsUsual P) (hPQ : P ≪ Q) :
    F.IsUsual Q :=
  ⟨hF.1, fun s hs ↦ hF.2 s (hPQ hs)⟩

theorem IsUsual.probability_mixture {κ : Type*} [Countable κ]
    (P : κ → Measure Ω) (c : κ → ℝ≥0) (hc : (∑' k, (c k : ℝ≥0∞)) = 1)
    (hF : ∀ k, F.IsUsual (P k)) :
    F.IsUsual (Measure.sum (fun k ↦ (c k : ℝ≥0∞) • P k)) := by
  have hex : ∃ k, c k ≠ 0 := by
    by_contra hn
    have hz : ∀ k, c k = 0 := by simpa only [not_exists, not_not] using hn
    simp only [hz, ENNReal.coe_zero, tsum_zero] at hc
    exact zero_ne_one hc
  obtain ⟨k, hk⟩ := hex
  exact (hF k).of_absolutelyContinuous (Measure.absolutelyContinuous_probability_mixture P c hk)

end MeasureTheory.Filtration

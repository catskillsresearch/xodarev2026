/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ReverseOneSided
public import StochLean.Probability.Process.Filtration.SubmartingaleReindex
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # Uniform integrability along decreasing deterministic times

A decreasing clock turns a one-sided martingale into a native reverse
one-sided martingale. Its expected values are bounded by the initial expected
value in the appropriate direction, so reverse UI applies. No path regularity
or second moments are needed, and repeated sampling times are allowed.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [Preorder ι] [OrderBot ι] {F : Filtration ι mΩ} {X : ι → Ω → ℝ}

theorem Supermartingale.uniformIntegrable_antitone_reindex
    (hX : Supermartingale X F P) {a : ℕ → ι} (ha : Antitone a) :
    UniformIntegrable (fun n ↦ X (a n)) 1 P := by
  let e : ℕᵒᵈ → ι := fun n ↦ a (OrderDual.ofDual n)
  have he : Monotone e := fun _ _ hij ↦ ha hij
  have hY := hX.reindex e he
  have hUI := hY.uniformIntegrable_of_reverse_expectation_bounded
    (C := ∫ ω, X ⊥ ω ∂P) (fun n ↦ by
      simpa only [setIntegral_univ] using hX.setIntegral_le (i := ⊥) (j := e n) bot_le
        (@MeasurableSet.univ Ω (F ⊥)))
  exact hUI.reindex OrderDual.toDual

theorem Submartingale.uniformIntegrable_antitone_reindex
    (hX : Submartingale X F P) {a : ℕ → ι} (ha : Antitone a) :
    UniformIntegrable (fun n ↦ X (a n)) 1 P := by
  apply (hX.neg.uniformIntegrable_antitone_reindex ha).mono_norm
    (fun n ↦ (hX.integrable (a n)).aestronglyMeasurable)
  intro n
  exact Filter.Eventually.of_forall fun ω ↦ (norm_neg (X (a n) ω)).ge

end MeasureTheory

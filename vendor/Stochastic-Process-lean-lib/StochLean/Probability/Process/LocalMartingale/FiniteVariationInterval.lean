/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.ContinuousFiniteVariation
public import StochLean.Probability.Process.Path.FiniteVariationInterval

/-! # Protter II.27, Corollary 1: finite variation on a stochastic interval

Finite variation is required only inside the selected interval, on each finite
subhorizon. The closed stopped processes agree, including zero and infinite
stopping times. No process value at an infinite time is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}
  {σ τ : Ω → WithTop ℝ≥0}

theorem IsContinuousLocalMartingale.stoppedProcess_eq_of_finiteVariation_interval
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω)
    (hv : ∀ᵐ ω ∂P, σ ω < τ ω → ∀ b : ℝ≥0, (b : WithTop ℝ≥0) ≤ τ ω →
      BoundedVariationOn (X · ω) (Ioo (σ ω).untopA b)) :
    Indistinguishable (MeasureTheory.stoppedProcess X τ)
      (MeasureTheory.stoppedProcess X σ) P := by
  have hM : IsContinuousLocalMartingale
      (MeasureTheory.stoppedProcess X τ - MeasureTheory.stoppedProcess X σ) F P := by
    refine ⟨(hX.1.stoppedProcess hF hτ).sub (hX.1.stoppedProcess hF hσ) hF, ?_⟩
    filter_upwards [hX.2.stoppedProcess τ, hX.2.stoppedProcess σ] with ω ht hs
    exact ht.sub hs
  have hV : HasFiniteVariationPaths
      (MeasureTheory.stoppedProcess X τ - MeasureTheory.stoppedProcess X σ) P := by
    filter_upwards [hX.1.2.1, hle, hv] with ω hc ho hvω
    rcases ho.eq_or_lt with he | hl
    · have heq : (fun t ↦ (MeasureTheory.stoppedProcess X τ -
          MeasureTheory.stoppedProcess X σ) t ω) = (fun _ ↦ (0 : ℝ)) := by
        funext t
        simp only [Pi.sub_apply, MeasureTheory.stoppedProcess, he, sub_self]
      rw [heq]
      exact (monotone_const.monotoneOn univ).locallyBoundedVariationOn
    · exact locallyBoundedVariationOn_stopped_difference_of_interval hc hl (hvω hl)
  have h0 : (MeasureTheory.stoppedProcess X τ - MeasureTheory.stoppedProcess X σ) 0 =ᵐ[P] 0 := by
    apply ae_of_all
    intro ω
    simp only [Pi.sub_apply, MeasureTheory.stoppedProcess, WithTop.coe_zero,
      min_eq_left (show (0 : WithTop ℝ≥0) ≤ τ ω from bot_le),
      min_eq_left (show (0 : WithTop ℝ≥0) ≤ σ ω from bot_le), sub_self, Pi.zero_apply]
  filter_upwards [hM.indistinguishable_zero_of_finiteVariation hF hV h0] with ω hω t
  exact sub_eq_zero.mp (hω t)

end ProbabilityTheory

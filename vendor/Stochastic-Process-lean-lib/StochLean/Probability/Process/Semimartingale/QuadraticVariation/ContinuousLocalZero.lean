/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousLocalMartingale
public import StochLean.Probability.Process.LocalMartingale.NonnegativeZero

/-! # A continuous local martingale with zero raw quadratic variation is zero

The raw bracket includes the initial square, so no separate initial-value
hypothesis is necessary. This is the zero-bracket assertion of Protter II.27.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.indistinguishable_zero_of_quadraticVariation_zero
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hQ : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF) 0 P) :
    Indistinguishable X 0 P := by
  let N := (fun t ω ↦ (X t ω) ^ 2) - (hX.isSemimartingale hF).quadraticVariation hF
  have hN : IsLocalMartingale N F P :=
    (hX.isContinuousLocalMartingale_sq_sub_quadraticVariation hF).1
  have hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ N t ω := by
    filter_upwards [hQ] with ω hω t
    simpa only [N, Pi.sub_apply, hω t, Pi.zero_apply, sub_zero] using sq_nonneg (X t ω)
  have h0 : N 0 =ᵐ[P] 0 := by
    filter_upwards [(hX.isSemimartingale hF).quadraticVariation_zero_ae hF] with ω hω
    simp only [N, Pi.sub_apply, hω, sub_self, Pi.zero_apply]
  filter_upwards [hN.indistinguishable_zero_of_nonneg hpos h0, hQ] with ω hn hq t
  have hs : (X t ω) ^ 2 = 0 := by
    simpa only [N, Pi.sub_apply, hq t, Pi.zero_apply, sub_zero] using hn t
  exact (sq_eq_zero_iff).mp hs

end ProbabilityTheory

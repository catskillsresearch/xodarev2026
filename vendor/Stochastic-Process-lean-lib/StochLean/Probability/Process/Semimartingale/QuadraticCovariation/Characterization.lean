/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Jump
public import StochLean.Probability.Process.LocalMartingale.FiniteVariationUniqueness

/-! # Protter II.27, Corollary 2: characterization of raw mixed covariation

The canonical bracket is unique up to indistinguishability among adapted
cadlag FV processes with the stated local-martingale residual, jumps and
initial product. No predictable compensator or second bracket is constructed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y A : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_unique_of_locally_squareIntegrable
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hLX : Locally (fun M ↦ IsSquareIntegrableMartingale M F P) F X P)
    (hLY : Locally (fun M ↦ IsSquareIntegrableMartingale M F P) F Y P)
    (ha : Adapted F A) (hc : HasCadlagPaths A P) (hv : HasFiniteVariationPaths A P)
    (hM : IsLocalMartingale (X * Y - A) F P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 →
      jumpProcess A t ω = jumpProcess X t ω * jumpProcess Y t ω)
    (h0 : A 0 =ᵐ[P] fun ω ↦ X 0 ω * Y 0 ω) :
    Indistinguishable A (hX.quadraticCovariation hY hF) P := by
  apply indistinguishable_of_finiteVariation_localMartingale_residuals hF ha
    (hX.adapted_quadraticCovariation hY hF) hc
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hv
    (hX.hasFiniteVariationPaths_quadraticCovariation hY hF) hM
    (hX.isLocalMartingale_mul_sub_quadraticCovariation hY hF hLX hLY)
  · filter_upwards [hj, h0, hX.jumpProcess_quadraticCovariation hY hF] with ω hjω h0ω hq t
    rw [hq t]
    by_cases ht : t = 0
    · subst t
      simpa only [jumpProcess_zero] using h0ω
    · exact hjω t ht
  · exact h0.trans (hX.quadraticCovariation_zero_ae hY hF).symm

end ProbabilityTheory

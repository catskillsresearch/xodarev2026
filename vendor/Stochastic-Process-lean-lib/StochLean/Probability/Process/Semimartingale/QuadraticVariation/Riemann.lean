/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.CadlagRiemann
public import StochLean.Probability.Process.Partition.SquareSums
public import StochLean.Probability.Process.UCP.ExhaustingStopping

/-! # Random-partition square sums converge to the raw quadratic variation

Exact telescoping reduces the square sums to the stopped square minus twice
the left Riemann sum. Endpoint exhaustion and the proved cadlag-integrand
Riemann theorem then give UCP convergence, with the original initial square.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_quadraticVariationSumProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).quadraticVariationSumProcess X) atTop
      (hX.quadraticVariation hF) := by
  have hsq := hπ.tendstoUCP_min_terminal (fun t ω ↦ (X t ω) ^ 2)
  have hJ := hX.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag
    hF hX.adapted hX.hasCadlagPaths hπ
  have hu := hsq.sub (hJ.smul 2)
  have heq (n : ℕ) : (fun t ω ↦ (X (min ((π n).terminal ω) t) ω) ^ 2) -
      (2 : ℝ) • (π n).leftRiemannSumProcess X X = (π n).quadraticVariationSumProcess X := by
    funext t ω
    exact ((π n).quadraticVariationSumProcess_eq_square_sub_riemann X t ω).symm
  rw [show (fun n ↦ (fun t ω ↦ (X (min ((π n).terminal ω) t) ω) ^ 2) -
    (2 : ℝ) • (π n).leftRiemannSumProcess X X) =
      (fun n ↦ (π n).quadraticVariationSumProcess X) from funext heq] at hu
  exact hu

end ProbabilityTheory

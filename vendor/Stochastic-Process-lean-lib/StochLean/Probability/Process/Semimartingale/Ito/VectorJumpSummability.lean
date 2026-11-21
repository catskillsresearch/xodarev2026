/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPart
public import StochLean.Probability.Process.Path.FiniteProduct
public import StochLean.Analysis.PathVariation.VectorEnergy
public import StochLean.Analysis.PathVariation.VectorTaylorJumpSeries

/-! # Actual vector Taylor jump series for coordinate semimartingales

Every assertion is on one common event for all finite horizons. The only
stochastic brackets used are the existing real coordinate quadratic variations.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ}

theorem summable_norm_sq_semimartingale_coordinate_jumps
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ ‖fun i ↦ jumpProcess (X i) s ω‖ ^ 2) := by
  have h : ∀ᵐ ω ∂P, ∀ i, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ (jumpProcess (X i) s ω) ^ 2) :=
    ae_all_iff.mpr (fun i ↦ (hX i).summable_sq_jumps hF)
  filter_upwards [h] with ω hω t
  exact summable_norm_sq_pi_of_summable_sq
    (fun (s : Ioc 0 t) i ↦ jumpProcess (X i) s ω) (fun i ↦ hω i t)

theorem summable_abs_frechet_semimartingale_jump_remainders
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦
        |f (fun i ↦ X i s ω) - f (fun i ↦ leftLimitProcess (X i) s ω) -
          fderiv ℝ f (fun i ↦ leftLimitProcess (X i) s ω)
            (fun i ↦ jumpProcess (X i) s ω)|) ∧
      Summable (fun s : Ioc 0 t ↦
        |frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
          (fun i ↦ X i s ω)|) := by
  have hc := HasCadlagPaths.pi (fun i ↦ (hX i).hasCadlagPaths)
  filter_upwards [hc, summable_norm_sq_semimartingale_coordinate_jumps hX hF]
    with ω hx hs t
  have hl (s : Ioc 0 t) : Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ leftLimitProcess (X i) s ω := by
    rw [hx.leftLim_pi]
    funext i
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hj (s : Ioc 0 t) : (fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ jumpProcess (X i) s ω := by
    rw [hl]
    rfl
  have hs' : Summable (fun s : Ioc 0 t ↦
      ‖(fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s‖ ^ 2) := by
    simpa only [hj] using hs t
  have hj' (s : Ioc 0 t) : (fun i ↦ X i s ω) - (fun i ↦ leftLimitProcess (X i) s ω) =
      fun i ↦ jumpProcess (X i) s ω := rfl
  constructor
  · simpa only [hl, hj'] using summable_abs_frechet_first_order_jump_remainders hx hs' hf
  · simpa only [hl] using summable_abs_frechet_second_order_jump_remainders hx hs' hf

end ProbabilityTheory

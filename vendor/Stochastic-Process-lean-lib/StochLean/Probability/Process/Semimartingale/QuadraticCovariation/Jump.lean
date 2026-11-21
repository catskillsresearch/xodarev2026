/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation
public import StochLean.Probability.Process.Path.LeftLimitAddition

/-! # The jumps of raw quadratic covariation are products of the source jumps

The convention `ΔX₀ = X₀` is included; the assertion holds for all times
on one full-measure event.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.jumpProcess_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (jumpProcess (hX.quadraticCovariation hY hF))
      (fun t ω ↦ jumpProcess X t ω * jumpProcess Y t ω) P := by
  let S := (hX.add hY).quadraticVariation hF
  let A := hX.quadraticVariation hF
  let B := hY.quadraticVariation hF
  filter_upwards [hX.hasCadlagPaths, hY.hasCadlagPaths,
    (hX.add hY).hasCadlagPaths_quadraticVariation hF,
    hX.hasCadlagPaths_quadraticVariation hF, hY.hasCadlagPaths_quadraticVariation hF,
    (hX.add hY).jumpProcess_quadraticVariation hF,
    hX.jumpProcess_quadraticVariation hF, hY.jumpProcess_quadraticVariation hF]
    with ω hx hy hs ha hb hsj haj hbj t
  have hdiff : IsCadlagPath ((S - A - B) · ω) := (hs.sub ha).sub hb
  change jumpProcess (fun u v ↦ (1 / 2 : ℝ) * (S - A - B) u v) t ω = _
  rw [IsCadlagPath.jumpProcess_const_mul (X := S - A - B) hdiff,
    IsCadlagPath.jumpProcess_sub (X := S - A) (Y := B) (hs.sub ha) hb,
    IsCadlagPath.jumpProcess_sub (X := S) (Y := A) hs ha]
  change (1 / 2 : ℝ) * (jumpProcess ((hX.add hY).quadraticVariation hF) t ω -
    jumpProcess (hX.quadraticVariation hF) t ω - jumpProcess (hY.quadraticVariation hF) t ω) = _
  rw [hsj t, haj t, hbj t, hx.jumpProcess_add hy t]
  ring

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Filtration.Intersection
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessFiltration

/-! # Protter II.16: filtration invariance of the Chapter II integral

Approximate the common adapted caglad integrand in the intersection filtration,
which is usual. Transport the same simple processes to each original filtration;
their elementary integrals agree exactly. UCP uniqueness identifies the two
constructed integrals. Neither filtration needs to contain the other, and no
semimartingale assumption on a generated union filtration is made.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F G : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_congr_filtration
    (hXF : IsSemimartingale X F P) (hXG : IsSemimartingale X G P)
    (hF : F.IsUsual P) (hG : G.IsUsual P)
    (haF : Adapted F H) (haG : Adapted G H) (hr : HasCagladPaths H P) :
    Indistinguishable (hXF.stochasticIntegral hF haF hr)
      (hXG.stochasticIntegral hG haG hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP (haF.inf haG) (hF.inf hG) hr
  have hSF (n : ℕ) := (hS n).monoFiltration (fun _ ↦ inf_le_left)
  have hSG (n : ℕ) := (hS n).monoFiltration (fun _ ↦ inf_le_right)
  apply hXF.stochasticIntegral_indistinguishable_of_limit hF haF hr hSF huS
  · have hu := hXG.tendstoUCP_stochasticIntegral_of_simple hG haG hr hSG huS
    have heq (n : ℕ) : (hSG n).elementaryIntegralProcess X =
        (hSF n).elementaryIntegralProcess X := by
      rw [(hS n).elementaryIntegralProcess_monoFiltration (fun _ ↦ inf_le_right) X,
        (hS n).elementaryIntegralProcess_monoFiltration (fun _ ↦ inf_le_left) X]
    simpa only [heq] using hu
  · exact (hXG.hasCadlagPaths_stochasticIntegral hG haG hr).hasRightContinuousPaths

end ProbabilityTheory

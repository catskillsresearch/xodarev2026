/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.UCP
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Density
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessRegularity
public import StochLean.Probability.Process.UCP.Complete
public import StochLean.Probability.Process.UCP.Algebra

/-! # Construction of the Chapter II integral by simple UCP approximation

Density supplies an actual sequence, source continuity makes its elementary
integrals Cauchy, and UCP completeness constructs their adapted cadlag limit.
Linearity and source continuity then prove convergence for every simple
approximation of the same integrand. No integral operator is assumed as data.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.exists_elementaryIntegralProcess_limit
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {S : ℕ → ℝ≥0 → Ω → ℝ} (hS : ∀ n, IsSimplePredictable (S n) F)
    (hu : TendstoUCP P S atTop H) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J := by
  have hc : CauchyUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) :=
    hX.elementaryIntegralProcess_cauchyUCP hF hS hu.cauchyUCP
  exact hc.exists_adapted_cadlag_limit
    (fun n ↦ (hS n).adapted_elementaryIntegralProcess hX.adapted hF
      hX.hasCadlagPaths.hasRightContinuousPaths) hF
    (fun n ↦ (hS n).hasCadlagPaths_elementaryIntegralProcess hX.hasCadlagPaths)

/-- An actual limit exists and works for every source simple UCP approximation. -/
theorem IsSemimartingale.exists_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      ∀ S : ℕ → ℝ≥0 → Ω → ℝ, ∀ hS : ∀ n, IsSimplePredictable (S n) F,
        TendstoUCP P S atTop H →
          TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  obtain ⟨J, hJa, hJr, hJS⟩ := hX.exists_elementaryIntegralProcess_limit hF hS huS
  refine ⟨J, hJa, hJr, ?_⟩
  intro R hR huR
  have hd : TendstoUCP P (fun n ↦ R n - S n) atTop 0 := by
    simpa only [sub_self] using huR.sub huS
  have hJd := hX.tendstoUCP_elementaryIntegralProcess_zero hF (fun n ↦ (hR n).sub (hS n)) hd
  have hsum := hJd.add hJS
  have heq : (fun n ↦ ((hR n).sub (hS n)).elementaryIntegralProcess X +
      (hS n).elementaryIntegralProcess X) = fun n ↦ (hR n).elementaryIntegralProcess X := by
    funext n
    rw [(hR n).elementaryIntegralProcess_sub (hS n) X, sub_add_cancel]
  simpa only [heq, zero_add] using hsum

end ProbabilityTheory

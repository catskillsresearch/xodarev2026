/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.StoppedDifference
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality
public import StochLean.Probability.Process.Path.FiniteVariationInterval

/-! # Protter II.18 corollary: finite variation on a stochastic interval

On each selected path, open-interval finite variation yields finite variation
of `X^T - X^S`, with the right-endpoint jump retained. Its existing canonical
Stieltjes integral is the local interval integral: the integrator is zero up
to `S`, equals `X - X_S` on `(S,T]`, and is constant afterwards. No global
finite-variation hypothesis on `X` is made.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

/-- Open-interval BV on each finite subhorizon, allowing an infinite upper stopping time. -/
theorem IsSemimartingale.stochasticIntegral_eq_Stieltjes_on_interval
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    ∀ᵐ ω ∂P, σ ω < τ ω →
      (∀ b : ℝ≥0, (b : WithTop ℝ≥0) ≤ τ ω →
        BoundedVariationOn (X · ω) (Ioo (σ ω).untopA b)) →
      ∃ hv : LocallyBoundedVariationOn
        (fun t ↦ MeasureTheory.stoppedProcess X τ t ω - MeasureTheory.stoppedProcess X σ t ω) univ,
      ∃ hreg : IsCadlagPath
        (fun t ↦ MeasureTheory.stoppedProcess X τ t ω - MeasureTheory.stoppedProcess X σ t ω), ∀ t,
      MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ t ω -
        MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) σ t ω =
          pathStieltjesIntegral
            (fun s ↦ MeasureTheory.stoppedProcess X τ s ω - MeasureTheory.stoppedProcess X σ s ω)
            hv hreg.1 (H · ω) t := by
  have hZ := (hX.stoppedProcess hF hτ).sub (hX.stoppedProcess hF hσ)
  filter_upwards [hX.hasCadlagPaths,
    hZ.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr,
    hX.stochasticIntegral_stopped_difference hF ha hr hσ hτ] with ω hXω hFV hJ
  intro hστ hv
  have hvZ := locallyBoundedVariationOn_stopped_difference_of_interval hXω hστ hv
  obtain ⟨hrZ, hIZ⟩ := hFV hvZ
  exact ⟨hvZ, hrZ, fun t ↦ (hJ t).symm.trans (hIZ t)⟩

/-- For a finite upper endpoint, the source hypothesis is simply BV on `(S,T)`. -/
theorem IsSemimartingale.stochasticIntegral_eq_Stieltjes_on_finite_interval
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    ∀ᵐ ω ∂P, σ ω < τ ω → τ ω ≠ ⊤ →
      BoundedVariationOn (X · ω) (Ioo (σ ω).untopA (τ ω).untopA) →
      ∃ hv : LocallyBoundedVariationOn
        (fun t ↦ MeasureTheory.stoppedProcess X τ t ω - MeasureTheory.stoppedProcess X σ t ω) univ,
      ∃ hreg : IsCadlagPath
        (fun t ↦ MeasureTheory.stoppedProcess X τ t ω - MeasureTheory.stoppedProcess X σ t ω), ∀ t,
      MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ t ω -
        MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) σ t ω =
          pathStieltjesIntegral
            (fun s ↦ MeasureTheory.stoppedProcess X τ s ω - MeasureTheory.stoppedProcess X σ s ω)
            hv hreg.1 (H · ω) t := by
  filter_upwards [hX.stochasticIntegral_eq_Stieltjes_on_interval hF ha hr hσ hτ] with ω hω
  intro hστ hτfinite hv
  apply hω hστ
  intro b hb
  have hb' : b ≤ (τ ω).untopA := by
    apply WithTop.coe_le_coe.mp
    simpa only [WithTop.untopA_eq_untop hτfinite, WithTop.coe_untop] using hb
  exact hv.mono (fun _ hs ↦ ⟨hs.1, hs.2.trans_le hb'⟩)

end ProbabilityTheory

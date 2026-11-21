/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPart
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariation
public import StochLean.Probability.Process.FiniteVariation.CagladStieltjesIntegral
public import StochLean.Analysis.PathVariation.FiniteVariationCadlag

/-! # Integration against raw quadratic variation splits into continuous and jump parts

The Stieltjes realization is exactly the one used by the canonical continuous
quadratic variation. Indistinguishability invariance identifies its integral
with the existing raw-bracket integral, retaining the separate initial square.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_quadraticVariation_continuous_jump_decomposition
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr)
      (fun t ω ↦ H 0 ω * (X 0 ω) ^ 2 +
        (hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF ha hr t ω +
        ∑' s : Ioc 0 t, H s ω * (jumpProcess X s ω) ^ 2) P := by
  let D := Classical.choice (hX.nonempty_bracketRealization hX hF)
  let B : ℝ≥0 → Ω → ℝ := fun t ω ↦ D.left ω t
  have hvB : ∀ ω, LocallyBoundedVariationOn (B · ω) univ := fun ω ↦
    ((D.left ω).mono.monotoneOn univ).locallyBoundedVariationOn
  have hrB : ∀ ω, IsRightContinuousPath (B · ω) := fun ω ↦ (D.left ω).right_continuous
  have hcB : HasCadlagPaths B P := Eventually.of_forall fun ω ↦
    isCadlagPath_of_locallyBoundedVariation (hvB ω) (hrB ω)
  have hB : IsSemimartingale B F P :=
    (show HasFiniteVariationPaths B P from Eventually.of_forall hvB).isSemimartingale
      D.left_adapted hF hcB
  have hIB := ((hX.isSemimartingale_quadraticVariation hF).stochasticIntegral_congr_integrator
    hB hF ha hr D.left_eq).trans
      (hB.stochasticIntegral_eq_finiteVariationIntegral hF hvB hrB ha hr)
  have hvC : ∀ ω, LocallyBoundedVariationOn
      (hX.continuousQuadraticVariation hF · ω) univ := fun ω ↦
    ((hX.monotone_continuousQuadraticVariation hF ω).monotoneOn univ).locallyBoundedVariationOn
  have hrC : ∀ ω, IsRightContinuousPath (hX.continuousQuadraticVariation hF · ω) := fun ω t ↦
    (hX.continuous_continuousQuadraticVariation hF ω).continuousAt.continuousWithinAt
  have hIC := IsSemimartingale.stochasticIntegral_eq_finiteVariationIntegral
    (hX.isSemimartingale_continuousQuadraticVariation hF) hF hvC hrC ha hr
  filter_upwards [hr, D.left_eq, hX.quadraticVariation_zero_ae hF,
    hX.jumpProcess_quadraticVariation hF, hIB, hIC] with ω hH heq h0 hj hIBω hICω t
  have hjump (s : Ioc 0 t) : D.left ω s - Function.leftLim (D.left ω) s =
      (jumpProcess X s ω) ^ 2 := by
    have hs : (s : ℝ≥0) ≠ 0 := ne_of_gt s.2.1
    have h := hj s
    change hX.quadraticVariation hF s ω - leftLimitProcess (hX.quadraticVariation hF) s ω = _ at h
    simp only [leftLimitProcess, if_neg hs, heq] at h
    exact h
  have hinit : D.left ω 0 = (X 0 ω) ^ 2 := (heq 0).symm.trans h0
  rw [hIBω t, hICω t]
  change pathStieltjesIntegral (D.left ω) (hvB ω) (hrB ω) (H · ω) t =
    H 0 ω * (X 0 ω) ^ 2 +
      pathStieltjesIntegral (stieltjesContinuousPart (D.left ω)) (hvC ω) (hrC ω) (H · ω) t + _
  simpa only [hjump, hinit] using
    pathStieltjesIntegral_continuous_jump_decomposition (D.left ω) (hvB ω) (hvC ω)
      (H · ω) t (hH.integrableOn_stieltjes (D.left ω) t)

theorem IsSemimartingale.summable_abs_caglad_weighted_sq_jumps
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |H s ω * (jumpProcess X s ω) ^ 2|) := by
  filter_upwards [hr, hX.summable_sq_jumps hF] with ω hH hs t
  obtain ⟨C, _, hC⟩ := hH.exists_norm_bound_Icc t
  apply ((hs t).mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs, abs_mul,
    abs_of_nonneg (sq_nonneg (jumpProcess X s ω))]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [Real.norm_eq_abs] using hC s ⟨s.2.1.le, s.2.2⟩) (sq_nonneg _)

end ProbabilityTheory

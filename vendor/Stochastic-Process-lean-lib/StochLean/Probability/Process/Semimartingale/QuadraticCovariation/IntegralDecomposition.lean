/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.IntegralDecomposition
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPart
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra

/-! # Continuous and atomic parts of integration against mixed quadratic covariation

Polarization uses the existing square-bracket integral decompositions and
the actual absolutely summable weighted jump series. The initial product
is retained; mixed continuous covariation need not be increasing.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

private theorem integral_polarization {A B C : ℝ≥0 → Ω → ℝ}
    (hA : IsSemimartingale A F P) (hB : IsSemimartingale B F P)
    (hC : IsSemimartingale C F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((((hA.sub hB).sub hC).const_mul (1 / 2)).stochasticIntegral hF ha hr)
      ((1 / 2 : ℝ) • (hA.stochasticIntegral hF ha hr -
        hB.stochasticIntegral hF ha hr - hC.stochasticIntegral hF ha hr)) P := by
  filter_upwards [((hA.sub hB).sub hC).stochasticIntegral_const_mul_integrator
    hF ha hr (1 / 2), (hA.sub hB).stochasticIntegral_sub_integrator hC hF ha hr,
    hA.stochasticIntegral_sub_integrator hB hF ha hr] with ω hc habc hab t
  simp only [hc t, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, habc t, hab t]

theorem IsSemimartingale.summable_abs_caglad_weighted_mixed_jumps
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |H s ω * (jumpProcess X s ω * jumpProcess Y s ω)|) := by
  filter_upwards [hr, hX.quadraticCovariation_continuous_jump_decomposition hY hF]
    with ω hH hs t
  obtain ⟨C, _, hC⟩ := hH.exists_norm_bound_Icc t
  apply (((hs t).1).mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs, abs_mul]
  have hb : |H s ω| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC s ⟨s.2.1.le, s.2.2⟩
  exact mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem IsSemimartingale.stochasticIntegral_quadraticCovariation_continuous_jump_decomposition
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr)
      (fun t ω ↦ H 0 ω * (X 0 ω * Y 0 ω) +
        (hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral
          hF ha hr t ω +
        ∑' s : Ioc 0 t, H s ω * (jumpProcess X s ω * jumpProcess Y s ω)) P := by
  have hraw := integral_polarization
    ((hX.add hY).isSemimartingale_quadraticVariation hF)
    (hX.isSemimartingale_quadraticVariation hF)
    (hY.isSemimartingale_quadraticVariation hF) hF ha hr
  have hcont := integral_polarization
    ((hX.add hY).isSemimartingale_continuousQuadraticVariation hF)
    (hX.isSemimartingale_continuousQuadraticVariation hF)
    (hY.isSemimartingale_continuousQuadraticVariation hF) hF ha hr
  filter_upwards [hraw, hcont,
    (hX.add hY).stochasticIntegral_quadraticVariation_continuous_jump_decomposition hF ha hr,
    hX.stochasticIntegral_quadraticVariation_continuous_jump_decomposition hF ha hr,
    hY.stochasticIntegral_quadraticVariation_continuous_jump_decomposition hF ha hr,
    hX.summable_abs_caglad_weighted_sq_jumps hF hr,
    hY.summable_abs_caglad_weighted_sq_jumps hF hr,
    hX.summable_abs_caglad_weighted_mixed_jumps hY hF hr,
    hX.hasCadlagPaths, hY.hasCadlagPaths] with ω hrawω hcontω hz hx hy hsx hsy hsxy hcx hcy t
  have hsum : (∑' s : Ioc 0 t, H s ω * (jumpProcess (X + Y) s ω) ^ 2) =
      (∑' s : Ioc 0 t, H s ω * (jumpProcess X s ω) ^ 2) +
        2 * (∑' s : Ioc 0 t, H s ω * (jumpProcess X s ω * jumpProcess Y s ω)) +
          (∑' s : Ioc 0 t, H s ω * (jumpProcess Y s ω) ^ 2) := by
    calc
      _ = ∑' s : Ioc 0 t, (H s ω * (jumpProcess X s ω) ^ 2 +
          2 * (H s ω * (jumpProcess X s ω * jumpProcess Y s ω)) +
            H s ω * (jumpProcess Y s ω) ^ 2) := by
        apply tsum_congr
        intro s
        rw [hcx.jumpProcess_add hcy s]
        ring
      _ = _ := by
        rw [((hsx t).of_abs.add ((hsxy t).of_abs.mul_left 2)).tsum_add (hsy t).of_abs,
          (hsx t).of_abs.tsum_add ((hsxy t).of_abs.mul_left 2),
          (hsxy t).of_abs.tsum_mul_left 2]
  change (hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr t ω = _
  have hr' := hrawω t
  have hc' := hcontω t
  change (hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr t ω =
    (1 / 2 : ℝ) *
      (((hX.add hY).isSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr t ω -
      (hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr t ω -
      (hY.isSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr t ω) at hr'
  let hCZ := (hX.add hY).isSemimartingale_continuousQuadraticVariation hF
  change (hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral
    hF ha hr t ω =
    (1 / 2 : ℝ) * (hCZ.stochasticIntegral hF ha hr t ω -
      (hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF ha hr t ω -
      (hY.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF ha hr t ω) at hc'
  rw [hr', hc', hz t, hx t, hy t, hsum]
  simp only [Pi.add_apply]
  ring

end ProbabilityTheory

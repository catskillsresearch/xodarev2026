/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.BoundedDensity
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Martingale
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableL2
public import StochLean.Probability.Martingale.Convergence.InMeasure

/-! # The bounded-integrand step of Protter II.20

Bounded simple approximation, the source second-moment estimate and actual
uniform-integrability limits give the finite-time L2 martingale result. Neither
the integrator nor the integral is centered by discarding its initial value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.eLpNorm_stochasticIntegral_le_of_bounded
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : Martingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) (t : ℝ≥0) (hXt : MemLp (X t) 2 P) :
    eLpNorm (hX.stochasticIntegral hF ha hr t) 2 P ≤ C * eLpNorm (X t) 2 P := by
  obtain ⟨S, hS, hSb, huS⟩ := exists_bounded_simplePredictable_tendstoUCP ha hF hr C hb
  have huJ := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  apply eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall fun n ↦
    (hS n).eLpNorm_elementaryIntegral_min_const_le hM hF
      hX.hasCadlagPaths.hasRightContinuousPaths t hXt C (hSb n)) (huJ.fixedTime t)
  intro n
  exact ((hS n).memLp_elementaryIntegral_min_const hM hF
    hX.hasCadlagPaths.hasRightContinuousPaths t hXt C (hSb n)).aestronglyMeasurable

theorem IsSemimartingale.memLp_stochasticIntegral_of_bounded
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : Martingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) (t : ℝ≥0) (hXt : MemLp (X t) 2 P) :
    MemLp (hX.stochasticIntegral hF ha hr t) 2 P :=
  ⟨((hX.adapted_stochasticIntegral hF ha hr t).mono (F.le t) le_rfl).aestronglyMeasurable,
    (hX.eLpNorm_stochasticIntegral_le_of_bounded hF hM ha hr C hb t hXt).trans_lt
      (ENNReal.mul_lt_top (by simp) hXt.eLpNorm_lt_top)⟩

theorem IsSemimartingale.isSquareIntegrableMartingale_stochasticIntegral_of_bounded
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hM : IsSquareIntegrableMartingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) :
    IsSquareIntegrableMartingale (hX.stochasticIntegral hF ha hr) F P := by
  obtain ⟨S, hS, hSb, huS⟩ := exists_bounded_simplePredictable_tendstoUCP ha hF hr C hb
  have huJ := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  have hJS (n : ℕ) : IsSquareIntegrableMartingale ((hS n).elementaryIntegralProcess X) F P :=
    (hS n).isSquareIntegrableMartingale_elementaryIntegralProcess hM hF
      hX.hasCadlagPaths.hasRightContinuousPaths C (hSb n)
  refine ⟨martingale_of_tendstoInMeasure_uniformIntegrable (fun n ↦ (hJS n).1)
    (hX.adapted_stochasticIntegral hF ha hr).stronglyAdapted ?_ huJ.fixedTime,
    fun t ↦ hX.memLp_stochasticIntegral_of_bounded hF hM.1 ha hr C hb t (hM.2 t)⟩
  intro t
  let D : ℝ≥0 := ⟨(C : ℝ) ^ 2 * ∫ ω, (X t ω) ^ 2 ∂P,
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun ω ↦ sq_nonneg (X t ω)))⟩
  apply uniformIntegrable_of_bounded_integral_sq (fun n ↦ (hJS n).2 t) D
  intro n
  exact (hS n).integral_sq_elementaryIntegral_min_const_le hM.1 hF
    hX.hasCadlagPaths.hasRightContinuousPaths t (hM.2 t) C (hSb n)

end ProbabilityTheory

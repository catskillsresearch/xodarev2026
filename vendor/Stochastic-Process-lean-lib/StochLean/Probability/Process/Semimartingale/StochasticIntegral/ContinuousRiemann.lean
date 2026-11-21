/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.ContinuousLeftSampling
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialIncrement
public import StochLean.Probability.Process.UCP.Algebra

/-! # Increment-only random Riemann approximation for continuous integrands

The random partition mesh need not have a deterministic rate. The terminal
horizons may be random. The limiting process subtracts the original initial
product, because the Riemann sums contain only increments. This is the continuous
integrand case, not yet the full cadlag/caglad theorem of Protter II.21.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F Y) (hc : HasContinuousPaths Y P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess Y X) atTop
      (fun t ω ↦ hX.stochasticIntegral hF ha hc.hasCagladPaths t ω - Y 0 ω * X 0 ω) := by
  have hcoef (n : ℕ) (i : Fin (π n).size) :
      Measurable[((π n).point i.castSucc).measurableSpace]
        (fun ω ↦ Y ((π n).point i.castSucc ω) ω) :=
    ha.measurable_stoppedValue_of_leftContinuous_usual hF hc.hasLeftContinuousPaths
      ((π n).point i.castSucc).isStoppingTime
  let hS n := (π n).isSimplePredictable_leftSample_of_stoppingValues (ha 0) (hcoef n)
  have hu := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hc.hasCagladPaths hS
    (hπ.tendstoUCP_leftSample_of_continuous ha hF hc)
  have heq (n : ℕ) : (hS n).elementaryIntegralProcess X =
      ((π n).leftSampleRep Y (ha 0) (hcoef n)).integralProcess X :=
    (hS n).elementaryIntegralProcess_eq _ ((π n).toProcess_leftSampleRep Y (ha 0) (hcoef n)) X
  have hr := hu.sub (tendstoUCP_const atTop (fun _ ω ↦ Y 0 ω * X 0 ω))
  have hid : (fun n ↦ (hS n).elementaryIntegralProcess X - (fun _ ω ↦ Y 0 ω * X 0 ω)) =
      fun n ↦ (π n).leftRiemannSumProcess Y X := by
    funext n
    rw [heq n, (π n).leftRiemannSumProcess_eq_integralProcess_sub_initial Y X (ha 0) (hcoef n)]
    rfl
  rw [hid] at hr
  exact hr

/-- The same continuous-integrand theorem in Protter's exact left-limit normalization. -/
theorem IsSemimartingale.tendstoUCP_leftRiemannSum_leftLimit_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F Y) (hc : HasContinuousPaths Y P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess Y X) atTop
      (hX.stochasticIntegral hF (ha.leftLimitProcess_of_usual hF hc.hasCadlagPaths)
        hc.hasCadlagPaths.hasCagladPaths_leftLimitProcess) :=
  (hX.tendstoUCP_leftRiemannSum_of_continuous hF ha hc hπ).congr_right
    (hX.stochasticIntegral_leftLimit_of_continuous hF ha hc).symm

end ProbabilityTheory

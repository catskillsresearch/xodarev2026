/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.CrossSums
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessRegularity
public import StochLean.Probability.Process.Path.Multiplication
public import StochLean.Probability.Process.Path.Subtraction

/-! # Adaptedness and cadlag paths of actual raw mixed sums

Every summand uses coordinates stopped at finite stopping endpoints. No moment
assumption, coefficient approximation or semimartingale hypothesis is needed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem adapted_quadraticCovariationSumProcess (π : StoppingTimePartition F)
    (haX : Adapted F X) (haY : Adapted F Y) (hF : F.IsUsual P)
    (hrX : HasRightContinuousPaths X P) (hrY : HasRightContinuousPaths Y P) :
    Adapted F (π.quadraticCovariationSumProcess X Y) := by
  intro t
  have hm {Z : ℝ≥0 → Ω → ℝ} (ha : Adapted F Z) (hr : HasRightContinuousPaths Z P)
      (τ : FiniteStoppingTime F) : Measurable[F t] (fun ω ↦ Z (min (τ ω) t) ω) := by
    have hs := (ha.stronglyAdapted.stoppedProcess_of_usual hF hr τ.isStoppingTime).adapted t
    change Measurable[F t] (stoppedProcess Z τ.withTop t) at hs
    simpa only [τ.stoppedProcess_eq Z, min_comm] using hs
  have hs := Finset.measurable_fun_sum univ (fun i : Fin π.size ↦ fun _ ↦
    ((hm haX hrX (π.point i.succ)).sub (hm haX hrX (π.point i.castSucc))).mul
      ((hm haY hrY (π.point i.succ)).sub (hm haY hrY (π.point i.castSucc))))
  exact (((haX 0).mul (haY 0)).mono (F.mono bot_le) le_rfl).add hs

theorem hasCadlagPaths_quadraticCovariationSumProcess (π : StoppingTimePartition F)
    (hrX : HasCadlagPaths X P) (hrY : HasCadlagPaths Y P) :
    HasCadlagPaths (π.quadraticCovariationSumProcess X Y) P := by
  filter_upwards [hrX, hrY] with ω hx hy
  have hs := IsCadlagPath.finset_sum univ
    (fun i : Fin π.size ↦ fun t : ℝ≥0 ↦
      (X (min t (π.point i.succ ω)) ω - X (min t (π.point i.castSucc ω)) ω) *
        (Y (min t (π.point i.succ ω)) ω - Y (min t (π.point i.castSucc ω)) ω))
    (fun i _ ↦ ((hx.min_const _).sub (hx.min_const _)).mul
      ((hy.min_const _).sub (hy.min_const _)))
  have hc : IsCadlagPath (fun _ : ℝ≥0 ↦ X 0 ω * Y 0 ω) :=
    IsContinuousPath.isCadlagPath continuous_const
  convert hc.add hs using 1
  funext t
  simp only [quadraticCovariationSumProcess, StochLean.covariationSum,
    StochLean.TimePartition.increment, StochLean.TimePartition.left,
    StochLean.TimePartition.right, path, Pi.add_apply, min_comm]
  rfl

end ProbabilityTheory.StoppingTimePartition

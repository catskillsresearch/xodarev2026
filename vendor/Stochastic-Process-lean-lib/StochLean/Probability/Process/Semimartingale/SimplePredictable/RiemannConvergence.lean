/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.RiemannCeiling
public import StochLean.Probability.Process.Partition.LeftSamplingRegularity
public import StochLean.Probability.Process.Path.StoppingConvergence
public import StochLean.Probability.Process.Measurability.RightLimit
public import StochLean.Probability.Process.UCP.UniformConvergence
public import Mathlib.Topology.Algebra.Ring.Real

/-! # The fixed-source-step jump-displacement argument in Protter II.21

Sample the right-limit process of a fixed full source simple integrand. Exact
ceiling-endpoint formulas and right continuity of the integrator give actual
compact-uniform path convergence. Its increment-only limit retains the source
initial correction; it does not assume convergence of the sampled integrands.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {π : ℕ → StoppingTimePartition F}

theorem tendstoUniformlyOn_leftRiemannSum_rightLimitProcess (H : SimplePredictableRep F)
    {ω : Ω} (hπT : Tendsto (fun n ↦ (π n).terminal ω) atTop atTop)
    (hπmesh : Tendsto (fun n ↦ (π n).mesh ω) atTop (𝓝 0))
    (hrX : IsRightContinuousPath (X · ω)) (T : ℝ≥0) :
    TendstoUniformlyOn (fun n t ↦ (π n).leftRiemannSumProcess (rightLimitProcess H.toProcess) X t ω)
      (fun t ↦ H.integralProcess X t ω - H.initial ω * X 0 ω) atTop (Icc 0 T) := by
  classical
  have hm : Tendsto (fun n ↦ ((π n).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hπmesh
  have hstop (a : ℝ≥0) : TendstoUniformlyOn
      (fun n t ↦ X (min ((π n).path ω |>.ceilingPoint a) t) ω)
      (fun t ↦ X (min a t) ω) atTop (Icc 0 T) :=
    (tendstoUniformly_min_of_tendsto_nhdsGE (hrX a)
      (StochLean.TimePartition.ceilingPoint_tendsto_nhdsGE_of_eventually_le
        (fun n ↦ (π n).path ω) a (hπT.eventually (eventually_ge_atTop a)) hm)).tendstoUniformlyOn
  have hcell (i : Fin H.partition.size) : TendstoUniformlyOn
      (fun n t ↦ H.coefficient i ω *
        (X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.succ ω)) t) ω -
          X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.castSucc ω)) t) ω))
      (fun t ↦ H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) :=
    Real.uniformContinuous_const_mul.comp_tendstoUniformlyOn
      ((hstop (H.partition.point i.succ ω)).sub (hstop (H.partition.point i.castSucc ω)))
  have hsum (s : Finset (Fin H.partition.size)) : TendstoUniformlyOn
      (fun n t ↦ ∑ i ∈ s, H.coefficient i ω *
        (X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.succ ω)) t) ω -
          X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.castSucc ω)) t) ω))
      (fun t ↦ ∑ i ∈ s, H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const
          (Icc 0 T)
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hcell i).fun_add ih
  have heq (t : ℝ≥0) : H.integralProcess X t ω - H.initial ω * X 0 ω =
      ∑ i : Fin H.partition.size, H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω) := by
    rw [H.integralProcess_apply]
    ring
  simpa only [H.leftRiemannSum_rightLimitProcess, heq] using hsum Finset.univ

theorem tendstoUCP_leftRiemannSum_rightLimitProcess [IsFiniteMeasure P]
    (H : SimplePredictableRep F) (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (haX : Adapted F X) (hF : F.IsUsual P) (hrX : HasCadlagPaths X P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (rightLimitProcess H.toProcess) X) atTop
      (fun t ω ↦ H.integralProcess X t ω - H.initial ω * X 0 ω) := by
  have hrH : HasCagladPaths H.toProcess P := ae_of_all _ H.isCagladPath
  have haY := H.adapted.rightLimitProcess_of_usual hF hrH
  have hrY := hrH.hasCadlagPaths_rightLimitProcess.hasRightContinuousPaths
  have hcoef (n : ℕ) (i : Fin (π n).size) :
      Measurable[((π n).point i.castSucc).measurableSpace]
        (fun ω ↦ rightLimitProcess H.toProcess ((π n).point i.castSucc ω) ω) :=
    haY.stronglyAdapted.measurable_stoppedValue_of_usual hF hrY
      ((π n).point i.castSucc).isStoppingTime
  apply tendstoUCP_of_ae_compactDeviation_of_aemeasurable
  · intro n T
    apply aemeasurable_compactDeviation
    · intro t
      exact ((π n).adapted_leftRiemannSumProcess (haY 0) (hcoef n) haX hF
        hrX.hasRightContinuousPaths t).mono (F.le t) le_rfl
    · intro t
      exact ((H.adapted_integralProcess haX hF hrX.hasRightContinuousPaths t).sub
        ((H.measurable_initial.mul (haX 0)).mono (F.mono bot_le) le_rfl)).mono (F.le t) le_rfl
    · exact ((π n).hasCadlagPaths_leftRiemannSumProcess (haY 0)
        (hcoef n) hrX).hasRightContinuousPaths
    · have hc : HasCadlagPaths (fun (_ : ℝ≥0) ω ↦ H.initial ω * X 0 ω) P := by
        apply ae_of_all
        intro ω
        exact IsContinuousPath.isCadlagPath
          (continuous_const : Continuous (fun _ : ℝ≥0 ↦ H.initial ω * X 0 ω))
      exact ((H.hasCadlagPaths_integralProcess hrX).sub hc).hasRightContinuousPaths
  · filter_upwards [hπ, hrX] with ω hπω hXω T
    exact tendsto_compactDeviation_iff_tendstoUniformlyOn.mpr
      (H.tendstoUniformlyOn_leftRiemannSum_rightLimitProcess hπω.1 hπω.2 hXω.1 T)

end ProbabilityTheory.SimplePredictableRep

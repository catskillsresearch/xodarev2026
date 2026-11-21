/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessRegularity
public import StochLean.Probability.Process.UCP.UniformConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Ring.Real

/-! # Continuity in the integrator for a fixed elementary integrand

Only finitely many stopped increments are involved. No semimartingale premise
on the integrators, coefficient bound, or coefficient integrability is used.
This does not assert continuity in a varying integrator for general integrands.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem SimplePredictableRep.tendstoUniformlyOn_integralProcess
    (H : SimplePredictableRep F) {T : ℝ≥0} {ω : Ω}
    (hu : TendstoUniformlyOn (fun n t ↦ X n t ω) (fun t ↦ Y t ω) atTop (Icc 0 T)) :
    TendstoUniformlyOn (fun n t ↦ H.integralProcess (X n) t ω)
      (fun t ↦ H.integralProcess Y t ω) atTop (Icc 0 T) := by
  classical
  have hstop (a : ℝ≥0) : TendstoUniformlyOn (fun n t ↦ X n (min a t) ω)
      (fun t ↦ Y (min a t) ω) atTop (Icc 0 T) :=
    (hu.comp (fun t ↦ min a t)).mono (fun t ht ↦ ⟨bot_le, (min_le_right a t).trans ht.2⟩)
  have hcell (i : Fin H.partition.size) : TendstoUniformlyOn
      (fun n t ↦ H.coefficient i ω *
        (X n (min (H.partition.point i.succ ω) t) ω -
          X n (min (H.partition.point i.castSucc ω) t) ω))
      (fun t ↦ H.coefficient i ω *
        (Y (min (H.partition.point i.succ ω) t) ω -
          Y (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) :=
    Real.uniformContinuous_const_mul.comp_tendstoUniformlyOn
      ((hstop (H.partition.point i.succ ω)).sub (hstop (H.partition.point i.castSucc ω)))
  have hsum (s : Finset (Fin H.partition.size)) : TendstoUniformlyOn
      (fun n t ↦ ∑ i ∈ s, H.coefficient i ω *
        (X n (min (H.partition.point i.succ ω) t) ω -
          X n (min (H.partition.point i.castSucc ω) t) ω))
      (fun t ↦ ∑ i ∈ s, H.coefficient i ω *
        (Y (min (H.partition.point i.succ ω) t) ω -
          Y (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const
          (Icc 0 T)
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hcell i).fun_add ih
  have hinit := ((hu.tendsto_at (show (0 : ℝ≥0) ∈ Icc 0 T from ⟨le_rfl, bot_le⟩)).const_mul
    (H.initial ω)).tendstoUniformlyOn_const (s := Icc 0 T)
  simpa only [H.integralProcess_apply] using hinit.fun_add (hsum Finset.univ)

theorem IsSimplePredictable.tendstoUCP_elementaryIntegralProcess_integrator
    [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (hF : F.IsUsual P) (haX : ∀ n, Adapted F (X n)) (haY : Adapted F Y)
    (hrX : ∀ n, HasCadlagPaths (X n) P) (hrY : HasCadlagPaths Y P)
    (hu : TendstoUCP P X atTop Y) :
    TendstoUCP P (fun n ↦ hH.elementaryIntegralProcess (X n)) atTop
      (hH.elementaryIntegralProcess Y) := by
  apply tendstoUCP_of_subseq_ae_compactDeviation_of_aemeasurable
    (fun n T ↦ aemeasurable_compactDeviation
      (fun t ↦ ((hH.adapted_elementaryIntegralProcess (haX n) hF
        (hrX n).hasRightContinuousPaths) t).mono (F.le t) le_rfl)
      (fun t ↦ ((hH.adapted_elementaryIntegralProcess haY hF
        hrY.hasRightContinuousPaths) t).mono (F.le t) le_rfl)
      (hH.hasCadlagPaths_elementaryIntegralProcess (hrX n)).hasRightContinuousPaths
      (hH.hasCadlagPaths_elementaryIntegralProcess hrY).hasRightContinuousPaths T)
  intro ns hns
  obtain ⟨k, _, hk⟩ := (hu.comp hns).exists_seq_ae_locallyUniform
  refine ⟨k, hk.mono fun ω hω T ↦ ?_⟩
  apply tendsto_compactDeviation_iff_tendstoUniformlyOn.mpr
  exact hH.choose.tendstoUniformlyOn_integralProcess
    (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hω T))

end ProbabilityTheory

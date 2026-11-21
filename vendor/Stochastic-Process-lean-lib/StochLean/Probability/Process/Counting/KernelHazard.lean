/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardUnrestrictedBalance
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # The existing cumulative hazard with a kernel-valued lifetime law

The original `eCumulativeHazard` is jointly measurable in a measurable
kernel parameter and finite observation time. Its pre-jump denominator is
the actual kernel mass of the closed upper ray, including endpoint atoms.
The proof uses measurable kernel sections and a genuine parameterized
extended integral, without introducing another hazard owner.

For a finite history measure and a Markov lifetime kernel, Tonelli and the
already proved single-law balance give the actual stopped-hazard expectation
under the native composition-product measure. Initial atoms are excluded by
the positive-time integration interval, and infinite lifetimes remain in the
joint law. All values and integrals remain in ENNReal; no real conversion or
joint almost-sure all-time path regularity is asserted here.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {H : Type*} {mH : MeasurableSpace H}

/-- The existing extended cumulative hazard is jointly measurable in its
kernel parameter and finite observation time. -/
theorem measurable_eCumulativeHazard_kernel
    (κ : Kernel H (WithTop ℝ≥0)) [IsSFiniteKernel κ] :
    Measurable (fun p : H × ℝ≥0 ↦ eCumulativeHazard (κ p.1) p.2) := by
  have htail : Measurable (fun p : H × WithTop ℝ≥0 ↦ κ p.1 (Ici p.2)) := by
    have hs : MeasurableSet
        {q : (H × WithTop ℝ≥0) × WithTop ℝ≥0 | q.1.2 ≤ q.2} :=
      measurableSet_le measurable_fst.snd measurable_snd
    exact Kernel.measurable_kernel_prodMk_left
      (κ := κ.comap (Prod.fst : H × WithTop ℝ≥0 → H) measurable_fst) hs
  have hs : MeasurableSet
      {q : (H × ℝ≥0) × WithTop ℝ≥0 | 0 < q.2 ∧ q.2 ≤ (q.1.2 : WithTop ℝ≥0)} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (WithTop.continuous_coe.measurable.comp measurable_fst.snd))
  have hf : Measurable (fun q : (H × ℝ≥0) × WithTop ℝ≥0 ↦
      if 0 < q.2 ∧ q.2 ≤ (q.1.2 : WithTop ℝ≥0)
        then (κ q.1.1 (Ici q.2))⁻¹ else 0) :=
    Measurable.ite hs (htail.comp (measurable_fst.fst.prodMk measurable_snd)).inv
      measurable_const
  have hm : Measurable (fun p : H × ℝ≥0 ↦
      ∫⁻ u, if 0 < u ∧ u ≤ (p.2 : WithTop ℝ≥0)
        then (κ p.1 (Ici u))⁻¹ else 0 ∂κ p.1) :=
    hf.lintegral_kernel_prod_right'
      (κ := κ.comap (Prod.fst : H × ℝ≥0 → H) measurable_fst)
  convert hm using 1
  funext p
  rw [eCumulativeHazard, ← lintegral_indicator measurableSet_Ioc]
  simp only [indicator_apply, mem_Ioc]

/-- Under the actual history/lifetime composition-product measure, the
extended stopped-hazard mean is the mass of positive arrivals by time `t`.
There is no deterministic positive-survival or finite-lifetime assumption. -/
theorem lintegral_stoppedProcess_eCumulativeHazard_compProd
    (η : Measure H) [IsFiniteMeasure η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsMarkovKernel κ] (t : ℝ≥0) :
    (∫⁻ p : H × WithTop ℝ≥0, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id t p.2 ∂(η ⊗ₘ κ)) =
      (η ⊗ₘ κ) {p : H × WithTop ℝ≥0 | 0 < p.2 ∧ p.2 ≤ (t : WithTop ℝ≥0)} := by
  have hm : Measurable (fun p : H × WithTop ℝ≥0 ↦ stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id t p.2) :=
    (measurable_eCumulativeHazard_kernel κ).comp
      (measurable_fst.prodMk (measurable_const.min measurable_snd).untopA)
  have hs : MeasurableSet
      {p : H × WithTop ℝ≥0 | 0 < p.2 ∧ p.2 ≤ (t : WithTop ℝ≥0)} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  rw [Measure.lintegral_compProd hm, Measure.compProd_apply hs]
  apply lintegral_congr
  intro h
  exact lintegral_stoppedProcess_eCumulativeHazard_unrestricted (κ h) t

end ProbabilityTheory

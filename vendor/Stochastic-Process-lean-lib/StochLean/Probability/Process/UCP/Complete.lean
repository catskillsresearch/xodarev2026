/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Cauchy
public import StochLean.Probability.Process.UCP.UniformConvergence
public import StochLean.Probability.Process.Path.UniformLimit
public import StochLean.Probability.Process.Filtration.Usual
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Sequential UCP completeness for adapted cadlag processes

A summable-probability subsequence is uniformly Cauchy on every compact interval
on one full-measure event. The pointwise limits exist by real completeness and
are locally uniform. An initial-measurable null-set reset makes every path cadlag
and preserves adaptedness. The UCP-Cauchy estimate recovers the whole sequence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℕ → ℝ≥0 → Ω → ℝ}

theorem CauchyUCP.exists_adapted_cadlag_limit [IsFiniteMeasure P]
    (hc : CauchyUCP P X) (ha : ∀ n, Adapted F (X n)) (hF : F.IsUsual P)
    (hr : ∀ n, HasCadlagPaths (X n) P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Adapted F Y ∧
      (∀ ω, IsCadlagPath (Y · ω)) ∧ TendstoUCP P X atTop Y := by
  classical
  obtain ⟨k, hk, hkc⟩ := hc.exists_seq_ae_locallyUniform_cauchy
  let good : Set Ω := {ω | (∀ n, IsCadlagPath (X (k n) · ω)) ∧
    ∀ T : ℝ≥0, UniformCauchySeqOn (fun n t ↦ X (k n) t ω) atTop (Icc 0 T)}
  have hg : ∀ᵐ ω ∂P, ω ∈ good := by
    filter_upwards [ae_all_iff.mpr (fun n ↦ hr (k n)), hkc] with ω hω hcω
    exact ⟨hω, hcω⟩
  have hbad : MeasurableSet[F 0] goodᶜ := hF.complete_initial goodᶜ (ae_iff.mp hg)
  have hgood : MeasurableSet[F 0] good := by simpa only [compl_compl] using hbad.compl
  let V : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦ if ω ∈ good then X (k n) t ω else 0
  have hVa : ∀ n, Adapted F (V n) := by
    intro n t
    exact Measurable.ite (F.mono bot_le _ hgood) (ha (k n) t) measurable_const
  have hVr : ∀ n ω, IsCadlagPath (V n · ω) := by
    intro n ω
    by_cases hω : ω ∈ good
    · simpa only [V, if_pos hω] using hω.1 n
    · simpa only [V, if_neg hω] using
        (IsContinuousPath.isCadlagPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  have hVc : ∀ ω T, UniformCauchySeqOn (fun n t ↦ V n t ω) atTop (Icc 0 T) := by
    intro ω T
    by_cases hω : ω ∈ good
    · simpa only [V, if_pos hω] using hω.2 T
    · apply Metric.uniformCauchySeqOn_iff.mpr
      intro ε hε
      exact ⟨0, fun m _ n _ t _ ↦ by simpa only [V, if_neg hω, dist_self] using hε⟩
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun n ↦ V n t ω)
  have hlim : ∀ t ω, Tendsto (fun n ↦ V n t ω) atTop (𝓝 (Y t ω)) := by
    intro t ω
    exact ((hVc ω t).cauchySeq ⟨bot_le, le_rfl⟩).tendsto_limUnder
  have hVu : ∀ ω T, TendstoUniformlyOn (fun n t ↦ V n t ω) (Y · ω) atTop (Icc 0 T) :=
    fun ω T ↦ (hVc ω T).tendstoUniformlyOn_of_tendsto (fun t _ ↦ hlim t ω)
  have hYa : Adapted F Y := by
    intro t
    let : MeasurableSpace Ω := F t
    exact measurable_of_tendsto_metrizable (fun n ↦ hVa n t)
      (tendsto_pi_nhds.mpr (fun ω ↦ hlim t ω))
  have hYr : ∀ ω, IsCadlagPath (Y · ω) := fun ω ↦
    isCadlagPath_of_locallyUniform (fun n ↦ hVr n ω) (hVu ω)
  have hVUCP : TendstoUCP P V atTop Y := by
    apply tendstoUCP_of_ae_compactDeviation
      (fun n T ↦ measurable_compactDeviation
        (fun t ↦ (hVa n t).mono (F.le t) le_rfl)
        (fun t ↦ (hYa t).mono (F.le t) le_rfl)
        (fun ω ↦ (hVr n ω).1) (fun ω ↦ (hYr ω).1) T)
    exact Eventually.of_forall fun ω T ↦
      tendsto_compactDeviation_iff_tendstoUniformlyOn.mpr (hVu ω T)
  have hsub : TendstoUCP P (X ∘ k) atTop Y := by
    intro T ε hε
    have heq : (fun n ↦ P {ω | ε ≤ compactDeviation ((X ∘ k) n) Y T ω}) =
        fun n ↦ P {ω | ε ≤ compactDeviation (V n) Y T ω} := by
      funext n
      apply measure_congr
      filter_upwards [hg] with ω hω
      change (ε ≤ compactDeviation ((X ∘ k) n) Y T ω) =
        (ε ≤ compactDeviation (V n) Y T ω)
      simp only [compactDeviation, Function.comp_apply, V, if_pos hω]
    rw [heq]
    exact hVUCP T ε hε
  exact ⟨Y, hYa, hYr, hc.tendstoUCP_of_subseq hk.tendsto_atTop hsub⟩

end ProbabilityTheory

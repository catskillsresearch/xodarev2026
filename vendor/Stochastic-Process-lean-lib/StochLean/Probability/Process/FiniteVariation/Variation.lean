/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Stieltjes
public import StochLean.Analysis.PathVariation.TotalVariation
public import StochLean.Analysis.PathVariation.UniformPartition
public import StochLean.Probability.Process.Path.FiniteVariation
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # The adapted total-variation process

Variation is first kept in ENNReal, including infinite values. Right continuity,
not continuity, makes actual finite-partition sums converge to it. Real-valued
variation is the canonical Mathlib conversion; its finite-variation interpretation
requires the common-event locally BV hypothesis.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def eTotalVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  eVariationOn (fun s ↦ X s ω) (Icc 0 t)

noncomputable def totalVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathTotalVariation (fun s ↦ X s ω) t

theorem totalVariationProcess_eq_toReal (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    totalVariationProcess X t ω = (eTotalVariationProcess X t ω).toReal :=
  pathTotalVariation_eq _ t

@[simp] theorem totalVariationProcess_zero (X : ℝ≥0 → Ω → ℝ) : totalVariationProcess X 0 = 0 := by
  funext ω
  exact pathTotalVariation_zero _

theorem Indistinguishable.eTotalVariationProcess {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) :
    Indistinguishable (eTotalVariationProcess X) (eTotalVariationProcess Y) P := by
  filter_upwards [h] with ω hω t
  simp only [ProbabilityTheory.eTotalVariationProcess, hω]

theorem Indistinguishable.totalVariationProcess {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) :
    Indistinguishable (totalVariationProcess X) (totalVariationProcess Y) P := by
  filter_upwards [h.eTotalVariationProcess] with ω hω t
  simp only [totalVariationProcess_eq_toReal, hω]

theorem HasFiniteVariationPaths.hasMonotonePaths_totalVariationProcess
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hv : HasFiniteVariationPaths X P) :
    HasMonotonePaths (totalVariationProcess X) P :=
  hv.mono fun _ hω ↦ pathTotalVariation_monotone hω

theorem HasFiniteVariationPaths.hasCadlagPaths_totalVariationProcess
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hv : HasFiniteVariationPaths X P)
    (hr : HasRightContinuousPaths X P) : HasCadlagPaths (totalVariationProcess X) P := by
  filter_upwards [hv, hr] with ω hvω hrω
  have hm := pathTotalVariation_monotone hvω
  exact ⟨rightContinuous_pathTotalVariation hvω hrω,
    fun t _ ↦ ⟨Function.leftLim (pathTotalVariation (fun s ↦ X s ω)) t, hm.tendsto_leftLim t⟩⟩

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem Adapted.eTotalVariationProcess_of_rightContinuous (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.eTotalVariationProcess X) := by
  intro T
  let π : ℕ → TimePartition T := fun n ↦ (LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T))
  let : MeasurableSpace Ω := F T
  change Measurable (fun ω ↦ ProbabilityTheory.eTotalVariationProcess X T ω)
  apply measurable_of_tendsto_metrizable
    (f := fun n ω ↦ ENNReal.ofReal (pVariationSum 1 (π n) (fun t ↦ X t ω)))
  · intro n
    apply ENNReal.measurable_ofReal.comp
    simp only [pVariationSum_one]
    apply Finset.measurable_fun_sum
    intro i _
    have hd : Measurable (fun ω ↦ X ((π n).right i) ω - X ((π n).left i) ω) :=
      ((ha _).mono (F.mono ((π n).point_le_horizon i.succ)) le_rfl).sub
        ((ha _).mono (F.mono ((π n).point_le_horizon i.castSucc)) le_rfl)
    simpa only [Real.norm_eq_abs, TimePartition.increment] using hd.norm
  · apply tendsto_pi_nhds.mpr
    intro ω
    exact tendsto_oneVariationSum_of_rightContinuous (hr ω) hm

theorem Adapted.totalVariationProcess_of_rightContinuous (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.totalVariationProcess X) := by
  intro t
  have h := (ha.eTotalVariationProcess_of_rightContinuous hr t).ennreal_toReal
  have heq : ProbabilityTheory.totalVariationProcess X t =
      fun ω ↦ (ProbabilityTheory.eTotalVariationProcess X t ω).toReal :=
    funext (totalVariationProcess_eq_toReal X t)
  rw [heq]
  exact h

theorem Adapted.eTotalVariationProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.eTotalVariationProcess X) := by
  have hs : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  obtain ⟨Y, hXY, hYp, hYc⟩ := hs.exists_cadlag_indistinguishable_of_usual hF hc
  have hYa : Adapted F Y := fun t ↦ (hYp.stronglyAdapted t).measurable
  have hv := hYa.eTotalVariationProcess_of_rightContinuous (fun ω ↦ (hYc ω).1)
  intro t
  have hcomplete : IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hcomplete.measurable_congr_ae (hv t)
    (hXY.eTotalVariationProcess.symm.mono (fun _ hω ↦ hω t))

theorem Adapted.totalVariationProcess_of_usual (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.totalVariationProcess X) := by
  intro t
  have h := (ha.eTotalVariationProcess_of_usual hF hc t).ennreal_toReal
  have heq : ProbabilityTheory.totalVariationProcess X t =
      fun ω ↦ (ProbabilityTheory.eTotalVariationProcess X t ω).toReal :=
    funext (totalVariationProcess_eq_toReal X t)
  rw [heq]
  exact h

end MeasureTheory

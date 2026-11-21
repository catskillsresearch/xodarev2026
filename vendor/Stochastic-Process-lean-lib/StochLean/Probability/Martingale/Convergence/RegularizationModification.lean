/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.DyadicRightLimitL1
public import StochLean.Probability.Process.Measurability.DyadicRightLimit
public import StochLean.ForMathlib.MeasureTheory.ConditionalOrder

/-! # The modification identity for dyadic regularization

The actual extension is adapted under usual conditions. Conditional order
passes through L1 right-side sampling, placing the extension below the original
supermartingale (above for submartingales). Right-continuous expectations make
their means equal, which proves coordinatewise almost-sure equality.
-/

@[expose] public section

open StochLean ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.stronglyAdapted_dyadicRightLimitProcess
    (hX : Supermartingale X F P) (hF : F.IsUsual P) :
    StronglyAdapted F (dyadicRightLimitProcess X) := by
  have ha := hX.stronglyAdapted.adapted.dyadicRightLimitProcess_of_usual hF
    (hX.ae_exists_dyadic_one_sided_limits.mono fun _ hω t ↦ (hω t).1)
  exact fun t ↦ (ha t).stronglyMeasurable

theorem Submartingale.stronglyAdapted_dyadicRightLimitProcess
    (hX : Submartingale X F P) (hF : F.IsUsual P) :
    StronglyAdapted F (dyadicRightLimitProcess X) := by
  have ha := hX.stronglyAdapted.adapted.dyadicRightLimitProcess_of_usual hF
    (hX.ae_exists_dyadic_one_sided_limits.mono fun _ hω t ↦ (hω t).1)
  exact fun t ↦ (ha t).stronglyMeasurable

theorem Supermartingale.dyadicRightLimitProcess_ae_le
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (t : ℝ≥0) :
    dyadicRightLimitProcess X t ≤ᵐ[P] X t := by
  have hi := hX.integrable_dyadicRightLimitProcess t
  obtain ⟨e, he, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have ht : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  have hL1 := hX.tendsto_eLpNorm_dyadicRightLimitProcess he.antitone ht
  have hc : dyadicRightLimitProcess X t ≤ᵐ[P] P[X t | F t] := by
    apply ae_le_condExp_of_forall_setIntegral_le (F.le t) hi (hX.integrable t)
      (hX.stronglyAdapted_dyadicRightLimitProcess hF t)
    intro A hA
    apply le_of_tendsto' (tendsto_setIntegral_of_L1' _ hi.aestronglyMeasurable
      (Eventually.of_forall fun n ↦ hX.integrable (e n)) hL1 A)
    intro n
    exact hX.setIntegral_le (hm n).1.le hA
  rwa [condExp_of_stronglyMeasurable (F.le t) (hX.stronglyAdapted t) (hX.integrable t)] at hc

theorem Submartingale.ae_le_dyadicRightLimitProcess
    (hX : Submartingale X F P) (hF : F.IsUsual P) (t : ℝ≥0) :
    X t ≤ᵐ[P] dyadicRightLimitProcess X t := by
  have hi := hX.integrable_dyadicRightLimitProcess t
  obtain ⟨e, he, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have ht : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  have hL1 := hX.tendsto_eLpNorm_dyadicRightLimitProcess he.antitone ht
  have hc : X t ≤ᵐ[P] P[dyadicRightLimitProcess X t | F t] := by
    apply ae_le_condExp_of_forall_setIntegral_le (F.le t) (hX.integrable t) hi
      (hX.stronglyAdapted t)
    intro A hA
    apply ge_of_tendsto' (tendsto_setIntegral_of_L1' _ hi.aestronglyMeasurable
      (Eventually.of_forall fun n ↦ hX.integrable (e n)) hL1 A)
    intro n
    exact hX.setIntegral_le (hm n).1.le hA
  rwa [condExp_of_stronglyMeasurable (F.le t)
    (hX.stronglyAdapted_dyadicRightLimitProcess hF t) hi] at hc

theorem Supermartingale.integral_dyadicRightLimitProcess
    (hX : Supermartingale X F P)
    (hmean : IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P)) (t : ℝ≥0) :
    (∫ ω, dyadicRightLimitProcess X t ω ∂P) = ∫ ω, X t ω ∂P := by
  obtain ⟨e, he, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have ht : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  have hI := tendsto_integral_of_L1' _
    (hX.integrable_dyadicRightLimitProcess t).aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hX.integrable (e n))
    (hX.tendsto_eLpNorm_dyadicRightLimitProcess he.antitone ht)
  have hE := (hmean t).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hl, Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (hm n).1.le⟩)
  exact tendsto_nhds_unique hI hE

theorem Submartingale.integral_dyadicRightLimitProcess
    (hX : Submartingale X F P)
    (hmean : IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P)) (t : ℝ≥0) :
    (∫ ω, dyadicRightLimitProcess X t ω ∂P) = ∫ ω, X t ω ∂P := by
  obtain ⟨e, he, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have ht : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  have hI := tendsto_integral_of_L1' _
    (hX.integrable_dyadicRightLimitProcess t).aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hX.integrable (e n))
    (hX.tendsto_eLpNorm_dyadicRightLimitProcess he.antitone ht)
  have hE := (hmean t).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hl, Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (hm n).1.le⟩)
  exact tendsto_nhds_unique hI hE

theorem Supermartingale.isModification_dyadicRightLimitProcess
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hmean : IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P)) :
    IsModification X (dyadicRightLimitProcess X) P := by
  intro t
  exact ((integral_eq_iff_of_ae_le (hX.integrable_dyadicRightLimitProcess t)
    (hX.integrable t) (hX.dyadicRightLimitProcess_ae_le hF t)).mp
    (hX.integral_dyadicRightLimitProcess hmean t)).symm

theorem Submartingale.isModification_dyadicRightLimitProcess
    (hX : Submartingale X F P) (hF : F.IsUsual P)
    (hmean : IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P)) :
    IsModification X (dyadicRightLimitProcess X) P := by
  intro t
  exact (integral_eq_iff_of_ae_le (hX.integrable t)
    (hX.integrable_dyadicRightLimitProcess t) (hX.ae_le_dyadicRightLimitProcess hF t)).mp
    (hX.integral_dyadicRightLimitProcess hmean t).symm

end MeasureTheory

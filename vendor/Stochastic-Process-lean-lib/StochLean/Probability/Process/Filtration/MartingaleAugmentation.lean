/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.ConditionalExpectationAugmentation
public import StochLean.Probability.Process.LocalMartingale
public import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

/-! # A martingale in the genuine usual augmentation

When the raw filtration is right-continuous, its actual conditional
expectations are unchanged by usual augmentation. The original martingale
therefore remains a martingale on the genuinely completed probability space.
Uniform integrability is transported by actual completed-event representatives
and the original Lp norm. Native local martingales retain their actual masked
fundamental sequence. No initial-value normalization is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

private theorem completion_space_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} :
    mΩ ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
  fun _ hs ↦ hs.nullMeasurableSet

private theorem completion_trim_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} : P.completion.trim (completion_space_le (P := P)) = P := by
  apply @Measure.ext Ω mΩ
  intro s hs
  exact (trim_measurableSet_eq (μ := P.completion)
    (completion_space_le (P := P)) hs).trans rfl

private theorem aestronglyMeasurable_completion {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E]
    {Y : Ω → E} (hY : AEStronglyMeasurable Y P) :
    AEStronglyMeasurable (fun ω : NullMeasurableSpace Ω P ↦ Y ω) P.completion := by
  apply aestronglyMeasurable_of_aestronglyMeasurable_trim (completion_space_le (P := P))
  exact (congrArg (fun μ : @Measure Ω mΩ ↦ AEStronglyMeasurable Y μ)
    (completion_trim_eq (P := P))).mpr hY

private theorem eLpNorm_completion {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E]
    {Y : Ω → E} (hY : AEStronglyMeasurable Y P) (p : ℝ≥0∞) :
    eLpNorm (fun ω : NullMeasurableSpace Ω P ↦ Y ω) p P.completion =
      eLpNorm Y p P := by
  have hY' : AEStronglyMeasurable Y
      (P.completion.trim (completion_space_le (P := P))) :=
    (congrArg (fun μ : @Measure Ω mΩ ↦ AEStronglyMeasurable Y μ)
      (completion_trim_eq (P := P))).mpr hY
  exact (eLpNorm_trim_ae (completion_space_le (P := P)) hY').symm.trans
    (congrArg (fun μ : @Measure Ω mΩ ↦ eLpNorm Y p μ) (completion_trim_eq (P := P)))

/-- Uniform integrability survives genuine measure completion, for every
exponent and without a finite-measure assumption. -/
theorem UniformIntegrable.completion {Ω E ι : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E]
    {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UniformIntegrable X p P) :
    UniformIntegrable (fun i (ω : NullMeasurableSpace Ω P) ↦ X i ω) p P.completion := by
  classical
  let μC : @Measure Ω (eventuallyMeasurableSpace mΩ (ae P)) := P.completion
  change UniformIntegrable X p μC
  refine ⟨fun i ↦ aestronglyMeasurable_completion (hX.1 i), ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hX.2.1 hε
    refine ⟨δ, hδ, fun i s hs hsmall ↦ ?_⟩
    have hs' : @NullMeasurableSet Ω mΩ s P := hs
    obtain ⟨B, _, hB, he⟩ := hs'.exists_measurable_superset_ae_eq
    have he' : B =ᵐ[P.completion] s := he
    have hsmallB : P B ≤ ENNReal.ofReal δ := (measure_congr he).le.trans hsmall
    calc
      eLpNorm (s.indicator (X i)) p P.completion =
          eLpNorm (B.indicator (X i)) p P.completion := by
        apply eLpNorm_congr_ae
        filter_upwards [he'] with ω hω
        change (ω ∈ B) = (ω ∈ s) at hω
        simp only [indicator_apply, hω]
      _ = eLpNorm (B.indicator (X i)) p P :=
        eLpNorm_completion ((hX.1 i).indicator hB) p
      _ ≤ ENNReal.ofReal ε := hd i B hB hsmallB
  · obtain ⟨C, hC⟩ := hX.2.2
    exact ⟨C, fun i ↦ (eLpNorm_completion (hX.1 i) p).le.trans (hC i)⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A real martingale in an already right-continuous raw filtration remains
a native martingale in its genuine usual augmentation. -/
theorem Martingale.usualAugmentation_of_isRightContinuous
    (hX : Martingale X F P) (hF : F.IsRightContinuous) :
    Martingale (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω)
      (F.usualAugmentation P) P.completion := by
  refine ⟨fun t ↦ (hX.stronglyMeasurable t).mono (F.le_usualAugmentation P t), ?_⟩
  intro s t hst
  exact (Filtration.condExp_usualAugmentation_of_isRightContinuous
    hF (hX.integrable t) s).trans
    (hX.condExp_ae_eq hst)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A UI martingale remains UI in the genuine usual augmentation of an
already right-continuous filtration. -/
theorem IsUIMartingale.usualAugmentation_of_isRightContinuous
    (hX : IsUIMartingale X F P) (hF : F.IsRightContinuous) :
    IsUIMartingale (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω)
      (F.usualAugmentation P) P.completion :=
  ⟨hX.1.usualAugmentation_of_isRightContinuous hF, hX.2.completion⟩

/-- The same actual masked fundamental sequence localizes the process in
the genuine usual augmentation; its time-zero mask is unchanged. -/
theorem IsLocalMartingale.usualAugmentation_of_isRightContinuous
    (hX : IsLocalMartingale X F P) (hF : F.IsRightContinuous) :
    IsLocalMartingale (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω)
      (F.usualAugmentation P) P.completion := by
  refine ⟨fun t ↦ (hX.1 t).mono (F.le_usualAugmentation P t) le_rfl, hX.2.1, ?_⟩
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨τ, ⟨fun n t ↦ F.le_usualAugmentation P t _ (hτ.1.isStoppingTime n t),
    hτ.1.tendsto_top⟩, hτ.2.1, fun n ↦ ?_⟩
  exact (hτ.2.2 n).usualAugmentation_of_isRightContinuous hF

end ProbabilityTheory

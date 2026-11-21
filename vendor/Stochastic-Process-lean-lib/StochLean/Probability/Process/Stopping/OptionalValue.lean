/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.Optional
public import StochLean.Probability.Process.Stopping.TerminalMeasurable
public import StochLean.Probability.Process.Stopping.Finite

/-! # Optional stopping and measurable values

Optional processes need not themselves be cadlag. Stopping preserves optionality
by transporting each generator, using cadlag paths only for those generators.
Possibly infinite sampling uses the existing explicitly supplied terminal owner.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

/-- The finite-time stopping map is measurable for the optional sigma-field. -/
theorem IsStoppingTime.measurable_optional_stopping_map (hτ : IsStoppingTime F τ) :
    @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) F.optional F.optional
      (fun p ↦ ((min (p.1 : WithTop ℝ≥0) (τ p.2)).untopA, p.2)) := by
  rw [measurable_iff_comap_le]
  conv_lhs => rw [Filtration.optional]
  simp only [MeasurableSpace.comap_iSup]
  refine iSup_le fun X ↦ iSup_le fun ha ↦ iSup_le fun hc ↦ ?_
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (Function.uncurry (stoppedProcess X τ)) inferInstance ≤ F.optional
  have hsa : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  have hp := (hsa.isStronglyProgressive_of_rightContinuous (fun ω ↦ (hc ω).1)).stoppedProcess hτ
  have hpath : ∀ ω, IsCadlagPath (fun t ↦ stoppedProcess X τ t ω) := by
    intro ω
    cases ht : τ ω with
    | top =>
      simpa only [stoppedProcess, ht, min_eq_left le_top, WithTop.untopA,
        WithTop.untopD_coe] using hc ω
    | coe T =>
      simpa only [stoppedProcess, ht, ← WithTop.coe_min, WithTop.untopA,
        WithTop.untopD_coe] using (hc ω).min_const T
  exact (hp.isProgressive.adapted.measurable_optional_of_cadlag hpath).comap_le

theorem IsStronglyOptional.stoppedProcess {E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} (hX : IsStronglyOptional F X) (hτ : IsStoppingTime F τ) :
    IsStronglyOptional F (stoppedProcess X τ) :=
  hX.comp_measurable hτ.measurable_optional_stopping_map

theorem IsStronglyOptional.stronglyMeasurable_finiteStoppingTime
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyOptional F X) (τ : FiniteStoppingTime F) :
    StronglyMeasurable[τ.measurableSpace] (fun ω ↦ X (τ ω) ω) :=
  (measurable_stoppedValue hX.isStronglyProgressive τ.isStoppingTime).stronglyMeasurable

theorem IsStronglyOptional.stronglyMeasurable_stoppedValueWithTerminal
    {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} (hX : IsStronglyOptional F X)
    (hZ : StronglyMeasurable[⨆ t, F t] Z) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValueWithTerminal X Z τ) :=
  hX.isStronglyProgressive.stronglyMeasurable_stoppedValueWithTerminal hZ hτ

end MeasureTheory

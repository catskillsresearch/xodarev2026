/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Approximation
public import StochLean.Probability.Process.Path.RightContinuous

/-! # Measurability of sampling a right-continuous process at a finite stopping time

Countable-range finite stopping times permit direct measurable pasting of
coordinate evaluations. An arbitrary genuinely finite stopping time is
approximated from above by the existing dyadic stopping grids. Common-event
right continuity and native AE measurability of metric limits then give the
actual sampled value's AE measurability.

The process need not be adapted or jointly measurable, and the filtration
need not be usual. No value at infinity, replacement process, or new stopping
time selector is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Sampling a coordinate-measurable process at a countable-range genuinely
finite stopping time is measurable on the original sample space. -/
theorem measurable_sample_of_countable_range (τ : FiniteStoppingTime F)
    (hcount : (range τ).Countable) (hm : ∀ t, Measurable (X t)) :
    Measurable (fun ω ↦ X (τ ω) ω) := by
  let R := range τ
  let : Countable R := hcount.to_subtype
  have hmτ : Measurable τ :=
    (τ.isStoppingTime.measurable.untopD 0).mono τ.measurableSpace_le le_rfl
  have hmR : Measurable (fun ω ↦ (⟨τ ω, mem_range_self ω⟩ : R)) :=
    hmτ.subtype_mk
  have hmEval : Measurable (fun p : Ω × R ↦ X p.2.val p.1) :=
    measurable_from_prod_countable_left fun r ↦ hm r.val
  exact hmEval.comp (measurable_id.prodMk hmR)

/-- A coordinate-measurable process with common-event right-continuous paths
has an AE-measurable actual value at every genuinely finite stopping time. -/
theorem aemeasurable_sample_of_rightContinuous (τ : FiniteStoppingTime F)
    (hm : ∀ t, Measurable (X t)) (hr : HasRightContinuousPaths X P) :
    AEMeasurable (fun ω ↦ X (τ ω) ω) P := by
  let σ (n : ℕ) : FiniteStoppingTime F :=
    ⟨fun ω ↦ dyadicRightGrid n (τ ω), stoppingTime_dyadicRightGridFinite τ.isStoppingTime n⟩
  have hcount (n : ℕ) : (range (σ n)).Countable := by
    apply (countable_range_dyadicRightGrid n).mono
    rintro y ⟨ω, rfl⟩
    exact ⟨τ ω, rfl⟩
  have hmσ (n : ℕ) : Measurable (fun ω ↦ X (σ n ω) ω) :=
    (σ n).measurable_sample_of_countable_range (hcount n) hm
  apply aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hmσ n).aemeasurable)
  filter_upwards [hr] with ω hω
  exact (hω (τ ω)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_dyadicRightGrid (τ ω),
      Eventually.of_forall fun n ↦ le_dyadicRightGrid n (τ ω)⟩)

end ProbabilityTheory.FiniteStoppingTime

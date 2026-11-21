/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AfterCoefficient
public import StochLean.Probability.Process.Path.LifetimeStepJump
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps
public import StochLean.Probability.Process.ClassD.Basic
public import Mathlib.Probability.Martingale.Basic

/-! # Integrable single jumps for continuous Doob decomposition

The coefficient is revealed at its native stopped sigma-field. Its closed
lifetime indicator is the existing step process, not a new process owner.
Integrable coefficients give Class D without bounded lifetimes or amplitudes.
A nonpositive coefficient gives an actual supermartingale. A totally
inaccessible lifetime gives totally inaccessible positive-time jumps.
An infinite lifetime never activates at finite time; the initial jump is
retained when the lifetime is zero, and is almost surely zero for a totally
inaccessible lifetime.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}

namespace ProbabilityTheory

/-- No sign, finiteness of the lifetime, or finite measure assumption is needed. -/
theorem isClassD_indicator_stoppingTime_le (hτ : IsStoppingTime F τ)
    (hm : StronglyMeasurable[hτ.measurableSpace] Z) (hi : Integrable Z P) :
    IsClassD (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P := by
  have ho := hm.isStronglyOptional_indicator_stoppingTime_le hτ
  apply (isClassD_const (F := F) hi).mono_norm
  · intro σ
    exact ((ho.stronglyMeasurable_finiteStoppingTime σ).mono
      σ.measurableSpace_le).aestronglyMeasurable
  · intro σ
    exact Eventually.of_forall fun ω ↦ norm_indicator_le_norm_self _ _

/-- A negative lifetime coefficient produces a pathwise nonincreasing process. -/
theorem antitone_indicator_lifetime_le (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    {ω : Ω} (hZ : Z ω ≤ 0) :
    Antitone (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) := by
  classical
  intro s t hst
  by_cases hs : τ ω ≤ (s : WithTop ℝ≥0)
  · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
    simp only [indicator_apply, mem_ofPred_eq, if_pos hs, if_pos ht, le_refl]
  · by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
    · simpa only [indicator_apply, mem_ofPred_eq, if_neg hs, if_pos ht] using hZ
    · simp only [indicator_apply, mem_ofPred_eq, if_neg hs, if_neg ht, le_refl]

/-- The original lifetime itself is a countable covering of the step's jumps. -/
theorem IsTotallyInaccessibleStoppingTime.hasTotallyInaccessibleJumps_indicator
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (Z : Ω → ℝ) :
    HasTotallyInaccessibleJumps F
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) P := by
  classical
  refine ⟨fun _ ↦ τ, fun _ ↦ hτ, Eventually.of_forall fun ω t _ hj ↦ ?_⟩
  refine ⟨0, ?_⟩
  by_contra hne
  apply hj
  rw [jumpProcess_indicator_lifetime_le]
  exact indicator_of_notMem (show ω ∉ {v | τ v = (t : WithTop ℝ≥0)} from hne) _

/-- Total inaccessibility excludes activation at zero almost surely. -/
theorem IsTotallyInaccessibleStoppingTime.indicator_initial_ae_eq_zero
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (Z : Ω → ℝ) :
    {ω | τ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator Z =ᵐ[P] 0 := by
  classical
  have hn : ∀ᵐ ω ∂P, ¬ (τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) ∧ τ ω ≠ ⊤) := by
    rw [ae_iff]
    simpa only [not_not] using
      hτ.2 (fun _ ↦ ((0 : ℝ≥0) : WithTop ℝ≥0)) (isPredictableStoppingTime_const F P 0)
  filter_upwards [hn] with ω hω
  apply indicator_of_notMem
  intro ht
  have he : τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := le_antisymm ht bot_le
  exact hω ⟨he, he ▸ WithTop.coe_ne_top⟩

end ProbabilityTheory

namespace MeasureTheory

/-- This proves the conditional inequality from integrability and the actual
pathwise decrease; no supermartingale or compensator certificate is supplied. -/
theorem supermartingale_indicator_stoppingTime_le [IsFiniteMeasure P]
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) (hn : ∀ᵐ ω ∂P, Z ω ≤ 0) :
    Supermartingale
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P := by
  have hD := isClassD_indicator_stoppingTime_le hτ hm hi
  refine ⟨fun t ↦ hm.indicator_stoppingTime_le hτ t, ?_, hD.integrable⟩
  intro s t hst
  have hle : {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ≤ᵐ[P]
      {ω | τ ω ≤ (s : WithTop ℝ≥0)}.indicator Z :=
    hn.mono fun _ hω ↦ antitone_indicator_lifetime_le τ Z hω hst
  have hce := condExp_mono (hD.integrable t) (hD.integrable s) hle (m := F s)
  rwa [condExp_of_stronglyMeasurable (F.le s)
    (hm.indicator_stoppingTime_le hτ s) (hD.integrable s)] at hce

end MeasureTheory

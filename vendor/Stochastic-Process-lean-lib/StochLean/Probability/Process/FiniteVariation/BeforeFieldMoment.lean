/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.Stopping.BeforeSigmaOrder

/-! # Locally integrable variation at a time with trivial preceding information

When all events strictly before a positive deterministic time have probability
zero or one, one actual native localizer covers that time almost surely.
Its positive-lifetime mask is then one, and its integrable total variation
dominates the original increment from zero to that time.

Only measurability of this increment is required. Neither the initial value
nor the individual coordinates are assumed integrable, and no adaptedness,
usual conditions, or path regularity is imposed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private theorem exists_ae_le_localizer_of_before_zero_one
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsPreLocalizingSequence F τ P)
    (hzeroOne : ∀ s : Set Ω,
      MeasurableSet[(isStoppingTime_const F T).measurableSpaceBefore] s →
        P s = 0 ∨ P s = 1) :
    ∃ n, ∀ᵐ ω ∂P, (T : WithTop ℝ≥0) ≤ τ n ω := by
  classical
  let E : ℕ → Set Ω := fun n ↦ {ω | (T : WithTop ℝ≥0) ≤ τ n ω}
  have hmE (n : ℕ) :
      MeasurableSet[(isStoppingTime_const F T).measurableSpaceBefore] (E n) := by
    simpa only [E, compl_ofPred, not_lt] using
      ((hτ.isStoppingTime n).measurableSet_lt_before (isStoppingTime_const F T)).compl
  have hex : ∃ n, P (E n) = 1 := by
    by_contra h
    have hz (n : ℕ) : P (E n) = 0 :=
      (hzeroOne (E n) (hmE n)).resolve_right (fun hn ↦ h ⟨n, hn⟩)
    have hnone : ∀ᵐ ω ∂P, ∀ n, ω ∉ E n := by
      refine ae_all_iff.mpr fun n ↦ ?_
      rw [ae_iff]
      simpa only [E, mem_ofPred_eq, not_not] using hz n
    obtain ⟨ω, hω, hlim⟩ := (hnone.and hτ.tendsto_top).exists
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))).exists
    exact hω n hn.le
  obtain ⟨n, hn⟩ := hex
  have hm : MeasurableSet (E n) :=
    (isStoppingTime_const F T).measurableSpaceBefore_le_ambient _ (hmE n)
  exact ⟨n, (mem_ae_iff_prob_eq_one hm).mpr hn⟩

namespace HasLocallyIntegrableVariation

/-- A native locally integrable-variation process has an integrable actual
increment at a positive time with probability-trivial preceding information.
An arbitrary nonintegrable initial random value is not ruled out. -/
theorem integrable_sub_at_of_before_zero_one
    (hLV : HasLocallyIntegrableVariation X F P) (hT : 0 < T)
    (hzeroOne : ∀ s : Set Ω,
      MeasurableSet[(isStoppingTime_const F T).measurableSpaceBefore] s →
        P s = 0 ∨ P s = 1)
    (hm : AEStronglyMeasurable (fun ω ↦ X T ω - X 0 ω) P) :
    Integrable (fun ω ↦ X T ω - X 0 ω) P := by
  obtain ⟨τ, hτ, hIV⟩ := hLV
  obtain ⟨n, hn⟩ := exists_ae_le_localizer_of_before_zero_one
    hτ.toIsPreLocalizingSequence hzeroOne
  apply (hIV n).2.mono' hm
  filter_upwards [hn, (hIV n).ae_forall_norm_sub_le] with ω hω hb
  have hpos : ω ∈ {ω | ⊥ < τ n ω} :=
    (WithTop.coe_lt_coe.mpr hT).trans_le hω
  have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω := bot_le
  simpa only [stoppedProcess_eq_of_le hω, stoppedProcess_eq_of_le h0,
    indicator_of_mem hpos] using hb 0 T

end HasLocallyIntegrableVariation

end ProbabilityTheory

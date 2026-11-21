/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.AccessibleSingleJump
public import StochLean.Probability.Martingale.Doob.TotallyInaccessibleSingleJump
public import StochLean.Probability.Process.Stopping.ClassificationDecomposition

/-! # Actual predictable compensation of an arbitrary integrable single jump

The original stopping time is decomposed into its accessible and totally
inaccessible parts. Both components and both compensators are constructed
internally. Their coefficients are restricted to disjoint stopped-measurable
events, so the sum of the first-moment budgets is at most the original budget.

The resulting predictable cadlag process has integrable total variation and
starts at zero almost surely. Subtracting it from the actual closed lifetime
jump gives a true UI martingale. Positive lifetimes may be infinite; no
coefficient is assumed zero at infinity and no process is evaluated there.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {σ : Ω → WithTop ℝ≥0} {D : Ω → ℝ}

private theorem indicator_restricted_lifetime_le (σ : Ω → WithTop ℝ≥0)
    (D : Ω → ℝ) (E : Set Ω) (t : ℝ≥0) :
    {ω | restrictedStoppingTime σ E ω ≤ (t : WithTop ℝ≥0)}.indicator (E.indicator D) =
      E.indicator ({ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D) := by
  classical
  funext ω
  by_cases hω : ω ∈ E <;> simp [indicator_apply, restrictedStoppingTime, hω]

/-- The actual predictable IV compensator of an arbitrary positive integrable
single jump, with the sharp first-moment bound and true UI compensation. -/
theorem IsStoppingTime.exists_predictable_compensator_indicator
    (hσ : IsStoppingTime F σ) (hF : F.IsUsual P) (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    (hm : StronglyMeasurable[hσ.measurableSpace] D) (hi : Integrable D P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 =ᵐ[P] 0 ∧
      HasIntegrableVariation A P ∧
      (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) ≤ ∫ ω, ‖D ω‖ ∂P ∧
      IsUIMartingale
        ((fun t : ℝ≥0 ↦ {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D) - A) F P := by
  classical
  obtain ⟨E, H, hd⟩ := exists_accessibleInaccessible_decomposition hσ P
  let Da := E.indicator D
  let Db := H.indicator D
  have hma : StronglyMeasurable[hd.accessible.1.measurableSpace] Da :=
    (hm.indicator hd.measurable_left).mono
      (hσ.measurableSpace_mono hd.accessible.1 (le_restrictedStoppingTime σ E))
  have hmb : StronglyMeasurable[hd.totallyInaccessible.1.measurableSpace] Db :=
    (hm.indicator hd.measurable_right).mono
      (hσ.measurableSpace_mono hd.totallyInaccessible.1 (le_restrictedStoppingTime σ H))
  have hia : Integrable Da P := hi.indicator (hσ.measurableSpace_le E hd.measurable_left)
  have hib : Integrable Db P := hi.indicator (hσ.measurableSpace_le H hd.measurable_right)
  have hpa : ∀ᵐ ω ∂P, 0 < ProbabilityTheory.restrictedStoppingTime σ E ω :=
    hpos.mono fun ω hω ↦ hω.trans_le (le_restrictedStoppingTime σ E ω)
  obtain ⟨A, hpA, hcA, hA0, hvA, hEA, hMA⟩ :=
    hd.accessible.exists_predictable_compensator_indicator hF hpa hma hia
  obtain ⟨B, haB, hpB, hBc, hB0, hvB, hEB, hMB⟩ :=
    hd.totallyInaccessible.exists_continuous_compensator_indicator hF hmb hib
  have hcB : HasCadlagPaths B P :=
    (show HasContinuousPaths B P from Eventually.of_forall hBc).hasCadlagPaths
  have haA := hpA.stronglyAdapted.adapted
  have hv : HasIntegrableVariation (A + B) P := hvA.add hvB haA haB hF hcA hcB
  have hp : IsStronglyPredictable F (A + B) := StronglyMeasurable.add hpA hpB
  let J : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D
  let Ja : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | ProbabilityTheory.restrictedStoppingTime σ E ω ≤ (t : WithTop ℝ≥0)}.indicator Da
  let Jb : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | ProbabilityTheory.restrictedStoppingTime σ H ω ≤ (t : WithTop ℝ≥0)}.indicator Db
  have hrec : Indistinguishable (Ja + Jb) J P := by
    filter_upwards [hd.union_ae] with ω hω t
    change (ω ∈ E ∨ ω ∈ H) = (σ ω ≠ ⊤) at hω
    change Ja t ω + Jb t ω = J t ω
    rw [show Ja t = E.indicator (J t) from indicator_restricted_lifetime_le σ D E t,
      show Jb t = H.indicator (J t) from indicator_restricted_lifetime_le σ D H t,
      ← congrFun (indicator_union_of_disjoint hd.disjoint (J t)) ω]
    by_cases hf : σ ω = ⊤
    · have hz : J t ω = 0 := by
        simp only [J, indicator_apply, mem_ofPred_eq, hf, WithTop.not_top_le_coe, if_false]
      rw [indicator_apply]
      simp only [hz, ite_self]
    · have hmem : ω ∈ E ∪ H := (Iff.of_eq hω).mpr hf
      exact indicator_of_mem hmem (J t)
  have hbudget : (∫ ω, ‖Da ω‖ ∂P) + (∫ ω, ‖Db ω‖ ∂P) ≤ ∫ ω, ‖D ω‖ ∂P := by
    rw [← integral_add hia.norm hib.norm]
    apply integral_mono (hia.norm.add hib.norm) hi.norm
    intro ω
    change ‖Da ω‖ + ‖Db ω‖ ≤ ‖D ω‖
    by_cases he : ω ∈ E
    · have hh : ω ∉ H := fun hh ↦ disjoint_left.mp hd.disjoint he hh
      simp only [Da, Db, indicator_of_mem he, indicator_of_notMem hh, norm_zero, add_zero,
        le_refl]
    · by_cases hh : ω ∈ H
      · simp only [Da, Db, indicator_of_notMem he, indicator_of_mem hh, norm_zero, zero_add,
          le_refl]
      · simp only [Da, Db, indicator_of_notMem he, indicator_of_notMem hh, norm_zero,
          zero_add, norm_nonneg]
  refine ⟨A + B, hp, hcA.add hcB, ?_, hv, ?_, ?_⟩
  · filter_upwards [hA0] with ω hω
    change A 0 ω + B 0 ω = 0
    simp only [hω, congrFun hB0 ω, Pi.zero_apply, add_zero]
  · have hb : (∫ ω, (eVariationOn ((A + B) · ω) univ).toReal ∂P) ≤
        (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) +
          ∫ ω, (eVariationOn (B · ω) univ).toReal ∂P := by
      rw [← integral_add hvA.2 hvB.2]
      apply integral_mono_ae hv.2 (hvA.2.add hvB.2)
      filter_upwards [hvA.1, hvB.1] with ω hA hB
      simpa only [ENNReal.toReal_add hA hB, Pi.add_apply] using
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
          (eVariationOn_add_le (A · ω) (B · ω) univ)
    exact hb.trans ((add_le_add hEA hEB).trans hbudget)
  · apply (hMA.add hMB).congr
      (fun t ↦ (hm.indicator_stoppingTime_le hσ t).measurable.sub
        (hp.stronglyAdapted t).measurable)
    filter_upwards [hrec] with ω hω t
    change (Ja t ω - A t ω) + (Jb t ω - B t ω) = J t ω - (A t ω + B t ω)
    have he : Ja t ω + Jb t ω = J t ω := hω t
    linarith only [he]

end MeasureTheory

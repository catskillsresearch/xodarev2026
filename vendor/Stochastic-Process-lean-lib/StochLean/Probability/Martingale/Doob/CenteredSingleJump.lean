/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJump
public import StochLean.Probability.Process.Stopping.BeforeSigma
public import StochLean.Probability.Process.LocalMartingale

/-! # Before-centered integrable single jumps are UI martingales

The coefficient is measurable at the stopping time, not necessarily before it.
If its conditional expectation before that time vanishes, its actual closed
lifetime step is a martingale. Integrable domination of all stopping values
gives Class D and hence uniform integrability.

No predictability of the lifetime is needed for this centered martingale
statement. Predictability is needed separately to identify the removed
before-conditional step as a predictable compensating process. Infinite
lifetimes never activate at finite time; coefficients are not assumed zero
there and no finite evaluation of an infinite stopping time is used.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}

/-- Before-centered L1 coefficients give genuine martingales at any stopping
lifetime. The coefficient only needs measurability at that stopping time. -/
theorem martingale_indicator_stoppingTime_le_of_condExp_before_eq_zero
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) (hz : P[Z | hτ.measurableSpaceBefore] =ᵐ[P] 0) :
    Martingale (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P := by
  classical
  let J : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z
  have hD := isClassD_indicator_stoppingTime_le hτ hm hi
  refine ⟨fun t ↦ hm.indicator_stoppingTime_le hτ t, ?_⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hD.integrable t)
    (fun _ _ _ ↦ (hD.integrable s).integrableOn) _
    (hm.indicator_stoppingTime_le hτ s).aestronglyMeasurable
  intro A hA _
  let B : Set Ω := (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}) ∩
    {ω | τ ω ≤ (t : WithTop ℝ≥0)}
  have hBt : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
    simpa only [compl_ofPred, not_lt] using (hτ.measurableSet_gt_before t).compl
  have hB : MeasurableSet[hτ.measurableSpaceBefore] B :=
    (hτ.measurableSet_inter_gt_before s hA).inter hBt
  have hBambient : MeasurableSet B := hτ.measurableSpaceBefore_le_ambient _ hB
  have hzero : (∫ ω in B, Z ω ∂P) = 0 := by
    calc
      _ = ∫ ω in B, P[Z | hτ.measurableSpaceBefore] ω ∂P :=
        (setIntegral_condExp hτ.measurableSpaceBefore_le_ambient hi hB).symm
      _ = ∫ ω in B, (0 : Ω → ℝ) ω ∂P := integral_congr_ae (ae_restrict_of_ae hz)
      _ = 0 := by simp
  have he : A.indicator (J t - J s) = B.indicator Z := by
    funext ω
    simp only [J, B, indicator_apply, Pi.sub_apply, mem_inter_iff, mem_ofPred_eq]
    by_cases hAω : ω ∈ A
    · by_cases hs : τ ω ≤ (s : WithTop ℝ≥0)
      · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
        have hns := not_lt.mpr hs
        simp only [hAω, hs, ht, hns, if_true, if_false, and_false, false_and, sub_self]
      · have hss : (s : WithTop ℝ≥0) < τ ω := lt_of_not_ge hs
        by_cases ht : τ ω ≤ (t : WithTop ℝ≥0) <;>
          simp only [hAω, hs, ht, hss, if_true, if_false, and_self, and_false,
            sub_zero, sub_self]
    · simp only [hAω, false_and, if_false]
  have hd : (∫ ω in A, J t ω ∂P) - (∫ ω in A, J s ω ∂P) = 0 := by
    rw [← integral_sub (hD.integrable t).integrableOn (hD.integrable s).integrableOn]
    change (∫ ω in A, (J t - J s) ω ∂P) = 0
    rw [← integral_indicator (F.le s _ hA), he, integral_indicator hBambient]
    exact hzero
  exact (sub_eq_zero.mp hd).symm

/-- The same actual single jump is UI by its integrable coefficient envelope. -/
theorem isUIMartingale_indicator_stoppingTime_le_of_condExp_before_eq_zero
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) (hz : P[Z | hτ.measurableSpaceBefore] =ᵐ[P] 0) :
    IsUIMartingale (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P :=
  ⟨martingale_indicator_stoppingTime_le_of_condExp_before_eq_zero hτ hm hi hz,
    (isClassD_indicator_stoppingTime_le hτ hm hi).uniformIntegrable⟩

/-- Centering the original stopped-measurable L1 coefficient before its
lifetime constructs a true UI single-jump martingale, including infinite lifetimes. -/
theorem isUIMartingale_indicator_sub_condExp_before
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) :
    IsUIMartingale (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
      (Z - P[Z | hτ.measurableSpaceBefore])) F P := by
  have hK : StronglyMeasurable[hτ.measurableSpace] P[Z | hτ.measurableSpaceBefore] :=
    stronglyMeasurable_condExp.mono hτ.measurableSpaceBefore_le
  apply isUIMartingale_indicator_stoppingTime_le_of_condExp_before_eq_zero
    hτ (hm.sub hK) (hi.sub integrable_condExp)
  have he := condExp_sub (m := hτ.measurableSpaceBefore) hi
    (integrable_condExp (f := Z) (m := hτ.measurableSpaceBefore))
  rw [condExp_of_stronglyMeasurable hτ.measurableSpaceBefore_le_ambient
    stronglyMeasurable_condExp integrable_condExp] at he
  simpa only [sub_self] using he

end MeasureTheory

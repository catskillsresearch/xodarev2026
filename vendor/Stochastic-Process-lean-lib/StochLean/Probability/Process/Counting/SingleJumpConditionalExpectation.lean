/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.SingleJumpInformation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Conditional expectation from a closed single-jump count

For the original natural filtration, an observed jump reveals the entire
lifetime, while survival is one indivisible information event. The actual
conditional expectation therefore uses the full-lifetime conditional
expectation on the occurrence event and the survival average elsewhere.

The candidate's natural-information measurability follows from the native
Doob--Dynkin factorization and the actual restricted lifetime. Its L1
property and all event-integral identities are proved separately. The
positive survival-mass hypothesis is a genuine denominator guard.

This is a raw natural-filtration result, not a claim about its usual
augmentation. Zero, the closed observation endpoint, and an infinite
lifetime all retain their original meaning.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0} {Y : Ω → ℝ}

/-- Actual conditional expectation in the natural filtration of the
closed single-jump count, with a positive survival-probability guard. -/
theorem condExp_natural_singleJumpCount (hτ : Measurable τ) (hY : Integrable Y P)
    (t : ℝ≥0) (hSurvival : 0 < P.real {ω | (t : WithTop ℝ≥0) < τ ω}) :
    P[Y | (Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)) t] =ᵐ[P]
      fun ω ↦ if τ ω ≤ (t : WithTop ℝ≥0) then
        P[Y | MeasurableSpace.comap τ inferInstance] ω
      else (∫ v in {v | (t : WithTop ℝ≥0) < τ v}, Y v ∂P) /
        P.real {v | (t : WithTop ℝ≥0) < τ v} := by
  classical
  let N : ℝ≥0 → Ω → ℕ :=
    fun s ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount hτ)
  let mτ := MeasurableSpace.comap τ inferInstance
  let H := P[Y | mτ]
  let S : Set Ω := {ω | (t : WithTop ℝ≥0) < τ ω}
  let c : ℝ := (∫ ω in S, Y ω ∂P) / P.real S
  let G : Ω → ℝ := fun ω ↦ if τ ω ≤ (t : WithTop ℝ≥0) then H ω else c
  let R := restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}
  have hmτ : mτ ≤ mΩ := hτ.comap_le
  have hS : MeasurableSet[mΩ] S := measurableSet_lt measurable_const hτ
  have hiH : Integrable H P := integrable_condExp
  have hmH : StronglyMeasurable[mτ] H := stronglyMeasurable_condExp
  obtain ⟨g, hgm, hHg⟩ := hmH.exists_eq_measurable_comp
  have hR : Measurable[ℱ t] R := by
    apply measurable_iff_comap_le.mpr
    exact (natural_singleJumpCount_eq_comap_restricted hτ t).symm.le
  have heG : G = fun ω ↦
      if R ω ≤ (t : WithTop ℝ≥0) then g (R ω) else c := by
    funext ω
    dsimp only [G]
    by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
    · have hr : R ω = τ ω := restrictedStoppingTime_of_mem τ h
      simp only [hr, if_pos h]
      exact congrFun hHg ω
    · have hr : R ω = ⊤ := restrictedStoppingTime_of_notMem τ h
      simp only [hr, if_neg h, if_neg (WithTop.not_top_le_coe t)]
  have hmG : StronglyMeasurable[ℱ t] G := by
    rw [heG]
    exact (Measurable.ite (measurableSet_le hR measurable_const)
      (hgm.measurable.comp hR) measurable_const).stronglyMeasurable
  have hiG : Integrable G P := by
    refine (hiH.norm.add (integrable_const ‖c‖)).mono'
      (hmG.mono (ℱ.le t)).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    change ‖G ω‖ ≤ ‖H ω‖ + ‖c‖
    dsimp only [G]
    by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
    · rw [if_pos h]
      exact le_add_of_nonneg_right (norm_nonneg c)
    · rw [if_neg h]
      exact le_add_of_nonneg_left (norm_nonneg (H ω))
  have hGS : (∫ ω in S, G ω ∂P) = ∫ ω in S, Y ω ∂P := by
    calc
      (∫ ω in S, G ω ∂P) = ∫ _ in S, c ∂P := by
        apply setIntegral_congr_fun hS
        intro ω hω
        change (t : WithTop ℝ≥0) < τ ω at hω
        exact if_neg (not_le_of_gt hω)
      _ = P.real S * c := by rw [setIntegral_const, smul_eq_mul]
      _ = ∫ ω in S, Y ω ∂P := by
        dsimp only [c]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hSurvival)]
  change P[Y | ℱ t] =ᵐ[P] G
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le t) hY
    (fun _ _ _ ↦ hiG.integrableOn) ?_ hmG.aestronglyMeasurable
  intro E hE _
  obtain ⟨B, hB, hBt, he⟩ :=
    (measurableSet_natural_singleJumpCount_iff hτ t E).mp hE
  have hBτ : MeasurableSet[mτ] (τ ⁻¹' B) := ⟨B, hB, rfl⟩
  have hGB : (∫ ω in τ ⁻¹' B, G ω ∂P) = ∫ ω in τ ⁻¹' B, Y ω ∂P := by
    calc
      (∫ ω in τ ⁻¹' B, G ω ∂P) = ∫ ω in τ ⁻¹' B, H ω ∂P := by
        apply setIntegral_congr_fun (hτ hB)
        intro ω hω
        exact if_pos (hBt hω)
      _ = ∫ ω in τ ⁻¹' B, Y ω ∂P := setIntegral_condExp hmτ hY hBτ
  rcases he with rfl | rfl
  · exact hGB
  · have hd : Disjoint (τ ⁻¹' B) S := by
      apply Set.disjoint_left.mpr
      intro ω hω hs
      change (t : WithTop ℝ≥0) < τ ω at hs
      exact not_lt_of_ge (hBt hω) hs
    change (∫ ω in τ ⁻¹' B ∪ S, G ω ∂P) = ∫ ω in τ ⁻¹' B ∪ S, Y ω ∂P
    rw [setIntegral_union hd hS hiG.integrableOn hiG.integrableOn,
      setIntegral_union hd hS hY.integrableOn hY.integrableOn, hGB, hGS]

end ProbabilityTheory

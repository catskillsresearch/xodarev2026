/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ClassDPredictableJump
public import StochLean.Probability.Process.FiniteVariation.PredictableStepSeries
public import StochLean.Probability.Process.FiniteVariation.IntegrableJumps
public import StochLean.Probability.Process.Path.LifetimeStepSeriesJump
public import StochLean.Probability.Process.Path.LeftLimitAddition
public import StochLean.Probability.Process.Stopping.PredictableComparison

/-! # Regularity after an actual predictable jump correction series

The correction uses the negative conditional means of the original sampled
jumps, with explicit terminal zero at infinite lifetimes. Its absolute first
moment budget makes the actual closed-step series an integrable-variation
process. For each predictable test separately, disjoint finite graph collisions
are measurable in both before fields. Conditional expectation and the genuine
jump-series identity then cancel the original sampled jump in expectation.

The covering event may depend on the predictable test. No common event over
all random tests is asserted, and a covering graph need not consist of actual
nonzero jumps. The summable budget is an intermediate hypothesis, not a
compensator, a supermartingale, or a regularity certificate.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual summable predictable correction removes the mean jump at every
positive predictable test. Both summands' sampled jumps are proved integrable
before their integrals are added; an infinite test lifetime contributes zero. -/
theorem Adapted.integrable_stopped_jump_and_integral_eq_zero_tsum_neg_condExp
    (ha : Adapted F X) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (Γ : ℕ → Ω → WithTop ℝ≥0)
    (hΓ : ∀ n, IsPredictableStoppingTime F (Γ n) P)
    (hpΓ : ∀ n ω, 0 < Γ n ω)
    (hdΓ : Pairwise (fun n m ↦
      Disjoint (stoppingTimeGraph (Γ n)) (stoppingTimeGraph (Γ m))))
    (hcover : ∀ γ : Ω → WithTop ℝ≥0, IsPredictableStoppingTime F γ P →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω = (t : WithTop ℝ≥0) →
        jumpProcess X t ω ≠ 0 → ∃ n, Γ n ω = (t : WithTop ℝ≥0))
    (hs : Summable (fun n ↦ ∫ ω,
      ‖-P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) |
        (hΓ n).1.measurableSpaceBefore] ω‖ ∂P))
    {γ : Ω → WithTop ℝ≥0} (hγ : IsPredictableStoppingTime F γ P)
    (hpos : ∀ᵐ ω ∂P, 0 < γ ω) :
    let K : ℕ → Ω → ℝ := fun n ↦
      -P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) |
        (hΓ n).1.measurableSpaceBefore]
    let A : ℝ≥0 → Ω → ℝ := fun t ω ↦
      ∑' n, {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
    Integrable (stoppedValueWithTerminal (jumpProcess (X + A)) (fun _ ↦ (0 : ℝ)) γ) P ∧
      (∫ ω, stoppedValueWithTerminal (jumpProcess (X + A)) (fun _ ↦ (0 : ℝ)) γ ω ∂P) = 0 := by
  classical
  let J : ℕ → Ω → ℝ := fun n ↦
    stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n)
  let K : ℕ → Ω → ℝ := fun n ↦ -P[J n | (hΓ n).1.measurableSpaceBefore]
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦
    ∑' n, {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  let D : Ω → ℝ := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ
  let B : Ω → ℝ := stoppedValueWithTerminal (jumpProcess A) (fun _ ↦ (0 : ℝ)) γ
  change Integrable
      (stoppedValueWithTerminal (jumpProcess (X + A)) (fun _ ↦ (0 : ℝ)) γ) P ∧ _
  have hiJ (n : ℕ) : Integrable (J n) P :=
    hXD.integrable_stopped_jump_of_predictable hc (hΓ n) (ae_of_all _ (hpΓ n))
  have hiK (n : ℕ) : Integrable (K n) P := integrable_condExp.neg
  have hmK (n : ℕ) : StronglyMeasurable[(hΓ n).1.measurableSpaceBefore] (K n) :=
    stronglyMeasurable_condExp.neg
  have hsK : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P) := hs
  have hpA : IsStronglyPredictable F A :=
    isStronglyPredictable_tsum_indicator_stoppingTime_le hΓ hF.complete_initial hmK
  have hcA : HasCadlagPaths A P :=
    hasCadlagPaths_tsum_indicator_lifetime_le Γ hiK hsK
  have hvA : HasIntegrableVariation A P :=
    hasIntegrableVariation_tsum_indicator_stoppingTime_le hF hΓ hmK hiK hsK
  have hiD : Integrable D P :=
    ⟨((ha.stronglyMeasurable_stopped_jump_of_usual hF hc hγ.1).mono
      hγ.1.measurableSpace_le).aestronglyMeasurable,
      (hXD.integrable_stopped_jump_of_predictable hc hγ hpos).2⟩
  have hiB : Integrable B P :=
    hvA.integrable_stopped_jump hpA.stronglyAdapted.adapted hF hcA hγ.1 hpos
  let E : ℕ → Set Ω := fun n ↦ {ω | Γ n ω = γ ω ∧ γ ω ≠ ⊤}
  have hmEγ (n : ℕ) : MeasurableSet[hγ.1.measurableSpaceBefore] (E n) :=
    (hΓ n).measurableSet_eq_finite_before hγ.1 hF.complete_initial
  have hmE (n : ℕ) : MeasurableSet (E n) :=
    hγ.1.measurableSpaceBefore_le_ambient _ (hmEγ n)
  have hmEΓ (n : ℕ) : MeasurableSet[(hΓ n).1.measurableSpaceBefore] (E n) := by
    have he : E n = {ω | γ ω = Γ n ω ∧ Γ n ω ≠ ⊤} := by
      ext ω
      exact ⟨fun h ↦ ⟨h.1.symm, fun ht ↦ h.2 (h.1.symm.trans ht)⟩,
        fun h ↦ ⟨h.1.symm, fun ht ↦ h.2 (h.1.symm.trans ht)⟩⟩
    rw [he]
    exact hγ.measurableSet_eq_finite_before (hΓ n).1 hF.complete_initial
  have hdE : Pairwise (fun n m ↦ Disjoint (E n) (E m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro ω hn hm
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hn.2
    exact Set.disjoint_left.mp (hdΓ hnm)
      (show (t, ω) ∈ stoppingTimeGraph (Γ n) from hn.1.trans ht.symm)
      (show (t, ω) ∈ stoppingTimeGraph (Γ m) from hm.1.trans ht.symm)
  have hiEK (n : ℕ) : Integrable ((E n).indicator (K n)) P :=
    (hiK n).indicator (hmE n)
  have hsEK : Summable (fun n ↦ ∫ ω, ‖(E n).indicator (K n) ω‖ ∂P) := by
    apply hsK.of_nonneg_of_le
    · intro n
      exact integral_nonneg fun ω ↦ norm_nonneg _
    · intro n
      exact integral_mono (hiEK n).norm (hiK n).norm
        (fun ω ↦ norm_indicator_le_norm_self _ _)
  have heInt (n : ℕ) :
      (∫ ω, (E n).indicator (K n) ω ∂P) = -(∫ ω in E n, D ω ∂P) := by
    rw [integral_indicator (hmE n)]
    change (∫ ω in E n, -P[J n | (hΓ n).1.measurableSpaceBefore] ω ∂P) = _
    rw [integral_neg, setIntegral_condExp
      (hΓ n).1.measurableSpaceBefore_le_ambient (hiJ n) (hmEΓ n)]
    congr 1
    apply setIntegral_congr_fun (hmE n)
    intro ω hω
    change stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) ω = _
    simp only [D, stoppedValueWithTerminal, stoppedValue, hω.1]
  have heUnion : (⋃ n, E n).indicator D =ᵐ[P] D := by
    filter_upwards [hcover γ hγ, hpos] with ω hω hpω
    by_cases hD : D ω = 0
    · simp only [indicator_apply, hD, ite_self]
    · have hfin : γ ω ≠ ⊤ := by
        intro hh
        exact hD (stoppedValueWithTerminal_jump_eq_zero_of_top hh)
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfin
      have htpos : 0 < t := WithTop.coe_lt_coe.mp (ht.symm ▸ hpω)
      have hj : jumpProcess X t ω ≠ 0 := by
        change stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ ω ≠ 0 at hD
        rwa [stoppedValueWithTerminal_jump_eq_of_eq_coe ht.symm] at hD
      obtain ⟨n, hn⟩ := hω t htpos ht.symm hj
      exact indicator_of_mem
        (mem_iUnion.mpr ⟨n, show ω ∈ E n from ⟨hn.trans ht, hfin⟩⟩) D
  have hsumD : HasSum (fun n ↦ ∫ ω in E n, D ω ∂P) (∫ ω, D ω ∂P) := by
    have hsum := hasSum_integral_iUnion hmE hdE hiD.integrableOn
    have he : (∫ ω in ⋃ n, E n, D ω ∂P) = ∫ ω, D ω ∂P := by
      rw [← integral_indicator (MeasurableSet.iUnion hmE)]
      exact integral_congr_ae heUnion
    rwa [he] at hsum
  have heB : B =ᵐ[P] fun ω ↦ ∑' n, (E n).indicator (K n) ω := by
    filter_upwards [(ae_summable_norm_and_integrable_tsum_norm hiK hsK).1]
      with ω hω
    cases ht : γ ω with
    | top =>
      rw [show B ω = 0 from stoppedValueWithTerminal_jump_eq_zero_of_top ht]
      symm
      calc
        (∑' n, (E n).indicator (K n) ω) = ∑' _n : ℕ, (0 : ℝ) := by
          apply tsum_congr
          intro n
          exact indicator_of_notMem (fun hh ↦ hh.2 ht) _
        _ = 0 := tsum_zero
    | coe t =>
      rw [show B ω = jumpProcess A t ω from
        stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
      rw [show jumpProcess A t ω =
          ∑' n, {v | Γ n v = (t : WithTop ℝ≥0)}.indicator (K n) ω from
        jumpProcess_tsum_indicator_lifetime_le Γ K hω t]
      apply tsum_congr
      intro n
      have he : ω ∈ E n ↔ Γ n ω = (t : WithTop ℝ≥0) := by
        change Γ n ω = γ ω ∧ γ ω ≠ ⊤ ↔ _
        rw [ht]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, WithTop.coe_ne_top⟩⟩
      simp only [indicator_apply, mem_ofPred_eq, he]
  have hIB : (∫ ω, B ω ∂P) = -(∫ ω, D ω ∂P) := by
    calc
      (∫ ω, B ω ∂P) = ∫ ω, ∑' n, (E n).indicator (K n) ω ∂P :=
        integral_congr_ae heB
      _ = ∑' n, ∫ ω, (E n).indicator (K n) ω ∂P :=
        (integral_tsum_of_summable_integral_norm hiEK hsEK).symm
      _ = ∑' n, -(∫ ω in E n, D ω ∂P) := tsum_congr heInt
      _ = -(∫ ω, D ω ∂P) := hsumD.neg.tsum_eq
  have heAdd :
      stoppedValueWithTerminal (jumpProcess (X + A)) (fun _ ↦ (0 : ℝ)) γ =ᵐ[P]
        D + B := by
    filter_upwards [hc, hcA] with ω hx hA
    cases ht : γ ω with
    | top =>
      simp only [D, B, stoppedValueWithTerminal_jump_eq_zero_of_top ht,
        Pi.add_apply, add_zero]
    | coe t =>
      simp only [D, B, stoppedValueWithTerminal_jump_eq_of_eq_coe ht, Pi.add_apply]
      exact hx.jumpProcess_add hA t
  refine ⟨(hiD.add hiB).congr heAdd.symm, ?_⟩
  rw [integral_congr_ae heAdd]
  simp only [Pi.add_apply]
  rw [integral_add hiD hiB, hIB, add_neg_cancel]

end MeasureTheory

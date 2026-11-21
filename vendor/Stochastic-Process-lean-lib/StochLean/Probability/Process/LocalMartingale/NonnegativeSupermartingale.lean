/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.ForMathlib.MeasureTheory.FatouNonnegative
public import StochLean.ForMathlib.MeasureTheory.FatouLowerL1

/-! # Nonnegative local martingales are supermartingales

The proof retains the native Protter localization.  On an event in the
earlier sigma-field we intersect with the event that the localizer is still
strictly after the earlier time.  This makes the localized earlier value
exactly the original value; Fatou then passes the later value to the limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

/-- A nonnegative Protter local martingale with integrable initial value is a
supermartingale.  The separate initial-integrability hypothesis is necessary
for the project's masked local-martingale convention. -/
theorem IsLocalMartingale.supermartingale_of_nonneg
    (hX : IsLocalMartingale X F P) (h0i : Integrable (X 0) P)
    (hn : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ X t ω) : Supermartingale X F P := by
  obtain ⟨τ, hτ⟩ := hX.exists_klenkeLocalizingSequence h0i
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess X (τ n)
  have hYm (n : ℕ) : Martingale (Y n) F P := (hτ.2.2 n).1
  have hYnonneg (n : ℕ) (t : ℝ≥0) : 0 ≤ᵐ[P] Y n t := by
    filter_upwards [hn] with ω hω
    exact hω _
  have hYlim (t : ℝ≥0) : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ Y n t ω) atTop (𝓝 (X t ω)) := by
    filter_upwards [hτ.1.tendsto_top] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))] with n hnt
    exact (stoppedProcess_eq_of_le hnt.le).symm
  have hYintegral (n : ℕ) (t : ℝ≥0) : (∫ ω, Y n t ω ∂P) = ∫ ω, X 0 ω ∂P := by
    have he := (hYm n).setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le)
      MeasurableSet.univ
    have hzero : Y n 0 = X 0 := by
      funext ω
      exact stoppedProcess_eq_of_le bot_le
    simpa only [setIntegral_univ, hzero] using he.symm
  have hC : 0 ≤ ∫ ω, X 0 ω ∂P :=
    integral_nonneg_of_ae (hn.mono fun _ hω ↦ hω 0)
  have hXi (t : ℝ≥0) : Integrable (X t) P :=
    (integrable_and_integral_le_of_nonneg_ae_tendsto
      (fun n ↦ (hYm n).integrable t) (fun n ↦ hYnonneg n t) (hYlim t) hC
      (fun n ↦ (hYintegral n t).le)).1
  have hsub : Submartingale (-X) F P := by
    apply submartingale_of_setIntegral_le hX.1.stronglyAdapted.neg
      (fun t ↦ (hXi t).neg)
    intro s t hst A hA
    have hAm : MeasurableSet A := F.le s A hA
    let B : ℕ → Set Ω := fun n ↦ A ∩ {ω | (s : WithTop ℝ≥0) < τ n ω}
    have hBm (n : ℕ) : MeasurableSet[F s] (B n) :=
      hA.inter ((hτ.1.isStoppingTime n).measurableSet_gt s)
    have hBm' (n : ℕ) : MeasurableSet (B n) := F.le s _ (hBm n)
    let f : ℕ → Ω → ℝ := fun n ↦ (B n).indicator (Y n t)
    have hfi (n : ℕ) : Integrable (f n) P :=
      ((hYm n).integrable t).indicator (hBm' n)
    have hfn (n : ℕ) : 0 ≤ᵐ[P] f n := by
      filter_upwards [hYnonneg n t] with ω hω
      exact Set.indicator_nonneg (fun _ _ ↦ hω) ω
    have hflim : ∀ᵐ ω ∂P,
        Tendsto (fun n ↦ f n ω) atTop (𝓝 (A.indicator (X t) ω)) := by
      filter_upwards [hτ.1.tendsto_top, hn] with ω hτω hnω
      apply tendsto_const_nhds.congr'
      filter_upwards [hτω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))] with n hnt
      have hsn : (s : WithTop ℝ≥0) < τ n ω :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr hst) hnt
      change A.indicator (X t) ω =
        (B n).indicator (stoppedProcess X (τ n) t) ω
      have he : stoppedProcess X (τ n) t ω = X t ω :=
        stoppedProcess_eq_of_le hnt.le
      by_cases hωA : ω ∈ A
      · rw [Set.indicator_of_mem hωA,
          Set.indicator_of_mem (show ω ∈ B n from ⟨hωA, hsn⟩), he]
      · rw [Set.indicator_of_notMem hωA,
          Set.indicator_of_notMem (show ω ∉ B n from fun hωB ↦ hωA hωB.1)]
    have hbound (n : ℕ) : (∫ ω, f n ω ∂P) ≤ ∫ ω in A, X s ω ∂P := by
      rw [show (∫ ω, f n ω ∂P) = ∫ ω in B n, Y n t ω ∂P by
        exact integral_indicator (hBm' n)]
      rw [← (hYm n).setIntegral_eq hst (hBm n)]
      have heq : ∫ ω in B n, Y n s ω ∂P = ∫ ω in B n, X s ω ∂P := by
        apply setIntegral_congr_fun (hBm' n)
        intro ω hω
        exact stoppedProcess_eq_of_le hω.2.le
      rw [heq]
      exact setIntegral_mono_set (hXi s).integrableOn
        (ae_restrict_of_ae (hn.mono fun _ hω ↦ hω s))
        (Eventually.of_forall fun _ hω ↦ hω.1)
    have hFatou := integral_le_of_ae_tendsto_of_L1_lower_bound
      hfi (fun _ ↦ integrable_zero _ _ _) ((hXi t).indicator hAm)
      (integrable_zero _ _ _) hflim (ae_of_all P fun _ ↦ tendsto_const_nhds)
      (by simp) (fun n ↦ hfn n)
      (C := ∫ ω in A, X s ω ∂P) hbound
    rw [integral_indicator hAm] at hFatou
    change (∫ ω in A, -X s ω ∂P) ≤ ∫ ω in A, -X t ω ∂P
    rw [integral_neg, integral_neg]
    exact neg_le_neg hFatou
  simpa only [neg_neg] using hsub.neg

end ProbabilityTheory

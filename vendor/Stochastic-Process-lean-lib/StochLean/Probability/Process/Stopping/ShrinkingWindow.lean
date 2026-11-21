/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PredictableLimitPart
public import StochLean.Probability.Process.Stopping.Finite
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Shrinking windows before a totally inaccessible time

For increasing bounded stopping times and decreasing trigger events, the
probability of a triggered shrinking window tends to zero. Strictness before
the totally inaccessible time is required only on the corresponding trigger
event, not at an artificial bounded fallback. The no-collision conclusion is
derived from the predictable strict-limit part of the stopping times.

The lower endpoint of every window is strict. In particular, sampling at the
lifetime itself does not create a spurious event. Infinity is treated
explicitly and is never replaced by a finite default.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : Ω → WithTop ℝ≥0}
  {σ : ℕ → FiniteStoppingTime F} {E : ℕ → Set Ω} {δ : ℕ → ℝ≥0}

theorem IsTotallyInaccessibleStoppingTime.ae_eventually_not_mem_shrinking_stopping_window
    (ht : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hm : ∀ ω, Monotone (fun n ↦ σ n ω))
    {ν : ℝ≥0} (hb : ∀ n ω, σ n ω ≤ ν) (hE : Antitone E)
    (hstrict : ∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (σ n ω : WithTop ℝ≥0) < τ ω)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∉ E n ∩ {ω | (σ n ω : WithTop ℝ≥0) < τ ω ∧
        τ ω ≤ ((σ n ω + δ n : ℝ≥0) : WithTop ℝ≥0)} := by
  have hnull := ht.measure_strict_iSup_eq_zero (fun n ↦ (σ n).isStoppingTime)
    (fun ω i j hij ↦ WithTop.coe_le_coe.mpr (hm ω hij)) hF
  have havoid : ∀ᵐ ω ∂P,
      ¬ ((⨆ n, (σ n ω : WithTop ℝ≥0)) = τ ω ∧ τ ω ≠ ⊤ ∧
        ∀ n, (σ n ω : WithTop ℝ≥0) < τ ω) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [havoid, ae_all_iff.mpr hstrict] with ω havoid hstrict
  by_cases hω : ∀ n, ω ∈ E n
  · have hs : ∀ n, (σ n ω : WithTop ℝ≥0) < τ ω := fun n ↦ hstrict n (hω n)
    have hsup_le : (⨆ n, (σ n ω : WithTop ℝ≥0)) ≤ τ ω :=
      iSup_le fun n ↦ (hs n).le
    have hsup_finite : (⨆ n, (σ n ω : WithTop ℝ≥0)) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top
        (iSup_le fun n ↦ WithTop.coe_le_coe.mpr (hb n ω))
    have hsup_lt : (⨆ n, (σ n ω : WithTop ℝ≥0)) < τ ω := by
      apply lt_of_le_of_ne hsup_le
      intro he
      apply havoid
      refine ⟨he, ?_, hs⟩
      rw [← he]
      exact hsup_finite
    cases heτ : τ ω with
    | top =>
      filter_upwards with n hn
      exact WithTop.not_top_le_coe _ (heτ ▸ hn.2.2)
    | coe q =>
      cases heS : (⨆ n, (σ n ω : WithTop ℝ≥0)) with
      | top => exact (hsup_finite heS).elim
      | coe s =>
        have hsq : s < q := WithTop.coe_lt_coe.mp (by
          simpa only [heS, heτ] using hsup_lt)
        have hlim : Tendsto (fun n ↦ s + δ n) atTop (𝓝 s) := by
          simpa only [add_zero] using tendsto_const_nhds.add hδ
        filter_upwards [hlim.eventually_lt_const hsq] with n hn hmem
        have hns : σ n ω ≤ s := WithTop.coe_le_coe.mp (by
          simpa only [heS] using le_iSup (fun k ↦ (σ k ω : WithTop ℝ≥0)) n)
        have hq : q ≤ σ n ω + δ n := WithTop.coe_le_coe.mp (heτ ▸ hmem.2.2)
        have hsum : σ n ω + δ n ≤ s + δ n := by gcongr
        exact (not_le_of_gt (hsum.trans_lt hn)) hq
  · obtain ⟨N, hN⟩ := not_forall.mp hω
    filter_upwards [eventually_ge_atTop N] with n hn hmem
    exact hN (hE hn hmem.1)

theorem IsTotallyInaccessibleStoppingTime.tendsto_measureReal_shrinking_stopping_window
    (ht : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hm : ∀ ω, Monotone (fun n ↦ σ n ω))
    {ν : ℝ≥0} (hb : ∀ n ω, σ n ω ≤ ν) (hE : Antitone E)
    (hmE : ∀ n, MeasurableSet (E n))
    (hstrict : ∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (σ n ω : WithTop ℝ≥0) < τ ω)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n ↦ P.real (E n ∩ {ω | (σ n ω : WithTop ℝ≥0) < τ ω ∧
      τ ω ≤ ((σ n ω + δ n : ℝ≥0) : WithTop ℝ≥0)})) atTop (𝓝 0) := by
  let W : ℕ → Set Ω := fun n ↦ E n ∩
    {ω | (σ n ω : WithTop ℝ≥0) < τ ω ∧
      τ ω ≤ ((σ n ω + δ n : ℝ≥0) : WithTop ℝ≥0)}
  have hmτ : Measurable τ := ht.1.measurable.mono ht.1.measurableSpace_le le_rfl
  have hmσ (n : ℕ) : Measurable (σ n) :=
    ((σ n).isStoppingTime.measurable.untopD 0).mono (σ n).measurableSpace_le le_rfl
  have hmW (n : ℕ) : MeasurableSet (W n) :=
    (hmE n).inter ((measurableSet_lt (WithTop.measurable_coe.comp (hmσ n)) hmτ).inter
      (measurableSet_le hmτ (WithTop.measurable_coe.comp ((hmσ n).add measurable_const))))
  have hevent := ht.ae_eventually_not_mem_shrinking_stopping_window hF hm hb hE hstrict hδ
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (W n).indicator (fun _ ↦ (1 : ℝ)) ω)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hevent] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    exact (indicator_of_notMem hn (fun _ ↦ (1 : ℝ))).symm
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
    (fun n ↦ (measurable_const.indicator (hmW n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n ↦ Eventually.of_forall fun ω ↦
      (norm_indicator_le_norm_self (fun _ : Ω ↦ (1 : ℝ)) ω).trans_eq (norm_one (α := ℝ)))
    hlim
  simpa only [integral_indicator (hmW _), integral_const, Measure.real,
    Measure.restrict_apply_univ, smul_eq_mul, mul_one, mul_zero, integral_zero, W] using hint

end ProbabilityTheory

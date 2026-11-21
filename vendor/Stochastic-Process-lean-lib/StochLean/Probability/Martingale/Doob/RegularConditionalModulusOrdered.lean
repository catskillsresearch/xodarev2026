/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.StoppingLeftExpectation
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedUsual
public import StochLean.Probability.Process.Stopping.ThresholdHitting
public import StochLean.Probability.Process.Stopping.Delay
public import StochLean.Probability.Process.Path.Supremum

/-! # Ordered signed conditional increments at regular supermartingales

For the actual conditional increment versions `R n`, increasing first-threshold
times reduce the compact running-supremum estimate to expectations of sampled
source increments. Predictable zero jump means give left continuity of these
expectations. Right continuity and Class D give actual L1 convergence of the
delayed limiting samples. Conditional optional sampling compares the two upper
endpoints, without requiring their sequences to be monotone.

The lower threshold estimate holds only on the actual capped-hit trigger event;
nonnegativity controls its complement. No totally inaccessible hypothesis or
vanishing probability of unweighted jump occurrence is used. The conditional
versions and their valid stopping identities are inputs to this intermediate
lemma, not assumptions of a final Doob-Meyer existence theorem.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  {δ : ℕ → ℝ≥0} {R : ℕ → ℝ≥0 → Ω → ℝ}

/-- Compact maxima of ordered, actually sampled signed conditional increments
vanish in probability. Class D suffices; a common deterministic source bound
and monotonicity or positivity of the widths are not additional premises. -/
theorem Supermartingale.tendsto_measureReal_denseRunningSupremum_of_ordered_conditional_increments
    (hX : Supermartingale X F P) (hD : IsClassD X F P)
    (hc : HasCadlagPaths X P) (hF : F.IsUsual P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (hδ : Tendsto δ atTop (𝓝 0))
    (haR : ∀ n, StronglyAdapted F (R n))
    (hrR : ∀ n ω, IsRightContinuousPath (R n · ω))
    (hnR : ∀ n, ∀ᵐ ω ∂P, ∀ t, 0 ≤ R n t ω)
    (hmR : ∀ t ω, Antitone (fun n ↦ R n t ω))
    (heR : ∀ n (σ : FiniteStoppingTime F) (T : ℝ≥0), (∀ ω, σ ω ≤ T) →
      (fun ω ↦ R n (σ ω) ω) =ᵐ[P]
        (fun ω ↦ X (σ ω) ω) -
          P[(fun ω ↦ X (σ ω + δ n) ω) | σ.measurableSpace])
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R n) T ω})
      atTop (𝓝 0) := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  let H : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ hittingAfter (R n) (Ioi a) 0
  have hH (n : ℕ) : IsStoppingTime F (H n) :=
    (haR n).adapted.isStoppingTime_hittingAfter_isOpen (hrR n) isOpen_Ioi 0
  let σ : ℕ → FiniteStoppingTime F := fun n ↦ FiniteStoppingTime.truncate (hH n) T
  let E : ℕ → Set Ω := fun n ↦ {ω | H n ω ≤ (T : WithTop ℝ≥0)}
  have hmH (ω : Ω) : Monotone (fun n ↦ H n ω) :=
    monotone_hittingAfter_Ioi_of_antitone hmR a 0 ω
  have hmσ (ω : Ω) : Monotone (fun n ↦ σ n ω) := fun i j hij ↦
    FiniteStoppingTime.truncate_mono_of_le (hH i) (hH j) (fun ω ↦ hmH ω hij) T ω
  have hbσ (n : ℕ) (ω : Ω) : σ n ω ≤ T := FiniteStoppingTime.truncate_le (hH n) T ω
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    (σ n).measurableSpace_le _ (FiniteStoppingTime.measurableSet_truncate_trigger (hH n) T)
  let S : Ω → WithTop ℝ≥0 := fun ω ↦ ⨆ n, (σ n ω : WithTop ℝ≥0)
  have hS : IsStoppingTime F S := IsStoppingTime.iSup_nnreal (fun n ↦ (σ n).isStoppingTime)
  have hbS (ω : Ω) : S ω ≤ (T : WithTop ℝ≥0) :=
    iSup_le fun n ↦ WithTop.coe_le_coe.mpr (hbσ n ω)
  have hfS (ω : Ω) : S ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hbS ω)
  let τ : FiniteStoppingTime F := FiniteStoppingTime.ofNotTop hS hfS
  have heτ (ω : Ω) : (τ ω : WithTop ℝ≥0) = S ω :=
    congrFun (FiniteStoppingTime.withTop_ofNotTop hS hfS) ω
  have hbτ (ω : Ω) : τ ω ≤ T := WithTop.coe_le_coe.mp ((heτ ω).trans_le (hbS ω))
  have hστ (n : ℕ) (ω : Ω) : σ n ω ≤ τ ω := by
    apply WithTop.coe_le_coe.mp
    rw [heτ ω]
    exact le_iSup (fun k ↦ (σ k ω : WithTop ℝ≥0)) n
  have hlimσ (ω : Ω) : Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) := by
    have hh : Tendsto (fun n ↦ (σ n ω : WithTop ℝ≥0)) atTop (𝓝 (S ω)) :=
      tendsto_atTop_iSup (fun i j hij ↦ WithTop.coe_le_coe.mpr (hmσ ω hij))
    have he := (WithTop.tendsto_untopA (hfS ω)).comp hh
    exact he
  have hleft := hD.tendsto_integral_finiteStoppingTime_of_monotone_of_predictable_jump_mean_zero
    hc hF hreg σ τ hmσ hlimσ
  let addTime (ρ : FiniteStoppingTime F) (c : ℝ≥0) : FiniteStoppingTime F :=
    ⟨fun ω ↦ ρ ω + c, by
      simpa only [WithTop.coe_add] using ρ.isStoppingTime.add_const_nnreal c⟩
  let υ : ℕ → FiniteStoppingTime F := fun n ↦ addTime τ (δ n)
  let ρ : ℕ → FiniteStoppingTime F := fun n ↦ addTime (σ n) (δ n)
  have hu : UniformIntegrable (fun n ω ↦ X (υ n ω) ω) 1 P :=
    hD.uniformIntegrable_finiteStoppingTime υ
  have hiτ : Integrable (fun ω ↦ X (τ ω) ω) P := hD.integrable_finiteStoppingTime_value τ
  have hrightPath : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (υ n ω) ω) atTop
      (𝓝 (X (τ ω) ω)) := by
    filter_upwards [hc] with ω hcω
    apply (hcω.1 (τ ω)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ le_add_of_nonneg_right (show 0 ≤ δ n from bot_le)⟩
    simpa only [add_zero] using (tendsto_const_nhds (x := τ ω)).add hδ
  have hrightL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (memLp_one_iff_integrable.mpr hiτ) hu.2.1 hrightPath
  have hright := tendsto_integral_of_L1' (fun ω ↦ X (τ ω) ω) hiτ.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hD.integrable_finiteStoppingTime_value (υ n)) hrightL1
  have hdiff : Tendsto
      (fun n ↦ ((∫ ω, X (σ n ω) ω ∂P) - ∫ ω, X (υ n ω) ω ∂P) / a)
      atTop (𝓝 0) := by
    simpa only [sub_self, zero_div] using (hleft.sub hright).div_const a
  have hbound (n : ℕ) : a * P.real (E n) ≤
      (∫ ω, X (σ n ω) ω ∂P) - ∫ ω, X (υ n ω) ω ∂P := by
    have hiσ := hD.integrable_finiteStoppingTime_value (σ n)
    have hiρ := hD.integrable_finiteStoppingTime_value (ρ n)
    have hs := heR n (σ n) T (hbσ n)
    have hiR : Integrable (fun ω ↦ R n (σ n ω) ω) P :=
      (hiσ.sub integrable_condExp).congr hs.symm
    have hind : (E n).indicator (fun _ ↦ a) ≤ᵐ[P] (fun ω ↦ R n (σ n ω) ω) := by
      filter_upwards [hnR n] with ω hn
      by_cases hω : ω ∈ E n
      · rw [indicator_of_mem hω]
        exact FiniteStoppingTime.le_process_truncate_hittingAfter_Ioi_of_trigger
          (hH n) (hrR n) hω
      · rw [indicator_of_notMem hω]
        exact hn (σ n ω)
    have hI := integral_mono_ae ((integrable_const a).indicator (hEm n)) hiR hind
    have hIa : a * P.real (E n) ≤ ∫ ω, R n (σ n ω) ω ∂P := by
      simpa only [integral_indicator (hEm n), integral_const, Measure.real,
        Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using hI
    have hIR : (∫ ω, R n (σ n ω) ω ∂P) =
        (∫ ω, X (σ n ω) ω ∂P) - ∫ ω, X (ρ n ω) ω ∂P := by
      calc
        _ = ∫ ω, X (σ n ω) ω - P[(fun v ↦ X (ρ n v) v) | (σ n).measurableSpace] ω ∂P :=
          integral_congr_ae hs
        _ = _ := by
          rw [integral_sub hiσ integrable_condExp, integral_condExp (σ n).measurableSpace_le]
    have hcomp := hX.condExp_finiteStoppingTime_value_ae_le_of_le hF
      hc.hasRightContinuousPaths (ρ n) (υ n) (T := T + δ n)
      (fun ω ↦ show σ n ω + δ n ≤ τ ω + δ n from add_le_add (hστ n ω) le_rfl)
      (fun ω ↦ show τ ω + δ n ≤ T + δ n from add_le_add (hbτ ω) le_rfl)
    have horder : (∫ ω, X (υ n ω) ω ∂P) ≤ ∫ ω, X (ρ n ω) ω ∂P := by
      have h := integral_mono_ae integrable_condExp hiρ hcomp
      rwa [integral_condExp (ρ n).measurableSpace_le] at h
    exact (hIa.trans_eq hIR).trans (sub_le_sub_left horder _)
  have hsub (n : ℕ) : {ω | ENNReal.ofReal a < denseRunningSupremum (R n) T ω} ⊆ E n := by
    intro ω hω
    change ENNReal.ofReal a < ⨆ k, ENNReal.ofReal (R n (denseTimeUpTo T k) ω) at hω
    obtain ⟨k, hk⟩ := lt_iSup_iff.mp hω
    have hh : a < R n (denseTimeUpTo T k) ω :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mp hk
    exact (hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ denseTimeUpTo T k from bot_le) hh).trans
      (WithTop.coe_le_coe.mpr (min_le_left T (TopologicalSpace.denseSeq ℝ≥0 k)))
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hdiff
  intro n
  apply (measureReal_mono (hsub n)).trans
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using hbound n

end MeasureTheory

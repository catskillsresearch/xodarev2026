/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.LocalMartingale.PredictableFiniteVariation
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps

/-! # Continuous compensators for totally inaccessible source jumps

The actual predictable compensator of an adapted cadlag locally-IV source
with totally inaccessible positive-time jumps has continuous paths. The
source need not be increasing, nonnegative, zero-initial, or initially L1.

At a positive predictable lifetime the source jump vanishes, so the jump of
the actual local-martingale remainder is the negative compensator jump. It
is therefore before-measurable. The localized UI martingales have genuinely
integrable jump samples and zero before-conditional mean; before-measurability
makes those samples zero. Only afterwards does localization recover the
original sample, which was not assumed globally integrable.

The closed stopping endpoint uses the before-measurable event that the test
lifetime is at most the localizer. Infinite samples have explicit terminal
zero. The compensator's own constructed countable predictable jump cover
then removes all positive jumps on a common path event, proving continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

private theorem stopped_jump_eq_zero_of_aestronglyMeasurable_before
    {M : ℝ≥0 → Ω → ℝ} (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsPredictableStoppingTime F σ P)
    (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    (hmJ : AEStronglyMeasurable[hσ.1.measurableSpaceBefore]
      (stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) σ) P) :
    stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) σ =ᵐ[P] 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := hM.2.2
  let E (n : ℕ) : Set Ω := {ω | 0 < ρ n ω}
  let Y (n : ℕ) := MeasureTheory.stoppedProcess (fun t ↦ (E n).indicator (M t)) (ρ n)
  let J := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) σ
  let K (n : ℕ) := (E n).indicator ({ω | σ ω ≤ ρ n ω}.indicator J)
  have hE (n : ℕ) : MeasurableSet[F 0] (E n) :=
    (hρ.1.isStoppingTime n).measurableSet_gt 0
  have hKzero (n : ℕ) : K n =ᵐ[P] 0 := by
    have hcap : MeasurableSet[hσ.1.measurableSpaceBefore] {ω | σ ω ≤ ρ n ω} := by
      simpa only [compl_ofPred, not_lt] using
        ((hρ.1.isStoppingTime n).measurableSet_lt_before hσ.1).compl
    have hmK : AEStronglyMeasurable[hσ.1.measurableSpaceBefore] (K n) P := by
      refine ⟨(E n).indicator ({ω | σ ω ≤ ρ n ω}.indicator (hmJ.mk J)),
        (hmJ.stronglyMeasurable_mk.indicator hcap).indicator
          (hσ.1.le_measurableSpaceBefore _ (hE n)), ?_⟩
      filter_upwards [hmJ.ae_eq_mk] with ω hω
      simp only [K, indicator_apply]
      split_ifs <;> first | exact hω | rfl
    have hcY : HasCadlagPaths (Y n) P := (hM.2.1.indicator (E n)).stoppedProcess (ρ n)
    obtain ⟨hi, hz⟩ :=
      (hρ.2.2 n).1.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
        (hρ.2.2 n).2 hF hcY hσ hpos
    have he : stoppedValueWithTerminal (jumpProcess (Y n)) (fun _ ↦ (0 : ℝ)) σ =ᵐ[P]
        K n := hM.2.1.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess (E n) (ρ n) σ
    have hiK : Integrable (K n) P := hi.congr he
    have hCE : P[K n | hσ.1.measurableSpaceBefore] =ᵐ[P] 0 :=
      (condExp_congr_ae he).symm.trans hz
    exact (condExp_of_aestronglyMeasurable' hσ.1.measurableSpaceBefore_le_ambient
      hmK hiK).symm.trans hCE
  have hall : ∀ᵐ ω ∂P, ∀ n, K n ω = 0 := by
    rw [ae_all_iff]
    exact hKzero
  filter_upwards [hall, hρ.1.tendsto_top] with ω hzero hlim
  cases hs : σ ω with
  | top => exact stoppedValueWithTerminal_jump_eq_zero_of_top hs
  | coe t =>
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
    have hEω : ω ∈ E n := lt_of_le_of_lt bot_le hn
    have hcap : ω ∈ {ω | σ ω ≤ ρ n ω} := by
      change σ ω ≤ ρ n ω
      rw [hs]
      exact hn.le
    simpa only [K, J, Pi.zero_apply, indicator_of_mem hEω, indicator_of_mem hcap] using hzero n

namespace HasLocallyIntegrableVariation

/-- Totally inaccessible source jumps force the actual selected predictable
compensator to be continuous. Source monotonicity is not needed. -/
theorem hasContinuousPaths_predictableCompensator_of_totallyInaccessibleJumps
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hTI : HasTotallyInaccessibleJumps F X P) :
    HasContinuousPaths (hv.predictableCompensator ha hF hc) P := by
  let B := hv.predictableCompensator ha hF hc
  let M := X - B
  obtain ⟨hpB, hcB', _, hvB, hM⟩ := hv.predictableCompensator_properties ha hF hc
  have hcB : HasCadlagPaths B P := Eventually.of_forall hcB'
  obtain ⟨σ, hσ, hpos, _, hcover⟩ :=
    hpB.exists_positive_disjoint_predictableStoppingTime_cover_jumps hF
      hcB hvB.hasFiniteVariationPaths
  have hz (n : ℕ) :
      stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) (σ n) =ᵐ[P] 0 := by
    let JM := stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (σ n)
    let JB := stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) (σ n)
    have he : JM =ᵐ[P] -JB := by
      filter_upwards [hc, hcB, hTI.ae_jumpProcess_eq_zero_at_predictable (hσ n)]
        with ω hx hb hzero
      cases hs : σ n ω with
      | top =>
        simp only [JM, JB, stoppedValueWithTerminal_jump_eq_zero_of_top hs,
          Pi.neg_apply, neg_zero]
      | coe t =>
        have ht : 0 < t := WithTop.coe_lt_coe.mp (hs ▸ hpos n ω)
        simp only [JM, JB, stoppedValueWithTerminal_jump_eq_of_eq_coe hs, Pi.neg_apply]
        change jumpProcess (X - B) t ω = -jumpProcess B t ω
        rw [hx.jumpProcess_sub hb t, hzero t ht hs, zero_sub]
    have hmJB : StronglyMeasurable[(hσ n).1.measurableSpaceBefore] JB :=
      hpB.stronglyMeasurable_stopped_jump_before_of_finiteVariation hF
        hcB hvB.hasFiniteVariationPaths (hσ n).1
    have hmJM : AEStronglyMeasurable[(hσ n).1.measurableSpaceBefore] JM P :=
      hmJB.neg.aestronglyMeasurable.congr he.symm
    have hzM : JM =ᵐ[P] 0 := stopped_jump_eq_zero_of_aestronglyMeasurable_before
      hM hF (hσ n) (Eventually.of_forall (hpos n)) hmJM
    filter_upwards [he, hzM] with ω heω hzω
    change JB ω = 0
    exact neg_eq_zero.mp (heω.symm.trans hzω)
  have hall : ∀ᵐ ω ∂P, ∀ n,
      stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) (σ n) ω = 0 := by
    rw [ae_all_iff]
    exact hz
  apply hcB.hasContinuousPaths_of_jumpProcess_eq_zero
  filter_upwards [hall, hcover] with ω hzero hcov t ht
  by_contra hj
  obtain ⟨n, hn⟩ := hcov t (pos_iff_ne_zero.mpr ht) hj
  exact hj ((stoppedValueWithTerminal_jump_eq_of_eq_coe hn).symm.trans (hzero n))

end HasLocallyIntegrableVariation
end ProbabilityTheory

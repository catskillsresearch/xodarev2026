/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousBoundedJumps
public import StochLean.Probability.Martingale.Doob.SingleJumpContinuous
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumpAlgebra
public import StochLean.Probability.Process.Stopping.JumpCoefficients

/-! # Continuous Doob decomposition with one potentially unbounded jump

The exceptional amplitude is the actual source jump sampled with explicitly
zero terminal value. Its positive and negative parts give two integrable
negative single jumps. The existing single-jump theorem constructs their
continuous compensators and true Class D martingales.

Adding the first martingale and subtracting the second cancels the actual
exceptional jump. The resulting Class D supermartingale has bounded jump
norms, so the bounded-jump theorem supplies its increasing compensator.
Subtracting and adding back the two martingales gives the original process
the very same increasing compensator. In particular no difference of
increasing processes is falsely asserted to be increasing.

The exceptional lifetime may be infinite. No compensator, limit, or
uniform-integrability certificate is required in the hypotheses.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

/-- The single potentially unbounded jump is removed by actual compensated
single-jump martingales. The original process need not stop at that lifetime. -/
theorem Supermartingale.exists_continuous_doob_decomposition_of_one_large_jump
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hJ : HasTotallyInaccessibleJumps F X P)
    (h0 : X 0 =ᵐ[P] 0) (hσ : IsTotallyInaccessibleStoppingTime F σ P)
    (hm : StronglyMeasurable[hσ.1.measurableSpace]
      (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ))
    (hi : Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ) P)
    (hb : 0 ≤ b)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≠ σ ω →
      ‖jumpProcess X t ω‖ ≤ b) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      IsClassD A F P ∧ Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  classical
  let D := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ
  let Cp : Ω → ℝ := fun ω ↦ max (D ω) 0
  let Cm : Ω → ℝ := fun ω ↦ max (-D ω) 0
  let Jp : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -Cp ω)
  let Jm : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -Cm ω)
  have hmp : StronglyMeasurable[hσ.1.measurableSpace] Cp := by
    let : MeasurableSpace Ω := hσ.1.measurableSpace
    exact hm.sup stronglyMeasurable_const
  have hmm : StronglyMeasurable[hσ.1.measurableSpace] Cm := by
    let : MeasurableSpace Ω := hσ.1.measurableSpace
    exact hm.neg.sup stronglyMeasurable_const
  have hip : Integrable Cp P := hi.sup (integrable_const 0)
  have him : Integrable Cm P := hi.neg.sup (integrable_const 0)
  obtain ⟨Ap, _, _, _, _, hpc, hp0, _, _, _, _, _, _, _, _, hpM, hpMc, hpMD, _⟩ :=
    hσ.exists_continuous_compensator_neg hF hmp hip
      (Eventually.of_forall fun _ ↦ le_max_right _ _)
  obtain ⟨Am, _, _, _, _, hmc, hm0, _, _, _, _, _, _, _, _, hmM, hmMc, hmMD, _⟩ :=
    hσ.exists_continuous_compensator_neg hF hmm him
      (Eventually.of_forall fun _ ↦ le_max_right _ _)
  let Mp := Jp + Ap
  let Mm := Jm + Am
  let Y := X + Mp - Mm
  have hYs : Supermartingale Y F P := (hX.add_martingale hpM).sub_martingale hmM
  have hYD : IsClassD Y F P := (hXD.add hpMD).sub hmMD
  have hYc : HasCadlagPaths Y P := (hc.add hpMc).sub hmMc
  have hJpc : HasCadlagPaths Jp P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le σ (fun ω ↦ -Cp ω))
  have hJmc : HasCadlagPaths Jm P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le σ (fun ω ↦ -Cm ω))
  have hMpJ : HasTotallyInaccessibleJumps F Mp P :=
    (hσ.hasTotallyInaccessibleJumps_indicator (fun ω ↦ -Cp ω)).add_continuous
      hJpc (Eventually.of_forall hpc)
  have hMmJ : HasTotallyInaccessibleJumps F Mm P :=
    (hσ.hasTotallyInaccessibleJumps_indicator (fun ω ↦ -Cm ω)).add_continuous
      hJmc (Eventually.of_forall hmc)
  have hYJ : HasTotallyInaccessibleJumps F Y P :=
    (hJ.add hMpJ hc hpMc).sub hMmJ (hc.add hpMc) hmMc
  have hpz : Mp 0 =ᵐ[P] 0 := by
    filter_upwards [hσ.indicator_initial_ae_eq_zero (fun ω ↦ -Cp ω)] with ω hω
    change Jp 0 ω + Ap 0 ω = 0
    change Jp 0 ω = 0 at hω
    rw [hω, congrFun hp0 ω]
    simp only [Pi.zero_apply, zero_add]
  have hmz : Mm 0 =ᵐ[P] 0 := by
    filter_upwards [hσ.indicator_initial_ae_eq_zero (fun ω ↦ -Cm ω)] with ω hω
    change Jm 0 ω + Am 0 ω = 0
    change Jm 0 ω = 0 at hω
    rw [hω, congrFun hm0 ω]
    simp only [Pi.zero_apply, zero_add]
  have hY0 : Y 0 =ᵐ[P] 0 := by
    filter_upwards [h0, hpz, hmz] with ω hx hp hn
    change X 0 ω + Mp 0 ω - Mm 0 ω = 0
    rw [hx, hp, hn]
    simp only [Pi.zero_apply, zero_add, sub_zero]
  have hYj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess Y t ω‖ ≤ b := by
    filter_upwards [hc, hj] with ω hx hω t ht
    have hpcω : IsCadlagPath (Ap · ω) := IsContinuousPath.isCadlagPath (hpc ω)
    have hmcω : IsCadlagPath (Am · ω) := IsContinuousPath.isCadlagPath (hmc ω)
    have hpω : IsCadlagPath (Jp · ω) :=
      isCadlagPath_indicator_lifetime_le σ (fun ω ↦ -Cp ω) ω
    have hmω : IsCadlagPath (Jm · ω) :=
      isCadlagPath_indicator_lifetime_le σ (fun ω ↦ -Cm ω) ω
    have hMpω : IsCadlagPath (Mp · ω) := hpω.add hpcω
    have hMmω : IsCadlagPath (Mm · ω) := hmω.add hmcω
    have hjp : jumpProcess Mp t ω = if σ ω = (t : WithTop ℝ≥0) then -Cp ω else 0 := by
      change jumpProcess (Jp + Ap) t ω = _
      rw [hpω.jumpProcess_add hpcω,
        IsContinuousPath.jumpProcess_eq_zero (hpc ω) (ne_of_gt ht), add_zero]
      have he : jumpProcess Jp t ω =
          {v | σ v = (t : WithTop ℝ≥0)}.indicator (fun v ↦ -Cp v) ω :=
        jumpProcess_indicator_lifetime_le σ (fun ω ↦ -Cp ω) t ω
      simpa only [indicator_apply, mem_ofPred_eq] using he
    have hjm : jumpProcess Mm t ω = if σ ω = (t : WithTop ℝ≥0) then -Cm ω else 0 := by
      change jumpProcess (Jm + Am) t ω = _
      rw [hmω.jumpProcess_add hmcω,
        IsContinuousPath.jumpProcess_eq_zero (hmc ω) (ne_of_gt ht), add_zero]
      have he : jumpProcess Jm t ω =
          {v | σ v = (t : WithTop ℝ≥0)}.indicator (fun v ↦ -Cm v) ω :=
        jumpProcess_indicator_lifetime_le σ (fun ω ↦ -Cm ω) t ω
      simpa only [indicator_apply, mem_ofPred_eq] using he
    change ‖jumpProcess (X + Mp - Mm) t ω‖ ≤ b
    rw [(hx.add hMpω).jumpProcess_sub hMmω, hx.jumpProcess_add hMpω, hjp, hjm]
    by_cases hs : σ ω = (t : WithTop ℝ≥0)
    · have heD : D ω = jumpProcess X t ω :=
        stoppedValueWithTerminal_jump_eq_of_eq_coe hs
      rw [if_pos hs, if_pos hs, ← heD]
      have he : D ω + -Cp ω - -Cm ω = 0 := by
        dsimp only [Cp, Cm]
        rcases le_total 0 (D ω) with hn | hn
        · rw [max_eq_left hn, max_eq_right (neg_nonpos.mpr hn)]
          ring
        · rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
          ring
      rw [he, norm_zero]
      exact hb
    · rw [if_neg hs, if_neg hs, add_zero, sub_zero]
      exact hω t ht (fun he ↦ hs he.symm)
  obtain ⟨A, Z, hAa, hAp, hAc, hA0, hAm, hAv, hAD, hMA, _, _, hiZ,
      hZbound, hZlim, hZL1⟩ :=
    hYs.exists_continuous_doob_decomposition_of_classD_of_jump_bound
      hYD hF hYc hYJ hY0 hb hYj
  have he : (Y + A) - Mp + Mm = X + A := by
    funext t ω
    change (X t ω + Mp t ω - Mm t ω + A t ω) - Mp t ω + Mm t ω = X t ω + A t ω
    ring
  have hM : Martingale (X + A) F P := by
    rw [← he]
    exact (hMA.sub hpM).add hmM
  have hcA : HasCadlagPaths A P :=
    Eventually.of_forall fun ω ↦ IsContinuousPath.isCadlagPath (hAc ω)
  exact ⟨A, Z, hAa, hAp, hAc, hA0, hAm, hAv, hAD, hM, hc.add hcA,
    (hXD.add hAD).uniformIntegrable, hiZ, hZbound, hZlim, hZL1⟩

end MeasureTheory

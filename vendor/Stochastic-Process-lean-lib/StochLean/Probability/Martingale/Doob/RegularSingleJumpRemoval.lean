/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularJumpRemoval
public import StochLean.Probability.Martingale.Doob.SingleJumpCompensator
public import StochLean.Probability.Martingale.Doob.RegularContinuousBoundedJumps
public import StochLean.Probability.Process.ClassD.Martingale

/-! # Regular continuous Doob construction with a bounded single-jump residual

The single-jump compensator is constructed from the original stopping time
and its integrable coefficient. Removing the resulting true UI martingale
preserves the supermartingale and Class D properties. Actual predictable
jump identities and a bounded residual give bounded jumps of the compensated
residual, without any total-inaccessibility or amplitude-selection premise.

The bounded-jump regular theorem constructs a continuous increasing part.
Adding back the true UI martingale gives the original process exactly the
same increasing part; the signed single-jump compensator is not added to it.
All sampled jumps are proved integrable before any integral subtraction.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}
  {D : Ω → ℝ} {C : ℝ}

/-- Actual single-jump compensation reduces a regular Class D process with a
bounded single-jump residual to the constructed bounded-jump regular theorem.
No compensator, local decomposition, terminal or convergence input is assumed. -/
theorem Supermartingale.exists_continuous_doob_of_regular_bounded_single_jump_residual
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (h0 : X 0 =ᵐ[P] 0) (hσ : IsStoppingTime F σ) (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    (hm : StronglyMeasurable[hσ.measurableSpace] D) (hi : Integrable D P)
    (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ‖X t ω - {v | σ v ≤ (t : WithTop ℝ≥0)}.indicator D ω‖ ≤ C) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      IsClassD A F P ∧ Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  classical
  let J : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D
  have haJ : Adapted F J := fun t ↦ (hm.indicator_stoppingTime_le hσ t).measurable
  have hcJ : HasCadlagPaths J P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le σ D)
  obtain ⟨B, hpB, hcB, hB0, hvB, _, hMJ⟩ :=
    hσ.exists_predictable_compensator_indicator hF hpos hm hi
  let M := J - B
  let Y := (X - J) + B
  have heY : Y = X - M := by
    funext t ω
    change X t ω - J t ω + B t ω = X t ω - (J t ω - B t ω)
    ring
  have hcM : HasCadlagPaths M P := hcJ.sub hcB
  have hMD : IsClassD M F P :=
    (hMJ.1.isClassD_iff_uniformIntegrable_of_usual hF hcM.hasRightContinuousPaths).mpr hMJ.2
  have hYs : Supermartingale Y F P := by
    rw [heY]
    exact hX.sub_martingale hMJ.1
  have hYD : IsClassD Y F P := by
    rw [heY]
    exact hXD.sub hMD
  have hYc : HasCadlagPaths Y P := (hc.sub hcJ).add hcB
  have hY0 : Y 0 =ᵐ[P] 0 := by
    filter_upwards [h0, hpos, hB0] with ω hx hp hbω
    have hz : J 0 ω = 0 := by
      apply indicator_of_notMem
      exact not_le_of_gt hp
    change X 0 ω - J 0 ω + B 0 ω = 0
    simp only [hx, hz, hbω, Pi.zero_apply, sub_zero, add_zero]
  have hYreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0 := by
    intro ρ hρ hp
    have hiX :=
      (hMJ.1.compensator_stopped_jump_eq_neg_condExp_of_regular_residual_bound
        hMJ.2 hF hX.stronglyAdapted.adapted haJ hc hcJ hcB hpB hvB hreg C hb hρ hp).1
    obtain ⟨hiM, hzM⟩ :=
      hMJ.1.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
        hMJ.2 hF hcM hρ hp
    have hEM : (∫ ω, stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) =
        0 := by
      rw [← integral_condExp hρ.1.measurableSpaceBefore_le_ambient]
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hzM
    have he : stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) ρ =ᵐ[P]
        stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ -
          stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) ρ := by
      rw [heY]
      filter_upwards [hc, hcM] with ω hx hmω
      by_cases ht : ρ ω = ⊤
      · simp only [stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
      · simp only [stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
        exact hx.jumpProcess_sub hmω (ρ ω).untopA
    rw [integral_congr_ae he]
    simp only [Pi.sub_apply]
    rw [integral_sub hiX hiM, hreg ρ hρ hp, hEM, sub_self]
  have hYj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess Y t ω‖ ≤ 4 * C :=
    (hMJ.1.ae_norm_jumps_compensator_and_removed_le_of_regular_residual_bound
      hMJ.2 hF hX.stronglyAdapted.adapted haJ hc hcJ hcB hpB hvB hreg C hC hb).mono
        fun _ hω t ht ↦ (hω t ht).2
  obtain ⟨A, Z, hAa, hAp, hAc, hA0, hAm, hAv, hAD, hMA, _, _, hiZ,
      hZbound, hZlim, hZL1⟩ :=
    hYs.exists_continuous_doob_of_classD_of_jump_bound_of_predictable_jump_mean_zero
      hYD hF hYc hYreg hY0 (mul_nonneg (by norm_num) hC) hYj
  have he : (Y + A) + M = X + A := by
    rw [heY]
    funext t ω
    change (X t ω - M t ω + A t ω) + M t ω = X t ω + A t ω
    ring
  have hM : Martingale (X + A) F P := by
    rw [← he]
    exact hMA.add hMJ.1
  have hcA : HasCadlagPaths A P :=
    (show HasContinuousPaths A P from Eventually.of_forall hAc).hasCadlagPaths
  exact ⟨A, Z, hAa, hAp, hAc, hA0, hAm, hAv, hAD, hM, hc.add hcA,
    (hXD.add hAD).uniformIntegrable, hiZ, hZbound, hZlim, hZL1⟩

end MeasureTheory

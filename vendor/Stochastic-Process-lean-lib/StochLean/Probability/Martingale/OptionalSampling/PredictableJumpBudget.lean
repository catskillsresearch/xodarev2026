/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpIntegrableTerminal
public import StochLean.Probability.Martingale.Doob.CenteredStepSeries
public import StochLean.Probability.Process.Stopping.JumpExitIntegrability
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # A deterministic predictable jump budget for UI martingales

The actual terminal of a UI cadlag martingale is constructed by the existing
whole-half-line limit theorem. At a positive predictable lifetime its actual
zero-terminal jump is the difference of two conditional expectations of that
terminal, in the stopped field and the before field. Multiplication by a
bounded before-measurable coefficient commutes with both expectations.

A common bound on every finite sum of coefficient norms therefore bounds
the sum of the expected weighted jump norms by twice that budget times the
terminal L1 norm. The coefficients need not be indexed chronologically, and
the lifetimes may coincide or be infinite. Infinite lifetimes use terminal
zero and never activate a closed step at a finite time.

The budget uses finite sums, not a totalized real `tsum` inequality that could
hold for a nonsummable family. The resulting integrability and summability
are proved before the existing centered-step series theorem is applied.
No boundedness or L2 assumption on the martingale, semimartingale witness,
or general local Yoeurp theorem is an input or a conclusion.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
  {τ : ℕ → Ω → WithTop ℝ≥0} {K : ℕ → Ω → ℝ}

private theorem stopped_jumpWithTerminal_ae_eq_condExp_sub
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsPredictableStoppingTime F σ P) (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    {Z : Ω → ℝ}
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ M t ω) atTop (𝓝 (Z ω))) :
    stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) σ =ᵐ[P]
      P[Z | hσ.1.measurableSpace] - P[Z | hσ.1.measurableSpaceBefore] := by
  have hV := hM.stoppedValueWithTerminal_ae_eq_condExp_terminal
    hu hF hc.hasRightContinuousPaths hlim hσ.1
  have hL := hM.stopped_leftLimitWithTerminal_ae_eq_condExp_before_of_predictable
    hu hF hc hσ hpos hlim
  have hL' : stoppedValueWithTerminal (leftLimitProcess M) Z σ =ᵐ[P]
      P[Z | hσ.1.measurableSpaceBefore] :=
    hL.trans ((condExp_congr_ae hV).trans
      (condExp_condExp_of_le hσ.1.measurableSpaceBefore_le hσ.1.measurableSpace_le))
  have he : stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) σ =
      stoppedValueWithTerminal M Z σ -
        stoppedValueWithTerminal (leftLimitProcess M) Z σ := by
    funext ω
    by_cases ht : σ ω = ⊤
    · simp only [stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
    · simp only [stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
      rfl
  rw [he]
  exact hV.sub hL'

/-- An actual UI terminal and a finite-partial-sum budget give integrable,
before-centered weighted jumps and a genuinely summable first-moment bound. -/
theorem exists_integrable_terminal_predictable_jump_budget
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 < τ n ω)
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n))
    (C : ℝ) (hbudget : ∀ᵐ ω ∂P, ∀ s : Finset ℕ, ∑ n ∈ s, ‖K n ω‖ ≤ C) :
    let L : ℕ → Ω → ℝ := fun n ↦
      K n * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (τ n)
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ M t ω) atTop (𝓝 (Z ω))) ∧
      (∀ t, M t =ᵐ[P] P[Z | F t]) ∧
      (∀ n, Integrable (L n) P) ∧
      (∀ n, P[L n | (hτ n).1.measurableSpaceBefore] =ᵐ[P] 0) ∧
      Summable (fun n ↦ ∫ ω, ‖L n ω‖ ∂P) ∧
      (∑' n, ∫ ω, ‖L n ω‖ ∂P) ≤ 2 * C * ∫ ω, ‖Z ω‖ ∂P := by
  classical
  let J : ℕ → Ω → ℝ := fun n ↦
    stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (τ n)
  let L : ℕ → Ω → ℝ := fun n ↦ K n * J n
  change ∃ Z : Ω → ℝ, Integrable Z P ∧ _
  obtain ⟨Z, hiZ, hlim, _, hclose⟩ :=
    hM.exists_integrable_limit_of_uniformIntegrable hc.hasRightContinuousPaths hu
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ‖K n ω‖ ≤ C := by
    filter_upwards [hbudget] with ω hω
    simpa only [Finset.sum_singleton] using hω {n}
  have hmK (n : ℕ) : AEStronglyMeasurable (K n) P :=
    ((hK n).mono (hτ n).1.measurableSpaceBefore_le_ambient).aestronglyMeasurable
  have hJ (n : ℕ) : Integrable (J n) P ∧
      P[J n | (hτ n).1.measurableSpaceBefore] =ᵐ[P] 0 :=
    hM.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
      hu hF hc (hτ n) (hpos n)
  have hiL (n : ℕ) : Integrable (L n) P :=
    (hJ n).1.bdd_mul (hmK n) (hb n)
  have hzL (n : ℕ) : P[L n | (hτ n).1.measurableSpaceBefore] =ᵐ[P] 0 := by
    have hp := condExp_mul_of_stronglyMeasurable_left (hK n) (hiL n) (hJ n).1
    filter_upwards [hp, (hJ n).2] with ω hpω hzω
    change P[L n | (hτ n).1.measurableSpaceBefore] ω = 0
    rw [hpω]
    change K n ω * P[J n | (hτ n).1.measurableSpaceBefore] ω = 0
    rw [hzω, Pi.zero_apply, mul_zero]
  have hiKZ (n : ℕ) : Integrable (K n * Z) P := hiZ.bdd_mul (hmK n) (hb n)
  have heL (n : ℕ) : L n =ᵐ[P]
      P[K n * Z | (hτ n).1.measurableSpace] -
        P[K n * Z | (hτ n).1.measurableSpaceBefore] := by
    have heJ := stopped_jumpWithTerminal_ae_eq_condExp_sub
      hM hu hF hc (hτ n) (hpos n) hlim
    have hps := condExp_mul_of_stronglyMeasurable_left
      ((hK n).mono (hτ n).1.measurableSpaceBefore_le) (hiKZ n) hiZ
    have hpb := condExp_mul_of_stronglyMeasurable_left (hK n) (hiKZ n) hiZ
    filter_upwards [heJ, hps, hpb] with ω hjω hsω hbω
    change K n ω * J n ω = _
    change J n ω = _ at hjω
    simp only [Pi.sub_apply, Pi.mul_apply] at hjω hsω hbω ⊢
    rw [hjω, hsω, hbω]
    ring
  have hnorm (n : ℕ) : (∫ ω, ‖L n ω‖ ∂P) ≤ 2 * ∫ ω, ‖K n ω * Z ω‖ ∂P := by
    let U := P[K n * Z | (hτ n).1.measurableSpace]
    let V := P[K n * Z | (hτ n).1.measurableSpaceBefore]
    have hiU : Integrable U P := integrable_condExp
    have hiV : Integrable V P := integrable_condExp
    calc
      _ = ∫ ω, ‖U ω - V ω‖ ∂P := by
        apply integral_congr_ae
        filter_upwards [heL n] with ω hω
        exact congrArg norm hω
      _ ≤ ∫ ω, ‖U ω‖ + ‖V ω‖ ∂P :=
        integral_mono (hiU.sub hiV).norm (hiU.norm.add hiV.norm) (fun _ ↦ norm_sub_le _ _)
      _ = (∫ ω, ‖U ω‖ ∂P) + ∫ ω, ‖V ω‖ ∂P := integral_add hiU.norm hiV.norm
      _ ≤ (∫ ω, ‖K n ω * Z ω‖ ∂P) + ∫ ω, ‖K n ω * Z ω‖ ∂P :=
        add_le_add (integral_norm_condExp_le (K n * Z))
          (integral_norm_condExp_le (K n * Z))
      _ = _ := by ring
  have hsum (s : Finset ℕ) : (∑ n ∈ s, ∫ ω, ‖L n ω‖ ∂P) ≤
      2 * C * ∫ ω, ‖Z ω‖ ∂P := by
    have his : Integrable (fun ω ↦ ∑ n ∈ s, ‖K n ω * Z ω‖) P :=
      integrable_finsetSum s (fun n _ ↦ (hiKZ n).norm)
    calc
      _ ≤ ∑ n ∈ s, 2 * ∫ ω, ‖K n ω * Z ω‖ ∂P :=
        Finset.sum_le_sum (fun n _ ↦ hnorm n)
      _ = 2 * ∫ ω, ∑ n ∈ s, ‖K n ω * Z ω‖ ∂P := by
        rw [integral_finsetSum (f := fun n ω ↦ ‖K n ω * Z ω‖) s
          (fun n _ ↦ (hiKZ n).norm), Finset.mul_sum]
      _ ≤ 2 * ∫ ω, C * ‖Z ω‖ ∂P := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply integral_mono_ae his (hiZ.norm.const_mul C)
        filter_upwards [hbudget] with ω hω
        simp only [norm_mul]
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hω s) (norm_nonneg _)
      _ = _ := by rw [integral_const_mul]; ring
  have hnonneg (n : ℕ) : 0 ≤ ∫ ω, ‖L n ω‖ ∂P :=
    integral_nonneg fun _ ↦ norm_nonneg _
  exact ⟨Z, hiZ, hlim, hclose, hiL, hzL,
    summable_of_sum_le hnonneg hsum, Real.tsum_le_of_sum_le hnonneg hsum⟩

/-- The original weighted closed-step series is a genuine UI martingale.
Its integrable coefficients and summability follow from the actual budget;
no summability, terminal, or semimartingale certificate is supplied. -/
theorem isUIMartingale_tsum_mul_stopped_jumpWithTerminal_of_predictable_budget
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 < τ n ω)
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n))
    (C : ℝ) (hbudget : ∀ᵐ ω ∂P, ∀ s : Finset ℕ, ∑ n ∈ s, ‖K n ω‖ ≤ C) :
    IsUIMartingale (fun (t : ℝ≥0) ω ↦ ∑' n,
      {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator
        (K n * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (τ n)) ω) F P := by
  let L : ℕ → Ω → ℝ := fun n ↦
    K n * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) (τ n)
  obtain ⟨_, _, _, _, hi, hz, hs, _⟩ :=
    hM.exists_integrable_terminal_predictable_jump_budget hu hF hc hτ hpos hK C hbudget
  apply isUIMartingale_tsum_indicator_lifetime_le (C := L) _ hi hs
  intro n
  have hm : StronglyMeasurable[(hτ n).1.measurableSpace] (L n) :=
    ((hK n).mono (hτ n).1.measurableSpaceBefore_le).mul
      (hM.stronglyAdapted.adapted.stronglyMeasurable_stopped_jump_of_usual hF hc (hτ n).1)
  exact isUIMartingale_indicator_stoppingTime_le_of_condExp_before_eq_zero
    (hτ n).1 hm (hi n) (hz n)

end MeasureTheory.Martingale

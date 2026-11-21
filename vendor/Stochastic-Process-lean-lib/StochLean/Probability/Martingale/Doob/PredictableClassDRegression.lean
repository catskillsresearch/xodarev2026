/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableClassD
public import StochLean.Probability.Martingale.Doob.PredictableUniqueness
public import StochLean.Probability.Martingale.Doob.SingleJump
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping

/-! # General predictable Class D Doob construction with a random initial value

An arbitrary signed integrable initial-measurable random value is followed by
one nonnegative integrable initial-measurable downward jump at time one.
Neither random variable has a deterministic bound. The general existence
theorem constructs the compensator; predictable FV local-martingale
uniqueness identifies it with the actual positive lifetime step. The true UI
martingale part retains the original signed initial random value.

The unit-amplitude case has mean jump `-1` at the predictable time one.
Thus the example is outside the regular and totally-inaccessible-jump
subdomains; it tests the genuinely general predictable construction.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.PredictableClassDRegression

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {V K : Ω → ℝ}

/-- Actual general existence followed by predictable FV uniqueness, with an
unbounded integrable random jump and an arbitrary signed integrable initial
value. No candidate decomposition is an assumption. -/
theorem exists_actual_compensator_random_initial_and_integrable_jump
    (hF : F.IsUsual P) (hmV : StronglyMeasurable[F 0] V) (hiV : Integrable V P)
    (hmK : StronglyMeasurable[F 0] K) (hiK : Integrable K P)
    (hnK : ∀ᵐ ω ∂P, 0 ≤ K ω) :
    let B : ℝ≥0 → Ω → ℝ := fun t ↦
      {_ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator K
    let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ V ω - B t ω
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasIntegrableVariation A P ∧ IsClassD A F P ∧
      IsUIMartingale (X + A) F P ∧ Indistinguishable A B P ∧
      Indistinguishable (X + A) (fun _ ↦ V) P := by
  classical
  intro B X
  let τ : Ω → WithTop ℝ≥0 := fun _ ↦ ((1 : ℝ≥0) : WithTop ℝ≥0)
  have hτ : IsPredictableStoppingTime F τ P := isPredictableStoppingTime_const F P 1
  have hmKb : StronglyMeasurable[hτ.1.measurableSpaceBefore] K :=
    hmK.mono hτ.1.le_measurableSpaceBefore
  have hmKs : StronglyMeasurable[hτ.1.measurableSpace] K :=
    hmKb.mono hτ.1.measurableSpaceBefore_le
  have hpB : IsStronglyPredictable F B :=
    hmKb.isStronglyPredictable_indicator_stoppingTime_le hτ hF.complete_initial
  have hcB : HasCadlagPaths B P :=
    Eventually.of_forall fun ω ↦ isCadlagPath_indicator_lifetime_le τ K ω
  have hB0 : B 0 = 0 := by
    funext ω
    change {ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator K ω = 0
    apply indicator_of_notMem
    intro hh
    exact not_le_of_gt (show (0 : ℝ≥0) < 1 from zero_lt_one) (WithTop.coe_le_coe.mp hh)
  have hmB : HasMonotonePaths B P := by
    filter_upwards [hnK] with ω hω s t hst
    change {ω | τ ω ≤ (s : WithTop ℝ≥0)}.indicator K ω ≤
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator K ω
    by_cases hs : τ ω ≤ (s : WithTop ℝ≥0)
    · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
      simp only [indicator_apply, mem_ofPred_eq, hs, ht, if_true, le_refl]
    · simp only [indicator_apply, mem_ofPred_eq, hs, if_false]
      split_ifs
      · exact hω
      · exact le_rfl
  have hBD : IsClassD B F P := isClassD_indicator_stoppingTime_le hτ.1 hmKs hiK
  have hVc : HasContinuousPaths (fun _ : ℝ≥0 ↦ V) P :=
    Eventually.of_forall fun _ ↦ continuous_const
  have hVM : Martingale (fun _ : ℝ≥0 ↦ V) F P := martingale_const_fun F P hmV hiV
  have hcX : HasCadlagPaths X P := hVc.hasCadlagPaths.sub hcB
  have hXD : IsClassD X F P := (isClassD_const (F := F) hiV).sub hBD
  have haX : StronglyAdapted F X := hVM.stronglyAdapted.sub hpB.stronglyAdapted
  have hX : Supermartingale X F P := by
    refine ⟨haX, ?_, hXD.integrable⟩
    intro s t hst
    have hle : X t ≤ᵐ[P] X s := by
      filter_upwards [hmB] with ω hω
      exact sub_le_sub_left (hω hst) (V ω)
    have he := condExp_mono (hXD.integrable t) (hXD.integrable s) hle (m := F s)
    rwa [condExp_of_stronglyMeasurable (F.le s) (haX s) (hXD.integrable s)] at he
  obtain ⟨A, _, hpA, hcA, hA0, hmA, hvA, hAD, hMA, hcMA, _, _, _, _⟩ :=
    hX.exists_predictable_doob_of_classD hXD hF hcX
  have heMB : X + B = fun _ : ℝ≥0 ↦ V := by
    funext t ω
    exact sub_add_cancel (V ω) (B t ω)
  have hMB : Martingale (X + B) F P := heMB.symm ▸ hVM
  have hcMB : HasCadlagPaths (X + B) P := heMB.symm ▸ hVc.hasCadlagPaths
  have h0 : A 0 =ᵐ[P] B 0 := by
    filter_upwards with ω
    rw [hA0, hB0]
  have hAB := indistinguishable_of_predictable_finiteVariation_localMartingale_add hF
    (hMA.1.isLocalMartingale hcMA) (hMB.isLocalMartingale hcMB) hpA hpB
    hvA.hasFiniteVariationPaths hmB.hasFiniteVariationPaths h0
  refine ⟨A, hpA, hcA, hA0, hmA, hvA, hAD, hMA, hAB, ?_⟩
  filter_upwards [hAB] with ω hω t
  change V ω - B t ω + A t ω = V ω
  rw [hω t, sub_add_cancel]

/-- The deterministic unit downward jump has a nonzero predictable mean
jump, and cannot belong to the totally-inaccessible-jump subdomain. -/
theorem unit_downward_step_has_nonzero_predictable_mean_jump
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [IsProbabilityMeasure P] :
    let X : ℝ≥0 → Ω → ℝ := fun t _ ↦ if (1 : ℝ≥0) ≤ t then -1 else 0
    let τ : Ω → WithTop ℝ≥0 := fun _ ↦ ((1 : ℝ≥0) : WithTop ℝ≥0)
    IsPredictableStoppingTime F τ P ∧ (∀ ω, 0 < τ ω) ∧
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω ∂P) = -1 ∧
      ¬ HasTotallyInaccessibleJumps F X P := by
  intro X τ
  have hj (ω : Ω) : jumpProcess X 1 ω = -1 := by
    change jumpProcess (fun t _ ↦ if (1 : ℝ≥0) ≤ t then (-1 : ℝ) else 0) 1 ω = -1
    rw [jumpProcess_step_Ici, if_pos rfl]
  have he : stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ =
      fun _ ↦ (-1 : ℝ) := by
    funext ω
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe (show τ ω = (1 : WithTop ℝ≥0) from rfl)]
    exact hj ω
  have hmean :
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω ∂P) = -1 := by
    rw [he]
    simp
  refine ⟨isPredictableStoppingTime_const F P 1,
    fun _ ↦ WithTop.coe_lt_coe.mpr (show (0 : ℝ≥0) < 1 from zero_lt_one), hmean, ?_⟩
  intro hTI
  have hz := hTI.ae_jumpProcess_eq_zero (show (0 : ℝ≥0) < 1 from zero_lt_one)
  have hez : stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ =ᵐ[P]
      fun _ ↦ (0 : ℝ) := by
    filter_upwards [hz] with ω hω
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe (show τ ω = (1 : WithTop ℝ≥0) from rfl)]
    exact hω
  rw [integral_congr_ae hez] at hmean
  norm_num at hmean

end ProbabilityTheory.PredictableClassDRegression

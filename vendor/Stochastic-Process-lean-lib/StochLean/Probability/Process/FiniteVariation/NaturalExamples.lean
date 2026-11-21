/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra
public import StochLean.Probability.Process.Path.LifetimeStepJump
public import StochLean.Probability.Process.Stopping.AnnouncingExamples
public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpMultiplier

/-! # Discontinuous natural processes

A deterministic step at a strictly positive time is natural. Its actual raw
bracket with a bounded cadlag martingale is the corresponding single weighted
martingale jump, activated at the same time. Predictable stopping gives zero
mean of this actual integrable jump, so the naturality terminal is constructed
directly, without Yoeurp's theorem or a bracket-martingale premise.

The step is the existing `step_Ici` expression; no process, variation, bracket,
or terminal owner is introduced. Positive activation time is essential for
zero initial value. Taking time and amplitude equal to one proves that
naturality does not imply path continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- A deterministic step has integrable actual total variation. Its time
may be zero here; the separate naturality theorem requires positive time. -/
theorem hasIntegrableVariation_step_Ici (T : ℝ≥0) (c : ℝ) :
    HasIntegrableVariation (fun t (_ : Ω) ↦ if T ≤ t then c else 0) P := by
  have hm : Monotone (fun t : ℝ≥0 ↦ if T ≤ t then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hs : T ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      split_ifs <;> norm_num
  have hu : HasIntegrableVariation
      (fun t (_ : Ω) ↦ if T ≤ t then (1 : ℝ) else 0) P := by
    constructor
    · exact ae_of_all _ fun _ ↦ (hm.monotoneOn univ).boundedVariationOn
        (C := 1) (fun t _ ↦ by
          change |if T ≤ t then (1 : ℝ) else 0| ≤ 1
          split_ifs <;> norm_num)
    · exact integrable_const _
  have he : (fun t (_ : Ω) ↦ c * (if T ≤ t then (1 : ℝ) else 0)) =
      (fun t (_ : Ω) ↦ if T ≤ t then c else 0) := by
    funext t ω
    split_ifs <;> simp only [mul_one, mul_zero]
  simpa only [he] using hu.const_mul c

/-- The existing raw bracket with a positive-time deterministic step is
exactly its single weighted martingale jump. The identity itself needs only
the semimartingale property, not martingality of the first process. -/
theorem IsSemimartingale.quadraticCovariation_step_Ici
    (hM : IsSemimartingale M F P) (T : ℝ≥0) (hT : 0 < T) (c : ℝ)
    (hA : IsSemimartingale (fun t (_ : Ω) ↦ if T ≤ t then c else 0) F P)
    (hF : F.IsUsual P) :
    Indistinguishable (hM.quadraticCovariation hA hF)
      (fun t ω ↦ if T ≤ t then c * jumpProcess M T ω else 0) P := by
  classical
  have hv := (hasIntegrableVariation_step_Ici (P := P) T c).hasFiniteVariationPaths
  filter_upwards [hM.quadraticCovariation_of_finiteVariation_right hA hF hv]
    with ω hω t
  rw [hω t]
  simp only [if_neg (not_le_of_gt hT), mul_zero, zero_add]
  by_cases hTt : T ≤ t
  · rw [if_pos hTt, tsum_eq_single (⟨T, hT, hTt⟩ : Ioc 0 t)]
    · simp only [jumpProcess_step_Ici, if_true]
      exact mul_comm _ _
    · intro s hs
      have hne : T ≠ (s : ℝ≥0) := fun he ↦ hs (Subtype.ext he.symm)
      simp only [jumpProcess_step_Ici, if_neg hne, mul_zero]
  · rw [if_neg hTt]
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        have hne : T ≠ (s : ℝ≥0) := fun he ↦ hTt (he.trans_le s.property.2)
        simp only [jumpProcess_step_Ici, if_neg hne, mul_zero]
      _ = 0 := tsum_zero

/-- A deterministic positive-time step is natural, including either sign
of its amplitude. The tested terminal is the actual weighted jump. -/
theorem isNatural_step_Ici (hF : F.IsUsual P) (T : ℝ≥0) (hT : 0 < T) (c : ℝ) :
    IsNatural (fun t (_ : Ω) ↦ if T ≤ t then c else 0) F P hF := by
  have hv := hasIntegrableVariation_step_Ici (P := P) T c
  have ha : Adapted F (fun t (_ : Ω) ↦ if T ≤ t then c else 0) :=
    fun _ ↦ measurable_const
  have hc : HasCadlagPaths (fun t (_ : Ω) ↦ if T ≤ t then c else 0) P :=
    ae_of_all _ fun _ ↦ isCadlagPath_step_Ici T c
  refine ⟨ha, hc, hv, ae_of_all _ (fun _ ↦ if_neg (not_le_of_gt hT)), ?_⟩
  intro M hM hcM C _hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSA := hv.hasFiniteVariationPaths.isSemimartingale ha hF hc
  have hp := isPredictableStoppingTime_const F P T
  have hpos : ∀ᵐ ω ∂P, (0 : WithTop ℝ≥0) < (T : WithTop ℝ≥0) :=
    ae_of_all _ fun _ ↦ WithTop.coe_lt_coe.mpr hT
  have hi : Integrable (fun ω ↦ c * jumpProcess M T ω) P := by
    have hiJ : Integrable (jumpProcess M T) P := by
      simpa only [stoppedValue_const] using
        hM.integrable_stopped_jump_of_predictable_of_bounded
          hF hcM hp hpos (fun _ ↦ le_rfl)
    exact hiJ.const_mul c
  have he : (∫ ω, c * jumpProcess M T ω ∂P) = 0 := by
    simpa only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] using
      hM.integral_mul_stopped_jump_eq_zero_of_predictable_of_bounded
        hF hcM hp hpos (fun _ ↦ le_rfl) (K := fun _ : Ω ↦ c)
        stronglyMeasurable_const ‖c‖ (ae_of_all _ fun _ ↦ le_rfl)
  refine ⟨fun ω ↦ c * jumpProcess M T ω, hi, ?_, he⟩
  filter_upwards [hSM.quadraticCovariation_step_Ici T hT c hSA hF] with ω hω
  apply tendsto_atTop_of_eventually_const (i₀ := T)
  intro t ht
  exact (hω t).trans (if_pos ht)

omit [IsFiniteMeasure P] in
/-- On a probability space a nonzero positive-time deterministic step
cannot have continuous paths. Its exact positive-time jump gives the contradiction. -/
theorem not_hasContinuousPaths_step_Ici [IsProbabilityMeasure P]
    (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : c ≠ 0) :
    ¬ HasContinuousPaths (fun t (_ : Ω) ↦ if T ≤ t then c else 0) P := by
  intro h
  obtain ⟨ω, hω⟩ := h.exists
  have hz := IsContinuousPath.jumpProcess_eq_zero
    (X := fun t (_ : Ω) ↦ if T ≤ t then c else 0) (ω := ω) hω hT.ne'
  have hj := jumpProcess_step_Ici T (fun _ : Ω ↦ c) T ω
  exact hc (by simpa only [if_true] using hj.symm.trans hz)

/-- Naturality does not imply continuity: the deterministic upward unit
jump at time one is a genuine natural process. -/
theorem exists_isNatural_not_hasContinuousPaths [IsProbabilityMeasure P]
    (hF : F.IsUsual P) :
    ∃ A : ℝ≥0 → Ω → ℝ, IsNatural A F P hF ∧ ¬ HasContinuousPaths A P :=
  ⟨fun t (_ : Ω) ↦ if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0,
    isNatural_step_Ici hF 1 (by norm_num) 1,
    not_hasContinuousPaths_step_Ici 1 (by norm_num) 1 one_ne_zero⟩

end ProbabilityTheory

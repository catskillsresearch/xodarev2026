/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobCountableLp
public import StochLean.Probability.Process.Path.SupremumGlobal

/-! # Doob's Lp maximal inequality on the whole time half-line

Protter I.20 is proved for nonnegative submartingales and every real `p > 1`.
The actual supremum over all times is an extended nonnegative random variable.
Right continuity identifies it almost surely with a measurable countable
supremum. Finiteness is a consequence when the uniform coordinate bound is finite.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {p : ℝ}

theorem Submartingale.eLpNorm_iSup_ofReal_le (hX : Submartingale X F P)
    (hn : ∀ t ω, 0 ≤ X t ω) (hr : HasRightContinuousPaths X P) (hp : 1 < p) :
    eLpNorm (fun ω ↦ ⨆ t, ENNReal.ofReal (X t ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p / (p - 1)) * ⨆ t, eLpNorm (X t) (ENNReal.ofReal p) P := by
  have he : (fun ω ↦ ⨆ t, ENNReal.ofReal (X t ω)) =ᵐ[P]
      (fun ω ↦ ⨆ n, ENNReal.ofReal (X (TopologicalSpace.denseSeq ℝ≥0 n) ω)) := by
    filter_upwards [hr] with ω hω
    exact iSup_ofReal_eq_iSup_denseSeq_of_rightContinuous hω
  rw [eLpNorm_congr_ae he]
  exact hX.eLpNorm_iSup_sample_le hn hp _

/-- Coordinatewise almost-sure positivity is sufficient; there is no
uncountable intersection of coordinate positivity events. -/
theorem Submartingale.eLpNorm_iSup_ofReal_le_of_ae_nonneg
    (hX : Submartingale X F P) (hn : ∀ t, ∀ᵐ ω ∂P, 0 ≤ X t ω)
    (hr : HasRightContinuousPaths X P) (hp : 1 < p) :
    eLpNorm (fun ω ↦ ⨆ t, ENNReal.ofReal (X t ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p / (p - 1)) * ⨆ t, eLpNorm (X t) (ENNReal.ofReal p) P := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ max (X t ω) 0
  have hY : Submartingale Y F P := hX.sup (martingale_const F P (0 : ℝ)).submartingale
  have hyr : HasRightContinuousPaths Y P := by
    filter_upwards [hr] with ω hω t
    exact (hω t).max continuousWithinAt_const
  have he (t : ℝ≥0) : eLpNorm (Y t) (ENNReal.ofReal p) P =
      eLpNorm (X t) (ENNReal.ofReal p) P :=
    eLpNorm_congr_ae ((hn t).mono fun ω hω ↦ max_eq_left hω)
  have h := hY.eLpNorm_iSup_ofReal_le (fun _ _ ↦ le_max_right _ _) hyr hp
  have hz (z : ℝ≥0∞) : max z 0 = z := max_eq_left bot_le
  simpa only [he, Y, ENNReal.ofReal_max, ENNReal.ofReal_zero, hz] using h

/-- A measurable real envelope attaining the actual extended supremum almost
surely. The all-time bound holds on one event, not separately at each time. -/
theorem Submartingale.exists_memLp_globalEnvelope (hX : Submartingale X F P)
    (hn : ∀ t ω, 0 ≤ X t ω) (hr : HasRightContinuousPaths X P) (hp : 1 < p)
    {C : ℝ≥0∞} (hC : C < ∞) (hb : ∀ t, eLpNorm (X t) (ENNReal.ofReal p) P ≤ C) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g (ENNReal.ofReal p) P ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (g ω) = ⨆ t, ENNReal.ofReal (X t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t, X t ω ≤ g ω) ∧
      eLpNorm g (ENNReal.ofReal p) P ≤ ENNReal.ofReal (p / (p - 1)) * C := by
  let A (ω : Ω) := ⨆ n, ENNReal.ofReal (X (TopologicalSpace.denseSeq ℝ≥0 n) ω)
  have hm : Measurable A := Measurable.iSup fun n ↦ ENNReal.measurable_ofReal.comp
    ((hX.stronglyMeasurable _).measurable.mono (F.le _) le_rfl)
  have hA : eLpNorm A (ENNReal.ofReal p) P ≤ ENNReal.ofReal (p / (p - 1)) * C :=
    (hX.eLpNorm_iSup_sample_le hn hp _).trans (mul_le_mul le_rfl (iSup_le hb) bot_le bot_le)
  have hAf : eLpNorm A (ENNReal.ofReal p) P < ∞ :=
    hA.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC)
  have hf : ∀ᵐ ω ∂P, A ω < ∞ :=
    ae_lt_top_of_eLpNorm_lt_top_ennreal hm.aemeasurable (zero_lt_one.trans hp) hAf
  have he : eLpNorm (fun ω ↦ (A ω).toReal) (ENNReal.ofReal p) P =
      eLpNorm A (ENNReal.ofReal p) P := by
    apply eLpNorm_congr_enorm_ae
    filter_upwards [hf] with ω hω
    exact Real.enorm_toReal hω.ne
  refine ⟨fun ω ↦ (A ω).toReal, hm.ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg,
    ⟨hm.ennreal_toReal.aestronglyMeasurable, he.trans_lt hAf⟩, ?_, ?_, he.trans_le hA⟩
  · filter_upwards [hf, hr] with ω hfω hrω
    rw [ENNReal.ofReal_toReal hfω.ne]
    exact (iSup_ofReal_eq_iSup_denseSeq_of_rightContinuous hrω).symm
  · filter_upwards [hf, hr] with ω hfω hrω t
    apply (ENNReal.ofReal_le_iff_le_toReal hfω.ne).mp
    dsimp only [A]
    rw [← iSup_ofReal_eq_iSup_denseSeq_of_rightContinuous hrω]
    exact le_iSup (fun t ↦ ENNReal.ofReal (X t ω)) t

theorem Martingale.eLpNorm_iSup_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : ℝ≥0 → Ω → E} (hM : Martingale M F P)
    (hr : HasRightContinuousPaths M P) (hp : 1 < p) :
    eLpNorm (fun ω ↦ ⨆ t, ENNReal.ofReal ‖M t ω‖) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p / (p - 1)) * ⨆ t, eLpNorm (M t) (ENNReal.ofReal p) P := by
  have hnr : HasRightContinuousPaths (fun t ω ↦ ‖M t ω‖) P := by
    filter_upwards [hr] with ω hω t
    exact (hω t).norm
  simpa only [eLpNorm_norm] using
    hM.norm_submartingale.eLpNorm_iSup_ofReal_le (fun _ _ ↦ norm_nonneg _) hnr hp

end MeasureTheory

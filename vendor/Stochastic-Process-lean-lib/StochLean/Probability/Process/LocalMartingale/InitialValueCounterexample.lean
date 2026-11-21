/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.NormNum

/-!
# An explicit integrable but not square-integrable initial value

On `(0,1)` with Lebesgue probability, `Z(x) = x^(-1/2)` is in L1 but not L2.
The ambient sample type is real; values outside `(0,1)` have measure zero.
The filtration reveals the sample at time zero. This supplies the concrete
counterexample required by the Klenke 21.67, 21.70 and 21.73 source safeguards.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace StochLean.InitialValueCounterexample

noncomputable def sampleMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure sampleMeasure := by
  constructor
  simp [sampleMeasure, Real.volume_Ioo]

def fullFiltration : Filtration ℝ≥0 (borel ℝ) := Filtration.const ℝ≥0 (borel ℝ) le_rfl

noncomputable def initialValue (x : ℝ) : ℝ := x ^ (-1 / 2 : ℝ)

theorem measurable_initialValue : Measurable initialValue := by
  exact measurable_id.pow_const _

theorem integrable_initialValue : Integrable initialValue sampleMeasure := by
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mpr
    (by norm_num : (-1 : ℝ) < -1 / 2)

theorem not_integrable_square : ¬ Integrable (fun x ↦ initialValue x ^ 2) sampleMeasure := by
  intro h
  have heq : (fun x ↦ initialValue x ^ 2) =ᵐ[sampleMeasure] fun x : ℝ ↦ x ^ (-1 : ℝ) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with x hx
    dsimp [initialValue]
    rw [← Real.rpow_mul_natCast hx.1.le]
    norm_num
  have hi : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo 0 1) := h.congr heq
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hi
  norm_num at this

theorem not_memLp_two : ¬ MemLp initialValue 2 sampleMeasure := by
  intro h
  exact not_integrable_square ((memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h)

theorem unbounded_initialValue : ∀ C : ℝ, ∃ x, C < |initialValue x| := by
  intro C
  by_contra h
  push Not at h
  have hlp : MemLp initialValue 2 sampleMeasure :=
    MemLp.of_bound measurable_initialValue.aestronglyMeasurable C
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using h x)
  exact not_memLp_two hlp

theorem constant_isContinuousLocalMartingale :
    IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ initialValue) fullFiltration sampleMeasure :=
  isContinuousLocalMartingale_const_initial measurable_initialValue

/-- R33: the constant process has an unmasked Klenke witness. -/
theorem constant_has_klenkeLocalizer :
    ∃ τ, IsKlenkeLocalizingSequence (fun _ : ℝ≥0 ↦ initialValue) fullFiltration sampleMeasure τ :=
  constant_isContinuousLocalMartingale.1.exists_klenkeLocalizingSequence integrable_initialValue

/-- R33: its square cannot have an unmasked Klenke witness, despite zero increment QV. -/
theorem constant_square_has_no_klenkeLocalizer :
    ¬ ∃ τ, IsKlenkeLocalizingSequence (fun _ : ℝ≥0 ↦ fun x ↦ initialValue x ^ 2)
      fullFiltration sampleMeasure τ :=
  not_exists_klenkeLocalizingSequence_const_sq not_integrable_square

/-- The canonical Protter mask does allow the square of the same constant process. -/
theorem constant_square_isContinuousLocalMartingale :
    IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ fun x ↦ initialValue x ^ 2)
      fullFiltration sampleMeasure :=
  isContinuousLocalMartingale_const_initial (measurable_initialValue.pow_const 2)

/-- R34: no choice of stopping time can bound this unbounded integrable initial value. -/
theorem no_bounded_stopping (τ : ℝ → WithTop ℝ≥0) :
    ¬ ∃ C : ℝ, ∀ t x, |stoppedProcess (fun _ : ℝ≥0 ↦ initialValue) τ t x| ≤ C :=
  not_bounded_stoppedProcess_of_unbounded_initial unbounded_initialValue τ

/-- The product-initial-value issue in 21.73 already occurs with two copies of this example. -/
theorem not_integrable_product :
    ¬ Integrable (fun x ↦ initialValue x * initialValue x) sampleMeasure := by
  simpa only [← pow_two] using not_integrable_square

end StochLean.InitialValueCounterexample

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Bounded convergence in measure gives second-moment convergence

For an arbitrary index filter on a finite measure space, a uniform almost-sure
bound and convergence in measure to zero imply convergence of the squared
integrals to zero. The proof splits at a fixed positive norm threshold, then
lets the threshold shrink. It does not assume almost-everywhere convergence
or pass through a chosen almost-everywhere convergent subsequence.
-/

@[expose] public section

open Filter Set
open scoped Topology ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

private theorem integral_sq_le_threshold_tail {f : Ω → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hbound : ∀ᵐ ω ∂P, ‖f ω‖ ≤ C) :
    (∫ ω, f ω ^ 2 ∂P) ≤
      a ^ 2 * P.real univ + C ^ 2 * P.real {ω | a ≤ ‖f ω‖} := by
  let A : Set Ω := {ω | a ≤ ‖f ω‖}
  have hA : MeasurableSet A := measurableSet_le measurable_const hf.norm
  have hi : Integrable (fun ω ↦ f ω ^ 2) P :=
    (MemLp.of_bound hf.aestronglyMeasurable C hbound (p := 2)).integrable_sq
  have hI : Integrable (fun ω ↦ a ^ 2 + A.indicator (fun _ ↦ C ^ 2) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hA)
  have hle : (∫ ω, f ω ^ 2 ∂P) ≤
      ∫ ω, a ^ 2 + A.indicator (fun _ ↦ C ^ 2) ω ∂P := by
    apply integral_mono_ae hi hI
    filter_upwards [hbound] with ω hω
    have hsqC : f ω ^ 2 ≤ C ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (norm_nonneg _) hC).mpr hω
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA]
      exact hsqC.trans (le_add_of_nonneg_left (sq_nonneg a))
    · rw [indicator_of_notMem hωA, add_zero]
      have hsmall : ‖f ω‖ ≤ a := (lt_of_not_ge hωA).le
      simpa only [Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (norm_nonneg _) ha).mpr hsmall
  have he : (∫ ω, a ^ 2 + A.indicator (fun _ ↦ C ^ 2) ω ∂P) =
      a ^ 2 * P.real univ + C ^ 2 * P.real A := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hA),
      integral_indicator hA]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    ring
  exact hle.trans_eq he

theorem TendstoInMeasure.tendsto_integral_sq_of_measurable_of_bound
    {f : ι → Ω → ℝ} {l : Filter ι} (hlim : TendstoInMeasure P f l (0 : Ω → ℝ))
    (hf : ∀ i, Measurable (f i)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖f i ω‖ ≤ C) :
    Tendsto (fun i ↦ ∫ ω, f i ω ^ 2 ∂P) l (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun i ↦ ha.trans_le (integral_nonneg fun _ ↦ sq_nonneg _)
  · intro ε hε
    let a : ℝ := min 1 (ε / (4 * (P.real univ + 1)))
    have hm : 0 ≤ P.real univ := measureReal_nonneg
    have hden : 0 < 4 * (P.real univ + 1) := by positivity
    have ha : 0 < a := lt_min zero_lt_one (div_pos hε hden)
    have ha1 : a ≤ 1 := min_le_left _ _
    have hascale : a * (4 * (P.real univ + 1)) ≤ ε :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have hasq : a ^ 2 ≤ a := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left ha1 ha.le
    have hsmall : a ^ 2 * P.real univ < ε / 2 := by
      have hprod := mul_le_mul_of_nonneg_right hasq hm
      nlinarith only [hprod, hascale, hε, ha.le]
    have htail : Tendsto (fun i ↦ P.real {ω | a ≤ ‖f i ω‖}) l (𝓝 0) := by
      simpa only [Pi.zero_apply, sub_zero] using
        (tendstoInMeasure_iff_measureReal_norm.mp hlim) a ha
    have hscaled : Tendsto (fun i ↦ C ^ 2 * P.real {ω | a ≤ ‖f i ω‖}) l (𝓝 0) := by
      simpa only [mul_zero] using htail.const_mul (C ^ 2)
    filter_upwards [hscaled.eventually_lt_const (half_pos hε)] with i hi
    have hsplit := integral_sq_le_threshold_tail (hf i) hC ha.le (hbound i)
    linarith only [hsplit, hsmall, hi]

theorem TendstoInMeasure.tendsto_integral_sq_of_bound
    {f : ι → Ω → ℝ} {l : Filter ι} (hlim : TendstoInMeasure P f l (0 : Ω → ℝ))
    (hf : ∀ i, AEStronglyMeasurable (f i) P) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖f i ω‖ ≤ C) :
    Tendsto (fun i ↦ ∫ ω, f i ω ^ 2 ∂P) l (𝓝 0) := by
  let g : ι → Ω → ℝ := fun i ↦ (hf i).mk (f i)
  have hgm (i : ι) : Measurable (g i) := (hf i).stronglyMeasurable_mk.measurable
  have hfg (i : ι) : f i =ᵐ[P] g i := (hf i).ae_eq_mk
  have hgb (i : ι) : ∀ᵐ ω ∂P, ‖g i ω‖ ≤ C := by
    filter_upwards [hfg i, hbound i] with ω he hω
    rw [← he]
    exact hω
  have hg := (hlim.congr hfg EventuallyEq.rfl).tendsto_integral_sq_of_measurable_of_bound hgm hC hgb
  apply hg.congr'
  exact Eventually.of_forall fun i ↦ (integral_congr_ae ((hfg i).pow_const 2)).symm

theorem TendstoInMeasure.tendsto_eLpNorm_two_of_bound
    {f : ι → Ω → ℝ} {l : Filter ι} (hlim : TendstoInMeasure P f l (0 : Ω → ℝ))
    (hf : ∀ i, AEStronglyMeasurable (f i) P) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖f i ω‖ ≤ C) :
    Tendsto (fun i ↦ eLpNorm (f i) 2 P) l (𝓝 0) := by
  have hi (i : ι) : MemLp (f i) 2 P := MemLp.of_bound (hf i) C (hbound i)
  have he (i : ι) : eLpNorm (f i) 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, f i ω ^ 2 ∂P)) := by
    have h := (hi i).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Real.sqrt_eq_rpow, one_div] using h
  have hsq := hlim.tendsto_integral_sq_of_bound hf hC hbound
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsq.sqrt
  simpa only [he, Real.sqrt_zero, ENNReal.ofReal_zero, Function.comp_def] using h

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Stieltjes
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Finite-horizon integration against a locally BV path

The increment integral on `(s,t]` is the difference of integrals against the
canonical positive and negative Stieltjes components. Integrability is measured
against their sum, the total-variation measure. The source integral from time
zero additionally contains `f 0 * x 0`; this is not a measure atom.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

variable (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

theorem positiveVariationStieltjes_measure_le :
    (positiveVariationStieltjes x hx hr).measure ≤ (totalVariationStieltjes x hx hr).measure := by
  rw [totalVariationStieltjes_measure_eq_add]
  exact Measure.le_add_right le_rfl

theorem negativeVariationStieltjes_measure_le :
    (negativeVariationStieltjes x hx hr).measure ≤ (totalVariationStieltjes x hx hr).measure := by
  rw [totalVariationStieltjes_measure_eq_add]
  exact Measure.le_add_left le_rfl

noncomputable def pathStieltjesIncrementIntegral (f : ℝ≥0 → ℝ) (s t : ℝ≥0) : ℝ :=
  (∫ u in Ioc s t, f u ∂(positiveVariationStieltjes x hx hr).measure) -
    ∫ u in Ioc s t, f u ∂(negativeVariationStieltjes x hx hr).measure

noncomputable def pathStieltjesIntegral (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f 0 * x 0 + pathStieltjesIncrementIntegral x hx hr f 0 t

variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

theorem integrableOn_positiveVariationStieltjes
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    IntegrableOn f (Ioc s t) (positiveVariationStieltjes x hx hr).measure :=
  hf.mono_measure (positiveVariationStieltjes_measure_le x hx hr)

theorem integrableOn_negativeVariationStieltjes
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    IntegrableOn f (Ioc s t) (negativeVariationStieltjes x hx hr).measure :=
  hf.mono_measure (negativeVariationStieltjes_measure_le x hx hr)

theorem integrableOn_variationStieltjes_of_bounded (hf : Measurable f) {C : ℝ}
    (hC : ∀ u ∈ Ioc s t, ‖f u‖ ≤ C) :
    IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure :=
  .of_bound measure_Ioc_lt_top hf.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦ hC u hu)

@[simp] theorem pathStieltjesIncrementIntegral_self (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathStieltjesIncrementIntegral x hx hr f t t = 0 := by
  simp [pathStieltjesIncrementIntegral]

@[simp] theorem pathStieltjesIntegral_zero (f : ℝ≥0 → ℝ) :
    pathStieltjesIntegral x hx hr f 0 = f 0 * x 0 := by
  simp [pathStieltjesIntegral]

theorem pathStieltjesIncrementIntegral_const (c : ℝ) (hst : s ≤ t) :
    pathStieltjesIncrementIntegral x hx hr (fun _ ↦ c) s t = c * (x t - x s) := by
  simp only [pathStieltjesIncrementIntegral, setIntegral_const, smul_eq_mul, measureReal_def]
  rw [← sub_mul, variationStieltjes_measure_Ioc_sub x hx hr hst, mul_comm]

theorem pathStieltjesIntegral_const (c : ℝ) (t : ℝ≥0) :
    pathStieltjesIntegral x hx hr (fun _ ↦ c) t = c * x t := by
  rw [pathStieltjesIntegral,
    pathStieltjesIncrementIntegral_const c (show (0 : ℝ≥0) ≤ t from bot_le)]
  ring

theorem pathStieltjesIncrementIntegral_add
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIncrementIntegral x hx hr (fun u ↦ f u + g u) s t =
      pathStieltjesIncrementIntegral x hx hr f s t +
        pathStieltjesIncrementIntegral x hx hr g s t := by
  simp only [pathStieltjesIncrementIntegral,
    integral_add (integrableOn_positiveVariationStieltjes hf)
      (integrableOn_positiveVariationStieltjes hg),
    integral_add (integrableOn_negativeVariationStieltjes hf)
      (integrableOn_negativeVariationStieltjes hg)]
  ring

theorem pathStieltjesIncrementIntegral_const_mul (c : ℝ) (f : ℝ≥0 → ℝ) (s t : ℝ≥0) :
    pathStieltjesIncrementIntegral x hx hr (fun u ↦ c * f u) s t =
      c * pathStieltjesIncrementIntegral x hx hr f s t := by
  simp only [pathStieltjesIncrementIntegral, integral_const_mul]
  ring

theorem pathStieltjesIncrementIntegral_congr_ae
    (hfg : f =ᵐ[(totalVariationStieltjes x hx hr).measure.restrict (Ioc s t)] g) :
    pathStieltjesIncrementIntegral x hx hr f s t =
      pathStieltjesIncrementIntegral x hx hr g s t := by
  have hp := hfg.filter_mono (ae_mono
    (Measure.restrict_mono_measure (positiveVariationStieltjes_measure_le x hx hr) _))
  have hn := hfg.filter_mono (ae_mono
    (Measure.restrict_mono_measure (negativeVariationStieltjes_measure_le x hx hr) _))
  rw [pathStieltjesIncrementIntegral, pathStieltjesIncrementIntegral,
    integral_congr_ae hp, integral_congr_ae hn]

theorem norm_pathStieltjesIncrementIntegral_le {C : ℝ}
    (hC : ∀ u ∈ Ioc s t, ‖f u‖ ≤ C) (hst : s ≤ t) :
    ‖pathStieltjesIncrementIntegral x hx hr f s t‖ ≤ C * (eVariationOn x (Icc s t)).toReal := by
  have hp := norm_setIntegral_le_of_norm_le_const
    (μ := (positiveVariationStieltjes x hx hr).measure) measure_Ioc_lt_top hC
  have hn := norm_setIntegral_le_of_norm_le_const
    (μ := (negativeVariationStieltjes x hx hr).measure) measure_Ioc_lt_top hC
  have hm : ((positiveVariationStieltjes x hx hr).measure (Ioc s t)).toReal +
      ((negativeVariationStieltjes x hx hr).measure (Ioc s t)).toReal =
        (eVariationOn x (Icc s t)).toReal := by
    rw [← ENNReal.toReal_add measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne,
      ← Measure.add_apply, ← totalVariationStieltjes_measure_eq_add,
      totalVariationStieltjes_measure_Ioc x hx hr hst]
  calc
    ‖pathStieltjesIncrementIntegral x hx hr f s t‖ ≤
        ‖∫ u in Ioc s t, f u ∂(positiveVariationStieltjes x hx hr).measure‖ +
          ‖∫ u in Ioc s t, f u ∂(negativeVariationStieltjes x hx hr).measure‖ := norm_sub_le _ _
    _ ≤ C * ((positiveVariationStieltjes x hx hr).measure (Ioc s t)).toReal +
        C * ((negativeVariationStieltjes x hx hr).measure (Ioc s t)).toReal := add_le_add hp hn
    _ = C * (eVariationOn x (Icc s t)).toReal := by rw [← mul_add, hm]

theorem norm_pathStieltjesIntegral_le {C : ℝ} (hC : ∀ u ∈ Icc 0 t, ‖f u‖ ≤ C) :
    ‖pathStieltjesIntegral x hx hr f t‖ ≤ C * (|x 0| + pathTotalVariation x t) := by
  have h0 := hC 0 ⟨le_rfl, bot_le⟩
  have hinc := norm_pathStieltjesIncrementIntegral_le
    (x := x) (hx := hx) (hr := hr) (fun u hu ↦ hC u ⟨hu.1.le, hu.2⟩) bot_le
  calc
    ‖pathStieltjesIntegral x hx hr f t‖ ≤
        ‖f 0 * x 0‖ + ‖pathStieltjesIncrementIntegral x hx hr f 0 t‖ := norm_add_le _ _
    _ ≤ C * |x 0| + C * (eVariationOn x (Icc 0 t)).toReal :=
      add_le_add (by simpa only [norm_mul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right h0 (norm_nonneg (x 0))) hinc
    _ = _ := by rw [pathTotalVariation_eq, mul_add]

theorem tendsto_pathStieltjesIncrementIntegral_of_dominated_convergence
    {f : ℕ → ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ} {bound : ℝ≥0 → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n)
      ((totalVariationStieltjes x hx hr).measure.restrict (Ioc s t)))
    (hb : IntegrableOn bound (Ioc s t) (totalVariationStieltjes x hx hr).measure)
    (hf : ∀ n, ∀ᵐ u ∂(totalVariationStieltjes x hx hr).measure.restrict (Ioc s t),
      ‖f n u‖ ≤ bound u)
    (hlim : ∀ᵐ u ∂(totalVariationStieltjes x hx hr).measure.restrict (Ioc s t),
      Tendsto (fun n ↦ f n u) atTop (𝓝 (g u))) :
    Tendsto (fun n ↦ pathStieltjesIncrementIntegral x hx hr (f n) s t) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hx hr g s t)) := by
  have hp := Measure.restrict_mono_measure (positiveVariationStieltjes_measure_le x hx hr) (Ioc s t)
  have hn := Measure.restrict_mono_measure (negativeVariationStieltjes_measure_le x hx hr) (Ioc s t)
  exact (tendsto_integral_of_dominated_convergence bound (fun n ↦ (hfm n).mono_measure hp)
    (integrableOn_positiveVariationStieltjes hb) (fun n ↦ (hf n).filter_mono (ae_mono hp))
    (hlim.filter_mono (ae_mono hp))).sub
      (tendsto_integral_of_dominated_convergence bound (fun n ↦ (hfm n).mono_measure hn)
        (integrableOn_negativeVariationStieltjes hb) (fun n ↦ (hf n).filter_mono (ae_mono hn))
        (hlim.filter_mono (ae_mono hn)))

end StochLean

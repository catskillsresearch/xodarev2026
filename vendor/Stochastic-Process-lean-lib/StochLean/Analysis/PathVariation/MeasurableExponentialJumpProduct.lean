/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExponentialJumpProductLog
public import StochLean.ForMathlib.MeasureTheory.MeasurableComplexAtomicSeries

/-! # Measurability of the actual jump product on random atom sets

The nonzero jump locations are supported by a measurable finite-fiber
kernel. Square summability supplies both the zero count and the complex
logarithm series. The guarded formula preserves zero and negative factors;
it proves measurability of the original product, not of a substitute.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem measurable_tprod_exponentialJumpFactor_of_kernel_atoms
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {u : Ω → ℝ≥0 → ℝ}
    (hu : Measurable (uncurry u)) (hs : ∀ ω, Summable (fun t ↦ u ω t ^ 2))
    (hzero : ∀ ω t, κ ω {t} = 0 → u ω t = 0) :
    Measurable fun ω ↦ ∏' t, exponentialJumpFactor (u ω t) := by
  classical
  have hc : Measurable fun ω ↦ ∑' t, if u ω t = -1 then (1 : ℝ) else 0 :=
    measurable_tsum_of_support_in_kernel_atoms κ hκ
      (g := fun ω t ↦ if u ω t = -1 then (1 : ℝ) else 0)
      (Measurable.ite (measurableSet_eq_fun hu measurable_const)
        measurable_const measurable_const)
      (fun ω ↦ (summable_indicator_jump_neg_one (hs ω)).abs)
      (fun ω t ht ↦ by simp [hzero ω t ht])
  have hlog : Measurable (uncurry fun ω t ↦
      Complex.log (exponentialJumpFactor (u ω t) : ℂ)) :=
    Complex.measurable_log.comp (Complex.measurable_ofReal.comp
      ((contDiff_exponentialJumpFactor (n := 2)).continuous.measurable.comp hu))
  have hl := measurable_complex_tsum_of_support_in_kernel_atoms κ hκ hlog
    (fun ω ↦ summable_complex_log_exponentialJumpFactor (hs ω))
    (fun ω t ht ↦ by simp only [hzero ω t ht, exponentialJumpFactor_zero,
      Complex.ofReal_one, Complex.log_one])
  have he (ω : Ω) := tprod_exponentialJumpFactor_eq_zero_guarded_complex_log (hs ω)
  simp_rw [he]
  exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
    (Complex.measurable_re.comp (Complex.measurable_exp.comp hl)) measurable_const

theorem measurable_tprod_exponentialJumpFactor_Ioc_of_kernel_atoms
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {u : Ω → ℝ≥0 → ℝ} (T : ℝ≥0)
    (hu : Measurable (uncurry u))
    (hs : ∀ ω, Summable (fun t : Set.Ioc 0 T ↦ u ω t ^ 2))
    (hzero : ∀ ω t, t ∈ Set.Ioc 0 T → κ ω {t} = 0 → u ω t = 0) :
    Measurable fun ω ↦ ∏' t : Set.Ioc 0 T, exponentialJumpFactor (u ω t) := by
  classical
  let v : Ω → ℝ≥0 → ℝ := fun ω ↦ (Set.Ioc 0 T).indicator (u ω)
  have hv : Measurable (uncurry v) :=
    Measurable.ite (measurable_snd measurableSet_Ioc) hu measurable_const
  have hvs (ω : Ω) : Summable (fun t ↦ v ω t ^ 2) := by
    have h := (summable_subtype_iff_indicator (f := fun t ↦ u ω t ^ 2)
      (s := Set.Ioc 0 T)).mp (hs ω)
    convert h using 1
    funext t
    by_cases ht : t ∈ Set.Ioc 0 T <;> simp [v, Set.indicator, ht]
  have hv0 (ω : Ω) (t : ℝ≥0) (ht : κ ω {t} = 0) : v ω t = 0 := by
    by_cases hm : t ∈ Set.Ioc 0 T
    · simp only [v, Set.indicator_of_mem hm, hzero ω t hm ht]
    · exact Set.indicator_of_notMem hm _
  have he (ω : Ω) : (∏' t, exponentialJumpFactor (v ω t)) =
      ∏' t : Set.Ioc 0 T, exponentialJumpFactor (u ω t) := by
    rw [tprod_subtype (Set.Ioc 0 T) (fun t ↦ exponentialJumpFactor (u ω t))]
    apply tprod_congr
    intro t
    by_cases ht : t ∈ Set.Ioc 0 T <;>
      simp [v, Set.mulIndicator, ht, exponentialJumpFactor_zero]
  simpa only [he] using
    measurable_tprod_exponentialJumpFactor_of_kernel_atoms κ hκ hv hvs hv0

end StochLean

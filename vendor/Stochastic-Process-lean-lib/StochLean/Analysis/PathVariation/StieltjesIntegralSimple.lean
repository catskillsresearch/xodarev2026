/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegral

/-! # Finite-sum formulas for the canonical Stieltjes integral

Intervals are open on the left and closed on the right. Stopping at a finite
horizon caps both endpoints; intervals starting after the horizon contribute zero.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal BigOperators

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem pathStieltjesIncrementIntegral_indicator_Ioc {a b : ℝ≥0} (hab : a ≤ b)
    (c : ℝ) (T : ℝ≥0) :
    pathStieltjesIncrementIntegral x hx hr ((Ioc a b).indicator (fun _ ↦ c)) 0 T =
      c * (x (min b T) - x (min a T)) := by
  have heq : Ioc 0 T ∩ Ioc a b = Ioc a (min b T) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, le_min_iff]
    exact ⟨fun ⟨⟨_, huT⟩, hua, hub⟩ ↦ ⟨hua, hub, huT⟩,
      fun ⟨hua, hub, huT⟩ ↦ ⟨⟨bot_le.trans_lt hua, huT⟩, hua, hub⟩⟩
  simp only [pathStieltjesIncrementIntegral, setIntegral_indicator measurableSet_Ioc,
    heq, setIntegral_const, smul_eq_mul, measureReal_def]
  by_cases hTa : T ≤ a
  · rw [Ioc_eq_empty_of_le (min_le_right b T |>.trans hTa), measure_empty, measure_empty,
      ENNReal.toReal_zero, zero_mul, sub_self, min_eq_right hTa,
      min_eq_right (hTa.trans hab), sub_self, mul_zero]
  · have haT : a ≤ T := (lt_of_not_ge hTa).le
    rw [← sub_mul, variationStieltjes_measure_Ioc_sub x hx hr (le_min hab haT),
      min_eq_left haT, mul_comm]

theorem pathStieltjesIncrementIntegral_finsetSum {ι : Type*} (s : Finset ι)
    {f : ι → ℝ≥0 → ℝ} {a b : ℝ≥0}
    (hf : ∀ i ∈ s, IntegrableOn (f i) (Ioc a b) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIncrementIntegral x hx hr (fun u ↦ ∑ i ∈ s, f i u) a b =
      ∑ i ∈ s, pathStieltjesIncrementIntegral x hx hr (f i) a b := by
  simp only [pathStieltjesIncrementIntegral,
    integral_finsetSum s (fun i hi ↦ integrableOn_positiveVariationStieltjes (hf i hi)),
    integral_finsetSum s (fun i hi ↦ integrableOn_negativeVariationStieltjes (hf i hi)),
    Finset.sum_sub_distrib]

theorem integrableOn_variationStieltjes_finite_step {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (c0 : ℝ) (T : ℝ≥0) :
    IntegrableOn
      (fun t ↦ if t = 0 then c0 else ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t)
      (Ioc 0 T) (totalVariationStieltjes x hx hr).measure := by
  classical
  have hi (i : ι) : IntegrableOn ((Ioc (a i) (b i)).indicator (fun _ ↦ c i)) (Ioc 0 T)
      (totalVariationStieltjes x hx hr).measure := by
    have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ c i) (Ioc 0 T)
        (totalVariationStieltjes x hx hr).measure := integrableOn_const measure_Ioc_lt_top.ne
    exact hconst.indicator measurableSet_Ioc
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [if_neg (ne_of_gt ht.1)]

theorem pathStieltjesIntegral_finite_step {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (hab : ∀ i, a i ≤ b i) (c0 : ℝ) (T : ℝ≥0) :
    pathStieltjesIntegral x hx hr
      (fun t ↦ if t = 0 then c0 else ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t) T =
      c0 * x 0 + ∑ i, c i * (x (min (b i) T) - x (min (a i) T)) := by
  classical
  have hi (i : ι) : IntegrableOn ((Ioc (a i) (b i)).indicator (fun _ ↦ c i)) (Ioc 0 T)
      (totalVariationStieltjes x hx hr).measure := by
    have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ c i) (Ioc 0 T)
        (totalVariationStieltjes x hx hr).measure := integrableOn_const measure_Ioc_lt_top.ne
    exact hconst.indicator measurableSet_Ioc
  have hcongr : pathStieltjesIncrementIntegral x hx hr
      (fun t ↦ if t = 0 then c0 else ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t) 0 T =
      pathStieltjesIncrementIntegral x hx hr
        (fun t ↦ ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t) 0 T := by
    apply pathStieltjesIncrementIntegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [if_neg (ne_of_gt ht.1)]
  simp only [pathStieltjesIntegral, ↓reduceIte, hcongr,
    pathStieltjesIncrementIntegral_finsetSum Finset.univ (fun i _ ↦ hi i),
    pathStieltjesIncrementIntegral_indicator_Ioc (hab _)]

end StochLean

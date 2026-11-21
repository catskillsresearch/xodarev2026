/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralJump
public import StochLean.ForMathlib.MeasurableStieltjesNNReal

/-! # Stopping canonical Stieltjes measures and integrals

Stopping retains the atom at the stopping endpoint. The initial value is unchanged,
even at a zero stopping time; increment measures have no initial atom.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace StochLean

theorem locallyBoundedVariationOn_comp_min {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) (T : ℝ≥0) :
    LocallyBoundedVariationOn (fun t ↦ x (min t T)) univ := by
  intro a b _ _
  have hb : BoundedVariationOn x (Icc 0 b) := by
    simpa only [univ_inter] using hx 0 b (mem_univ _) (mem_univ _)
  change eVariationOn (fun t ↦ x (min t T)) (univ ∩ Icc a b) ≠ ⊤
  apply ne_top_of_le_ne_top hb
  exact eVariationOn.comp_le_of_monotoneOn x
    (s := Icc 0 b) (t := univ ∩ Icc a b) (fun t ↦ min t T)
    (fun _ _ _ _ h ↦ min_le_min_right T h)
    (fun t ht ↦ ⟨bot_le, (min_le_left t T).trans ht.2.2⟩)

theorem rightContinuous_comp_min {x : ℝ≥0 → ℝ}
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T t : ℝ≥0) :
    ContinuousWithinAt (fun u ↦ x (min u T)) (Ici t) t :=
  (hr (min t T)).comp (f := fun u : ℝ≥0 ↦ min u T)
    (continuous_id.min continuous_const).continuousWithinAt
    (fun u hu ↦ show min t T ≤ min u T from min_le_min_right T hu)

theorem pathTotalVariation_comp_min (x : ℝ≥0 → ℝ) (T t : ℝ≥0) :
    pathTotalVariation (fun u ↦ x (min u T)) t = pathTotalVariation x (min t T) := by
  rw [pathTotalVariation_eq, pathTotalVariation_eq]
  congr 1
  have him : (fun u : ℝ≥0 ↦ min u T) '' Icc 0 t = Icc 0 (min t T) := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨bot_le, min_le_min_right T hv.2⟩
    · intro hu
      exact ⟨u, ⟨bot_le, hu.2.trans (min_le_left _ _)⟩,
        min_eq_left (hu.2.trans (min_le_right _ _))⟩
  exact (eVariationOn.comp_eq_of_monotoneOn x (fun u ↦ min u T)
    (fun _ _ _ _ h ↦ min_le_min_right T h)).trans (congrArg (eVariationOn x) him)

theorem pathPositiveVariation_comp_min (x : ℝ≥0 → ℝ) (T t : ℝ≥0) :
    pathPositiveVariation (fun u ↦ x (min u T)) t = pathPositiveVariation x (min t T) := by
  simp only [pathPositiveVariation, pathTotalVariation_comp_min,
    min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le)]

theorem pathNegativeVariation_comp_min (x : ℝ≥0 → ℝ) (T t : ℝ≥0) :
    pathNegativeVariation (fun u ↦ x (min u T)) t = pathNegativeVariation x (min t T) := by
  simp only [pathNegativeVariation, pathTotalVariation_comp_min,
    min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le)]

theorem stieltjesMeasure_eq_restrict_of_eq_min {A B : StieltjesFunction ℝ≥0} (T : ℝ≥0)
    (h : ∀ t, B t = A (min t T)) : B.measure = A.measure.restrict (Iic T) := by
  let : IsFiniteMeasure (A.measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  symm
  apply Measure.ext_of_Iic
  intro t
  simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
    stieltjesMeasure_Iic_nnreal, h, min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le)]

variable (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0)

theorem totalVariationStieltjes_measure_comp_min :
    (totalVariationStieltjes (fun u ↦ x (min u T)) (locallyBoundedVariationOn_comp_min hx T)
      (rightContinuous_comp_min hr T)).measure =
        (totalVariationStieltjes x hx hr).measure.restrict (Iic T) :=
  stieltjesMeasure_eq_restrict_of_eq_min T (pathTotalVariation_comp_min x T)

theorem positiveVariationStieltjes_measure_comp_min :
    (positiveVariationStieltjes (fun u ↦ x (min u T)) (locallyBoundedVariationOn_comp_min hx T)
      (rightContinuous_comp_min hr T)).measure =
        (positiveVariationStieltjes x hx hr).measure.restrict (Iic T) :=
  stieltjesMeasure_eq_restrict_of_eq_min T (pathPositiveVariation_comp_min x T)

theorem negativeVariationStieltjes_measure_comp_min :
    (negativeVariationStieltjes (fun u ↦ x (min u T)) (locallyBoundedVariationOn_comp_min hx T)
      (rightContinuous_comp_min hr T)).measure =
        (negativeVariationStieltjes x hx hr).measure.restrict (Iic T) :=
  stieltjesMeasure_eq_restrict_of_eq_min T (pathNegativeVariation_comp_min x T)

theorem pathStieltjesIntegral_comp_min (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathStieltjesIntegral (fun u ↦ x (min u T)) (locallyBoundedVariationOn_comp_min hx T)
      (rightContinuous_comp_min hr T) f t = pathStieltjesIntegral x hx hr f (min t T) := by
  simp only [pathStieltjesIntegral, pathStieltjesIncrementIntegral]
  rw [positiveVariationStieltjes_measure_comp_min x hx hr T,
    negativeVariationStieltjes_measure_comp_min x hx hr T]
  simp only [Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Iic,
    min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le)]

theorem pathStieltjesIntegral_indicator_Iic (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathStieltjesIntegral x hx hr ((Iic T).indicator f) t =
      pathStieltjesIntegral x hx hr f (min t T) := by
  simp only [pathStieltjesIntegral, pathStieltjesIncrementIntegral,
    indicator_of_mem (show (0 : ℝ≥0) ∈ Iic T by change (0 : ℝ≥0) ≤ T; exact bot_le),
    setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic]

/-- Integrating the indicator strictly before a positive time removes the
jump at that time.  Before the cutoff the integral is the original path; at
and after the cutoff it is its left limit. -/
theorem pathStieltjesIntegral_indicator_Iio_one (hT : 0 < T) (t : ℝ≥0) :
    pathStieltjesIntegral x hx hr ((Iio T).indicator fun _ ↦ (1 : ℝ)) t =
      if t < T then x t else Function.leftLim x T := by
  by_cases ht : t < T
  · rw [if_pos ht, pathStieltjesIntegral]
    have he : ((Iio T).indicator fun _ ↦ (1 : ℝ)) =ᵐ[
        (totalVariationStieltjes x hx hr).measure.restrict (Ioc 0 t)]
        (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      simp [hu.2.trans_lt ht]
    rw [pathStieltjesIncrementIntegral_congr_ae he]
    have hinc : pathStieltjesIncrementIntegral x hx hr (fun _ ↦ (1 : ℝ)) 0 t =
        1 * (x t - x 0) :=
      pathStieltjesIncrementIntegral_const 1 bot_le
    rw [hinc]
    simp only [indicator_of_mem (show (0 : ℝ≥0) ∈ Iio T from hT), one_mul]
    ring
  · rw [if_neg ht, pathStieltjesIntegral]
    have hset : Ioc (0 : ℝ≥0) t ∩ Iio T = Ioo 0 T := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · exact fun h ↦ ⟨⟨h.1, h.2.le.trans (le_of_not_gt ht)⟩, h.2⟩
    simp only [pathStieltjesIncrementIntegral,
      setIntegral_indicator measurableSet_Iio, hset, setIntegral_const,
      smul_eq_mul]
    simp only [indicator_of_mem (show (0 : ℝ≥0) ∈ Iio T from hT), one_mul]
    rw [measureReal_def, measureReal_def, StieltjesFunction.measure_Ioo,
      StieltjesFunction.measure_Ioo]
    have hpnonneg : 0 ≤ Function.leftLim (positiveVariationStieltjes x hx hr) T -
        positiveVariationStieltjes x hx hr 0 :=
      sub_nonneg.mpr ((positiveVariationStieltjes x hx hr).mono.le_leftLim hT)
    have hnnonneg : 0 ≤ Function.leftLim (negativeVariationStieltjes x hx hr) T -
        negativeVariationStieltjes x hx hr 0 :=
      sub_nonneg.mpr ((negativeVariationStieltjes x hx hr).mono.le_leftLim hT)
    rw [ENNReal.toReal_ofReal hpnonneg, ENNReal.toReal_ofReal hnnonneg]
    have hp0 : positiveVariationStieltjes x hx hr 0 = 0 := pathPositiveVariation_zero x
    have hn0 : negativeVariationStieltjes x hx hr 0 = 0 := pathNegativeVariation_zero x
    have hd : positiveVariationStieltjes x hx hr T -
        negativeVariationStieltjes x hx hr T = x T - x 0 :=
      pathPositiveVariation_sub_negative x T
    have hj := variationStieltjes_measure_singleton_sub (x := x) (hx := hx) (hr := hr) hT
    rw [stieltjesMeasure_real_singleton, stieltjesMeasure_real_singleton] at hj
    linarith

end StochLean

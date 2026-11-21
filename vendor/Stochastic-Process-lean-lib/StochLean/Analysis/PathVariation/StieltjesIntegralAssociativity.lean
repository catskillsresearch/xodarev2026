/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralRegularity
public import StochLean.Analysis.PathVariation.StieltjesIntegralVariation
public import StochLean.ForMathlib.MeasurableStieltjesNNReal
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! # Associativity of pathwise Stieltjes integration

For a right-continuous locally finite-variation path, integration first by `f`
and then by `g` agrees with one integration by the pointwise product `g * f`.
The proof identifies the finite-horizon signed Stieltjes vector measure of the
first primitive with the original signed measure having density `f`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace StochLean

theorem integrable_withDensity_of_integrable_mul
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hf : Measurable f)
    (hgf : Integrable (fun x => g x * f x) μ) :
    Integrable g (μ.withDensity fun x => ENNReal.ofReal (f x)) := by
  rw [integrable_withDensity_iff hf.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  let s : Set α := f ⁻¹' Ici 0
  have hs : MeasurableSet s := measurableSet_Ici.preimage hf
  have hi := hgf.indicator hs
  apply hi.congr
  filter_upwards with x
  by_cases hx : 0 ≤ f x
  · rw [ENNReal.toReal_ofReal hx]
    simp [s, hx]
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    rw [ENNReal.ofReal_of_nonpos hx']
    simp [s, hx]

theorem integral_withDensityVector_real
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ)
    (hgp : Integrable g (μ.withDensity fun x => ENNReal.ofReal (f x)))
    (hgn : Integrable g (μ.withDensity fun x => ENNReal.ofReal (-f x))) :
    (∫ᵛ x, g x ∂<•(μ.withDensityᵥ f)) = ∫ x, g x * f x ∂μ := by
  letI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  letI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (-f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf]
  rw [MeasureTheory.VectorMeasure.integral_sub_vectorMeasure]
  · rw [MeasureTheory.VectorMeasure.integral_toSignedMeasure,
      MeasureTheory.VectorMeasure.integral_toSignedMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul₀
          hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
    have hneg_meas :
        AEMeasurable (fun x => ENNReal.ofReal (-f x)) μ := by
      simpa only [Pi.neg_apply] using
        hf.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hneg_meas
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
    rw [← integral_sub]
    · apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul]
      by_cases hx : 0 ≤ f x
      · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx)]
        rw [ENNReal.toReal_ofReal hx]
        simp [mul_comm]
      · have hx' : f x ≤ 0 := le_of_not_ge hx
        rw [ENNReal.ofReal_of_nonpos hx']
        rw [ENNReal.toReal_ofReal (neg_nonneg.mpr hx')]
        simp [mul_comm]
    · simpa only [smul_eq_mul] using
        (integrable_withDensity_iff_integrable_smul₀'
          hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hgp
    · simpa only [smul_eq_mul] using
        (integrable_withDensity_iff_integrable_smul₀' hneg_meas
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hgn
  · simpa only [MeasureTheory.VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hgp
  · simpa only [MeasureTheory.VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hgn

theorem vectorIntegrable_withDensity_real
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ)
    (hgp : Integrable g (μ.withDensity fun x => ENNReal.ofReal (f x)))
    (hgn : Integrable g (μ.withDensity fun x => ENNReal.ofReal (-f x))) :
    (μ.withDensityᵥ f).Integrable g := by
  letI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  letI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (-f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf]
  have hp : (μ.withDensity fun x => ENNReal.ofReal (f x)).toSignedMeasure.Integrable g := by
    simpa only [MeasureTheory.VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hgp
  have hn : (μ.withDensity fun x => ENNReal.ofReal (-f x)).toSignedMeasure.Integrable g := by
    simpa only [MeasureTheory.VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hgn
  exact hp.sub_vectorMeasure hn

theorem stieltjesMeasure_restrict_Iic_eq_Ioc (A : StieltjesFunction ℝ≥0) (T : ℝ≥0) :
    A.measure.restrict (Iic T) = A.measure.restrict (Ioc 0 T) := by
  rw [← Icc_bot]
  exact Measure.restrict_congr_set
    (Ioc_ae_eq_Icc' (variationStieltjes_measure_zero A)).symm

noncomputable def pathSignedStieltjesMeasure (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0) :
    VectorMeasure ℝ≥0 ℝ := by
  letI : IsFiniteMeasure
      ((positiveVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure
      ((negativeVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  exact
    ((positiveVariationStieltjes x hx hr).measure.restrict (Iic T)).toSignedMeasure -
      ((negativeVariationStieltjes x hx hr).measure.restrict (Iic T)).toSignedMeasure

theorem pathSignedStieltjesMeasure_apply_Iic (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T t : ℝ≥0) :
    pathSignedStieltjesMeasure x hx hr T (Iic t) = x (min t T) - x 0 := by
  letI : IsFiniteMeasure
      ((positiveVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure
      ((negativeVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  rw [pathSignedStieltjesMeasure, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable measurableSet_Iic,
    Measure.toSignedMeasure_apply_measurable measurableSet_Iic,
    measureReal_def, measureReal_def,
    Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    Iic_inter_Iic, stieltjesMeasure_Iic_nnreal, stieltjesMeasure_Iic_nnreal]
  rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · change (pathPositiveVariation x (min t T) - pathPositiveVariation x 0) -
        (pathNegativeVariation x (min t T) - pathNegativeVariation x 0) = _
    simpa only [pathPositiveVariation_zero, pathNegativeVariation_zero, sub_zero] using
      pathPositiveVariation_sub_negative x (min t T)
  · exact sub_nonneg.mpr ((negativeVariationStieltjes x hx hr).mono bot_le)
  · exact sub_nonneg.mpr ((positiveVariationStieltjes x hx hr).mono bot_le)

theorem pathSignedStieltjesMeasure_apply_univ (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0) :
    pathSignedStieltjesMeasure x hx hr T univ = x T - x 0 := by
  letI : IsFiniteMeasure
      ((positiveVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure
      ((negativeVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  rw [pathSignedStieltjesMeasure, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    measureReal_def, measureReal_def,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ,
    stieltjesMeasure_Iic_nnreal, stieltjesMeasure_Iic_nnreal]
  rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · change (pathPositiveVariation x T - pathPositiveVariation x 0) -
        (pathNegativeVariation x T - pathNegativeVariation x 0) = _
    simpa only [pathPositiveVariation_zero, pathNegativeVariation_zero, sub_zero] using
      pathPositiveVariation_sub_negative x T
  · exact sub_nonneg.mpr ((negativeVariationStieltjes x hx hr).mono bot_le)
  · exact sub_nonneg.mpr ((positiveVariationStieltjes x hx hr).mono bot_le)

theorem integral_pathSignedStieltjesMeasure (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (g : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hg : IntegrableOn g (Ioc 0 T) (totalVariationStieltjes x hx hr).measure) :
    (∫ᵛ u, g u ∂<•(pathSignedStieltjesMeasure x hx hr T)) =
      pathStieltjesIntegral x hx hr g T - pathStieltjesIntegral x hx hr g 0 := by
  have hgp0 : Integrable g
      ((positiveVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)) :=
    integrableOn_positiveVariationStieltjes hg
  have hgn0 : Integrable g
      ((negativeVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)) :=
    integrableOn_negativeVariationStieltjes hg
  have hgp : Integrable g
      ((positiveVariationStieltjes x hx hr).measure.restrict (Iic T)) := by
    rwa [stieltjesMeasure_restrict_Iic_eq_Ioc]
  have hgn : Integrable g
      ((negativeVariationStieltjes x hx hr).measure.restrict (Iic T)) := by
    rwa [stieltjesMeasure_restrict_Iic_eq_Ioc]
  letI : IsFiniteMeasure
      ((positiveVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure
      ((negativeVariationStieltjes x hx hr).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  rw [pathSignedStieltjesMeasure,
    MeasureTheory.VectorMeasure.integral_sub_vectorMeasure]
  · rw [MeasureTheory.VectorMeasure.integral_toSignedMeasure,
      MeasureTheory.VectorMeasure.integral_toSignedMeasure,
      stieltjesMeasure_restrict_Iic_eq_Ioc,
      stieltjesMeasure_restrict_Iic_eq_Ioc]
    exact (pathStieltjesIntegral_sub_eq_incrementIntegral hg bot_le).symm
  · simpa only [MeasureTheory.VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hgp
  · simpa only [MeasureTheory.VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hgn

noncomputable def pathStieltjesDensityMeasure (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f : ℝ≥0 → ℝ) (T : ℝ≥0) :
    VectorMeasure ℝ≥0 ℝ :=
  ((positiveVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)).withDensityᵥ f -
    ((negativeVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)).withDensityᵥ f

theorem pathStieltjesDensityMeasure_apply_Iic (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f : ℝ≥0 → ℝ) (T t : ℝ≥0)
    (hf : IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesDensityMeasure x hx hr f T (Iic t) =
      pathStieltjesIntegral x hx hr f (min t T) -
        pathStieltjesIntegral x hx hr f 0 := by
  have hfp : Integrable f
      ((positiveVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)) :=
    integrableOn_positiveVariationStieltjes hf
  have hfn : Integrable f
      ((negativeVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)) :=
    integrableOn_negativeVariationStieltjes hf
  rw [pathStieltjesDensityMeasure, _root_.sub_apply,
    withDensityᵥ_apply hfp measurableSet_Iic,
    withDensityᵥ_apply hfn measurableSet_Iic]
  by_cases ht : t ≤ T
  · rw [integral_Iic_restrict_Ioc ht, integral_Iic_restrict_Ioc ht,
      min_eq_left ht]
    have hft : IntegrableOn f (Ioc 0 t)
        (totalVariationStieltjes x hx hr).measure :=
      hf.mono_set fun u hu ↦ ⟨hu.1, hu.2.trans ht⟩
    exact (pathStieltjesIntegral_sub_eq_incrementIntegral hft bot_le).symm
  · have hTt : T ≤ t := le_of_not_ge ht
    have heq : Iic t ∩ Ioc 0 T = Ioc 0 T := inter_eq_right.mpr fun u hu ↦ hu.2.trans hTt
    rw [Measure.restrict_restrict measurableSet_Iic, heq,
      Measure.restrict_restrict measurableSet_Iic, heq, min_eq_right hTt]
    exact (pathStieltjesIntegral_sub_eq_incrementIntegral hf bot_le).symm

theorem pathStieltjesDensityMeasure_apply_univ (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesDensityMeasure x hx hr f T univ =
      pathStieltjesIntegral x hx hr f T - pathStieltjesIntegral x hx hr f 0 := by
  have hfp : Integrable f
      ((positiveVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)) :=
    integrableOn_positiveVariationStieltjes hf
  have hfn : Integrable f
      ((negativeVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)) :=
    integrableOn_negativeVariationStieltjes hf
  rw [pathStieltjesDensityMeasure, _root_.sub_apply,
    withDensityᵥ_apply hfp MeasurableSet.univ,
    withDensityᵥ_apply hfn MeasurableSet.univ,
    Measure.restrict_univ, Measure.restrict_univ]
  exact (pathStieltjesIntegral_sub_eq_incrementIntegral hf bot_le).symm

theorem integral_pathStieltjesDensityMeasure (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f g : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hfm : Measurable f)
    (hf : IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hgf : IntegrableOn (fun u ↦ g u * f u) (Ioc 0 T)
      (totalVariationStieltjes x hx hr).measure) :
    (∫ᵛ u, g u ∂<•(pathStieltjesDensityMeasure x hx hr f T)) =
      pathStieltjesIntegral x hx hr (fun u ↦ g u * f u) T -
        pathStieltjesIntegral x hx hr (fun u ↦ g u * f u) 0 := by
  let μp := (positiveVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)
  let μn := (negativeVariationStieltjes x hx hr).measure.restrict (Ioc 0 T)
  have hfp : Integrable f μp := integrableOn_positiveVariationStieltjes hf
  have hfn : Integrable f μn := integrableOn_negativeVariationStieltjes hf
  have hgfp : Integrable (fun u ↦ g u * f u) μp :=
    integrableOn_positiveVariationStieltjes hgf
  have hgfn : Integrable (fun u ↦ g u * f u) μn :=
    integrableOn_negativeVariationStieltjes hgf
  have hgpp : Integrable g (μp.withDensity fun u ↦ ENNReal.ofReal (f u)) :=
    integrable_withDensity_of_integrable_mul hfm hgfp
  have hgnp : Integrable g (μp.withDensity fun u ↦ ENNReal.ofReal (-f u)) := by
    apply integrable_withDensity_of_integrable_mul hfm.neg
    exact hgfp.neg.congr (Filter.Eventually.of_forall fun u ↦ by simp)
  have hgpn : Integrable g (μn.withDensity fun u ↦ ENNReal.ofReal (f u)) :=
    integrable_withDensity_of_integrable_mul hfm hgfn
  have hgnn : Integrable g (μn.withDensity fun u ↦ ENNReal.ofReal (-f u)) := by
    apply integrable_withDensity_of_integrable_mul hfm.neg
    exact hgfn.neg.congr (Filter.Eventually.of_forall fun u ↦ by simp)
  rw [pathStieltjesDensityMeasure,
    MeasureTheory.VectorMeasure.integral_sub_vectorMeasure
      (vectorIntegrable_withDensity_real hfp hgpp hgnp)
      (vectorIntegrable_withDensity_real hfn hgpn hgnn),
    integral_withDensityVector_real hfp hgpp hgnp,
    integral_withDensityVector_real hfn hgpn hgnn]
  exact (pathStieltjesIntegral_sub_eq_incrementIntegral hgf bot_le).symm

theorem pathSignedStieltjesMeasure_pathStieltjesIntegral
    (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ∀ S, IntegrableOn f (Ioc 0 S) (totalVariationStieltjes x hx hr).measure)
    (hAv : LocallyBoundedVariationOn (pathStieltjesIntegral x hx hr f) univ)
    (hAr : ∀ t, ContinuousWithinAt (pathStieltjesIntegral x hx hr f) (Ici t) t) :
    pathSignedStieltjesMeasure (pathStieltjesIntegral x hx hr f)
        hAv hAr T = pathStieltjesDensityMeasure x hx hr f T := by
  apply MeasureTheory.VectorMeasure.ext_of_generateFrom (range Iic)
  · rintro _ ⟨t, rfl⟩
    rw [pathSignedStieltjesMeasure_apply_Iic,
      pathStieltjesDensityMeasure_apply_Iic x hx hr f T t (hf T)]
  · exact (BorelSpace.measurable_eq (α := ℝ≥0)).trans (borel_eq_generateFrom_Iic ℝ≥0)
  · exact isPiSystem_Iic
  · rw [pathSignedStieltjesMeasure_apply_univ,
      pathStieltjesDensityMeasure_apply_univ x hx hr f T (hf T)]

/-- Stieltjes integration is associative on finite horizons. The separate
initial atom is handled explicitly, so the statement is valid without a
zero-initial-value assumption. -/
theorem pathStieltjesIntegral_associative
    (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f g : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hfm : Measurable f)
    (hf : ∀ S, IntegrableOn f (Ioc 0 S) (totalVariationStieltjes x hx hr).measure)
    (hAv : LocallyBoundedVariationOn (pathStieltjesIntegral x hx hr f) univ)
    (hAr : ∀ t, ContinuousWithinAt (pathStieltjesIntegral x hx hr f) (Ici t) t)
    (hg : IntegrableOn g (Ioc 0 T)
      (totalVariationStieltjes (pathStieltjesIntegral x hx hr f) hAv hAr).measure)
    (hgf : IntegrableOn (fun u ↦ g u * f u) (Ioc 0 T)
      (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIntegral (pathStieltjesIntegral x hx hr f) hAv hAr g T =
      pathStieltjesIntegral x hx hr (fun u ↦ g u * f u) T := by
  have hμ := pathSignedStieltjesMeasure_pathStieltjesIntegral
    x hx hr f T hf hAv hAr
  have hinc :
      pathStieltjesIntegral (pathStieltjesIntegral x hx hr f) hAv hAr g T -
          pathStieltjesIntegral (pathStieltjesIntegral x hx hr f) hAv hAr g 0 =
        pathStieltjesIntegral x hx hr (fun u ↦ g u * f u) T -
          pathStieltjesIntegral x hx hr (fun u ↦ g u * f u) 0 := by
    calc
      _ = (∫ᵛ u, g u ∂<•(pathSignedStieltjesMeasure
          (pathStieltjesIntegral x hx hr f) hAv hAr T)) :=
        (integral_pathSignedStieltjesMeasure
          (pathStieltjesIntegral x hx hr f) hAv hAr g T hg).symm
      _ = (∫ᵛ u, g u ∂<•(pathStieltjesDensityMeasure x hx hr f T)) := by rw [hμ]
      _ = _ := integral_pathStieltjesDensityMeasure x hx hr f g T hfm (hf T) hgf
  have h0 :
      pathStieltjesIntegral (pathStieltjesIntegral x hx hr f) hAv hAr g 0 =
        pathStieltjesIntegral x hx hr (fun u ↦ g u * f u) 0 := by
    simp only [pathStieltjesIntegral_zero]
    ring
  linarith

end StochLean

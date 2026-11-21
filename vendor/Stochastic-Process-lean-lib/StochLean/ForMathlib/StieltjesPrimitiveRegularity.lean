/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import StochLean.Probability.Process.Path.Caglad
public import Mathlib.Topology.Order.LeftRightLim

/-! # One-sided regularity of measure primitives, including atoms

Right limits of closed-upper-endpoint integrals retain the endpoint atom. Left
limits use the open upper endpoint instead. No atomless-measure assumption occurs.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure ℝ≥0} {g : ℝ≥0 → E}

theorem continuousWithinAt_integral_Iic_right (hg : Integrable g μ) (t : ℝ≥0) :
    ContinuousWithinAt (fun r ↦ ∫ u in Iic r, g u ∂μ) (Ici t) t := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[Ici t] t)
    (F := fun r ↦ (Iic r).indicator g) (f := (Iic t).indicator g) (fun u ↦ ‖g u‖)
    (Eventually.of_forall fun r ↦ hg.aestronglyMeasurable.indicator measurableSet_Iic)
    (Eventually.of_forall fun r ↦ Eventually.of_forall fun u ↦ norm_indicator_le_norm_self g u)
    hg.norm
    (Eventually.of_forall fun u ↦ by
      by_cases hu : u ≤ t
      · have heq : (fun r ↦ (Iic r).indicator g u) =ᶠ[𝓝[Ici t] t] fun _ ↦ g u := by
          filter_upwards [self_mem_nhdsWithin] with r hr
          exact indicator_of_mem (s := Iic r) (a := u)
            (hu.trans (show t ≤ r from hr)) g
        rw [indicator_of_mem (s := Iic t) (a := u) hu]
        exact tendsto_const_nhds.congr' heq.symm
      · have hut : t < u := lt_of_not_ge hu
        have heq : (fun r ↦ (Iic r).indicator g u) =ᶠ[𝓝[Ici t] t] fun _ ↦ 0 := by
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hut)] with r hr
          exact indicator_of_notMem (s := Iic r) (a := u)
            (by change ¬ u ≤ r; exact not_le.mpr hr) g
        rw [indicator_of_notMem (s := Iic t) (a := u) hu]
        exact tendsto_const_nhds.congr' heq.symm)
  change Tendsto _ (𝓝[Ici t] t) (𝓝 _)
  simpa only [integral_indicator measurableSet_Iic] using h

theorem tendsto_integral_Iic_left (hg : Integrable g μ) (t : ℝ≥0) :
    Tendsto (fun r ↦ ∫ u in Iic r, g u ∂μ) (𝓝[<] t) (𝓝 (∫ u in Iio t, g u ∂μ)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[<] t)
    (F := fun r ↦ (Iic r).indicator g) (f := (Iio t).indicator g) (fun u ↦ ‖g u‖)
    (Eventually.of_forall fun r ↦ hg.aestronglyMeasurable.indicator measurableSet_Iic)
    (Eventually.of_forall fun r ↦ Eventually.of_forall fun u ↦ norm_indicator_le_norm_self g u)
    hg.norm
    (Eventually.of_forall fun u ↦ by
      by_cases hu : u < t
      · have heq : (fun r ↦ (Iic r).indicator g u) =ᶠ[𝓝[<] t] fun _ ↦ g u := by
          filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hu)] with r hr
          exact indicator_of_mem (s := Iic r) (a := u) (show u ≤ r from hr.le) g
        rw [indicator_of_mem (s := Iio t) (a := u) hu]
        exact tendsto_const_nhds.congr' heq.symm
      · have heq : (fun r ↦ (Iic r).indicator g u) =ᶠ[𝓝[<] t] fun _ ↦ 0 := by
          filter_upwards [self_mem_nhdsWithin] with r hr
          exact indicator_of_notMem (s := Iic r) (a := u)
            (not_le.mpr ((show r < t from hr).trans_le (le_of_not_gt hu))) g
        rw [indicator_of_notMem (s := Iio t) (a := u) hu]
        exact tendsto_const_nhds.congr' heq.symm)
  simpa only [integral_indicator measurableSet_Iic, integral_indicator measurableSet_Iio] using h

theorem integral_Iic_restrict_Ioc {T r : ℝ≥0} (hr : r ≤ T) :
    (∫ u in Iic r, g u ∂μ.restrict (Ioc 0 T)) = ∫ u in Ioc 0 r, g u ∂μ := by
  have heq : Iic r ∩ Ioc 0 T = Ioc 0 r := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun ⟨hur, hu0, _⟩ ↦ ⟨hu0, hur⟩, fun ⟨hu0, hur⟩ ↦ ⟨hur, hu0, hur.trans hr⟩⟩
  rw [Measure.restrict_restrict measurableSet_Iic, heq]

theorem continuousWithinAt_integral_Ioc_right
    (hg : ∀ T, IntegrableOn g (Ioc 0 T) μ) (t : ℝ≥0) :
    ContinuousWithinAt (fun r ↦ ∫ u in Ioc 0 r, g u ∂μ) (Ici t) t := by
  have ht : t < t + 1 := lt_add_one t
  have h := continuousWithinAt_integral_Iic_right (hg (t + 1)) t
  apply h.congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with r hr
    exact (integral_Iic_restrict_Ioc (μ := μ) (g := g) hr.le).symm
  · exact (integral_Iic_restrict_Ioc (μ := μ) (g := g) ht.le).symm

theorem tendsto_integral_Ioc_left
    (hg : ∀ T, IntegrableOn g (Ioc 0 T) μ) (t : ℝ≥0) :
    Tendsto (fun r ↦ ∫ u in Ioc 0 r, g u ∂μ) (𝓝[<] t) (𝓝 (∫ u in Ioo 0 t, g u ∂μ)) := by
  have h := tendsto_integral_Iic_left (hg t) t
  have heq : (∫ u in Iio t, g u ∂μ.restrict (Ioc 0 t)) = ∫ u in Ioo 0 t, g u ∂μ := by
    have hs : Iio t ∩ Ioc 0 t = Ioo 0 t := by
      ext u
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      exact ⟨fun ⟨hut, hu0, _⟩ ↦ ⟨hu0, hut⟩, fun ⟨hu0, hut⟩ ↦ ⟨hut, hu0, hut.le⟩⟩
    rw [Measure.restrict_restrict measurableSet_Iio, hs]
  rw [heq] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact integral_Iic_restrict_Ioc (μ := μ) (g := g) (show r ≤ t from hr.le)

theorem isCadlagPath_integral_Ioc (hg : ∀ T, IntegrableOn g (Ioc 0 T) μ) :
    ProbabilityTheory.IsCadlagPath (fun r ↦ ∫ u in Ioc 0 r, g u ∂μ) :=
  ⟨continuousWithinAt_integral_Ioc_right hg, fun t _ ↦ ⟨_, tendsto_integral_Ioc_left hg t⟩⟩

theorem integral_Ioc_sub_leftLim [CompleteSpace E]
    (hg : ∀ T, IntegrableOn g (Ioc 0 T) μ) {t : ℝ≥0} (ht : 0 < t) :
    (∫ u in Ioc 0 t, g u ∂μ) - Function.leftLim (fun r ↦ ∫ u in Ioc 0 r, g u ∂μ) t =
      μ.real {t} • g t := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  rw [leftLim_eq_of_tendsto (tendsto_integral_Ioc_left hg t)]
  have hu : Ioo 0 t ∪ {t} = Ioc 0 t := by
    simpa only [Icc_self] using Ioo_union_Icc_eq_Ioc ht (le_refl t)
  have hd : Disjoint (Ioo 0 t) {t} := disjoint_singleton_right.mpr (by simp)
  have h := setIntegral_union hd (measurableSet_singleton t)
    ((hg t).mono_set Ioo_subset_Ioc_self)
    ((hg t).mono_set (singleton_subset_iff.mpr ⟨ht, le_rfl⟩))
  rw [hu, integral_singleton] at h
  rw [h, add_sub_cancel_left]

end StochLean

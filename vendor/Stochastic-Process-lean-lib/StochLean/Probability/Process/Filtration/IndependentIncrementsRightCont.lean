/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuous
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Probability.Independence.Integration

/-! # Future-increment independence survives right continuation

For an adapted right-continuous real process, independence of future increments
from `F_s` also holds for `F_(s+)`. Bounded continuous tests and dominated
convergence pass from times strictly above `s` to `s`; no right continuity of
the original filtration or Gaussian-law assumption is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem HasRightContinuousPaths.indep_increment_rightCont
    (hr : HasRightContinuousPaths X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (F.rightCont s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P := by
  have hmeas (u : ℝ≥0) : Measurable (fun ω ↦ X t ω - X u ω) :=
    (ha.measurable (i := t)).sub (ha.measurable (i := u))
  apply indep_comap_of_bcf (F.rightCont.le s) (hmeas s).aemeasurable
  intro A hA f
  obtain rfl | hst := hst.eq_or_lt
  · simp
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun u ↦ f (X t ω - X u ω)) (𝓝[>] s)
      (𝓝 (f (X t ω - X s ω))) := by
    filter_upwards [hr] with ω hω
    exact f.continuous.tendsto _ |>.comp
      (((hω s).mono Ioi_subset_Ici_self).tendsto.const_sub (X t ω))
  have hleft : Tendsto (fun u ↦ ∫ ω in A, f (X t ω - X u ω) ∂P) (𝓝[>] s)
      (𝓝 (∫ ω in A, f (X t ω - X s ω) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) _ _
      (integrable_const _) (ae_restrict_of_ae hlim)
    · exact Eventually.of_forall fun u ↦
        (f.continuous.measurable.comp (hmeas u)).aestronglyMeasurable
    · exact Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _
  have hright : Tendsto (fun u ↦ P.real A * ∫ ω, f (X t ω - X u ω) ∂P) (𝓝[>] s)
      (𝓝 (P.real A * ∫ ω, f (X t ω - X s ω) ∂P)) := by
    apply Tendsto.const_mul
    apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) _ _
      (integrable_const _) hlim
    · exact Eventually.of_forall fun u ↦
        (f.continuous.measurable.comp (hmeas u)).aestronglyMeasurable
    · exact Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hst)] with u hsu hut
  have hle : F.rightCont s ≤ F u := by
    rw [F.rightCont_eq]
    exact iInf₂_le u hsu
  exact ((hi u t hut.le).setIntegral_eq_mul (F.le u) (hmeas u).aemeasurable
    (hle A hA) f.continuous.measurable.aestronglyMeasurable).symm

end ProbabilityTheory

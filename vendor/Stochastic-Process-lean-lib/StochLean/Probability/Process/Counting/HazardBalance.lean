/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Hazard
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual stopped-hazard expectation and increment balance

The process here is the existing `stoppedProcess` applied to the
deterministic cumulative hazard and the original extended lifetime. Its
clock is bounded by a finite observation time before any finite evaluation
is used. No stopped-hazard selector or second real hazard owner is added.

Tonelli's theorem turns a lifetime cutoff at an integration time `u` into
the actual pre-jump survival mass `μ (Ici u)`. Under positive survival at
the finite horizon, that mass is positive and finite, so its reciprocal
cancels legitimately. Initial and infinite atoms remain allowed; only
finite positive lifetimes belong to the hazard's integration interval.

The real L1 and increment statements follow after extended finiteness.
They are deterministic law identities, not yet a compensator theorem in
a completed or right-continuous natural filtration.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0))

/-- The actual stopped hazard integrates exactly those finite positive
hazard times lying at or before the original lifetime, including an atom
at that lifetime. The minimum clock is proved finite before evaluation. -/
theorem stoppedProcess_eCumulativeHazard_eq_lintegral (t : ℝ≥0) (v : WithTop ℝ≥0) :
    stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v =
      ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0),
        (Iic v).indicator (fun u ↦ (μ (Ici u))⁻¹) u ∂μ := by
  classical
  have hfin : min (t : WithTop ℝ≥0) v ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hclock : (((min (t : WithTop ℝ≥0) v).untopA : ℝ≥0) : WithTop ℝ≥0) =
      min (t : WithTop ℝ≥0) v := by
    rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  change eCumulativeHazard μ (min (t : WithTop ℝ≥0) v).untopA = _
  rw [eCumulativeHazard, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hclock]
  have hs : Ioc (0 : WithTop ℝ≥0) (min (t : WithTop ℝ≥0) v) =
      Iic v ∩ Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    ext u
    simp only [mem_Ioc, mem_inter_iff, mem_Iic, le_min_iff]
    exact ⟨fun h ↦ ⟨h.2.2, h.1, h.2.1⟩, fun h ↦ ⟨h.2.1, h.2.2, h.1⟩⟩
  rw [hs]

/-- The expected extended stopped hazard is the actual mass of finite
positive lifetimes occurring by the observation time. -/
theorem lintegral_stoppedProcess_eCumulativeHazard [IsFiniteMeasure μ] {t T : ℝ≥0}
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) (ht : t ≤ T) :
    (∫⁻ v, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v ∂μ) =
      μ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  classical
  let w : WithTop ℝ≥0 → ℝ≥0∞ := fun u ↦ (μ (Ici u))⁻¹
  let f : WithTop ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ := fun v ↦ (Iic v).indicator w
  have hw : Measurable w := by
    have ha : Antitone (fun u : WithTop ℝ≥0 ↦ μ (Ici u)) := by
      intro u v huv
      exact measure_mono (Ici_subset_Ici.mpr huv)
    exact ha.measurable.inv
  have hf : Measurable (Function.uncurry f) := by
    have hm : Measurable (fun p : WithTop ℝ≥0 × WithTop ℝ≥0 ↦
        if p.2 ≤ p.1 then w p.2 else 0) :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hw.comp measurable_snd) measurable_const
    convert hm using 1
    funext p
    change (Iic p.1).indicator w p.2 = _
    simp only [Set.indicator_apply, mem_Iic]
  calc
    (∫⁻ v, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v ∂μ) =
        ∫⁻ v, ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), f v u ∂μ ∂μ := by
      apply lintegral_congr
      intro v
      exact stoppedProcess_eCumulativeHazard_eq_lintegral μ t v
    _ = ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0),
        ∫⁻ v, f v u ∂μ ∂μ := lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ _ in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), (1 : ℝ≥0∞) ∂μ := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro u hu
      have hpos : μ (Ici u) ≠ 0 := ne_of_gt (hT.trans_le
        (measure_mono (Ici_subset_Ici.mpr
          (hu.2.trans (WithTop.coe_le_coe.mpr ht)))))
      have he : (fun v ↦ f v u) = (Ici u).indicator (fun _ ↦ w u) := by
        funext v
        simp only [f, Set.indicator_apply, mem_Iic, mem_Ici]
      change (∫⁻ v, f v u ∂μ) = (1 : ℝ≥0∞)
      rw [he, lintegral_indicator_const measurableSet_Ici]
      exact ENNReal.inv_mul_cancel hpos (measure_ne_top μ _)
    _ = _ := setLIntegral_one _

/-- The real actual stopped hazard is integrable and has the expected
finite-positive occurrence mass. Its extended value is first proved
finite for every lifetime, not merely interpreted with `toReal ∞ = 0`. -/
theorem integrable_stoppedProcess_eCumulativeHazard_toReal_and_integral
    [IsFiniteMeasure μ] {t T : ℝ≥0}
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) (ht : t ≤ T) :
    Integrable (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t) μ ∧
      (∫ v, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v ∂μ) =
        μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t
  have hm : Measurable A := (measurable_eCumulativeHazard μ).comp
    ((measurable_const.min measurable_id).untopA)
  have hfin : ∀ v, A v ≠ ∞ := by
    intro v
    exact eCumulativeHazard_ne_top_of_le μ hT
      ((WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) v)).trans ht)
  have he : (∫⁻ v, A v ∂μ) = μ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) :=
    lintegral_stoppedProcess_eCumulativeHazard μ hT ht
  change Integrable (fun v ↦ (A v).toReal) μ ∧
    (∫ v, (A v).toReal ∂μ) = μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0))
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable ?_, ?_⟩
  · rw [he]
    exact measure_ne_top μ _
  · rw [integral_toReal hm.aemeasurable
      (Eventually.of_forall fun v ↦ lt_top_iff_ne_top.mpr (hfin v)), he]
    rfl

/-- On the strict survival event at `s`, the expected actual hazard
increment from `s` to `t` equals the lifetime mass in `(s,t]`. -/
theorem setIntegral_stoppedProcess_eCumulativeHazard_toReal_sub [IsFiniteMeasure μ]
    {s t T : ℝ≥0} (hT : 0 < μ (Ici (T : WithTop ℝ≥0)))
    (hst : s ≤ t) (ht : t ≤ T) :
    (∫ v in Ioi (s : WithTop ℝ≥0),
      (stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v -
      stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id s v) ∂μ) =
      μ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  classical
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id
  have hAt : Integrable (A t) μ ∧ (∫ v, A t v ∂μ) =
      μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) :=
    integrable_stoppedProcess_eCumulativeHazard_toReal_and_integral μ hT ht
  have hAs : Integrable (A s) μ ∧ (∫ v, A s v ∂μ) =
      μ.real (Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0)) :=
    integrable_stoppedProcess_eCumulativeHazard_toReal_and_integral μ hT (hst.trans ht)
  have he : (Ioi (s : WithTop ℝ≥0)).indicator (fun v ↦ A t v - A s v) =
      fun v ↦ A t v - A s v := by
    funext v
    by_cases hv : (s : WithTop ℝ≥0) < v
    · exact Set.indicator_of_mem (show v ∈ Ioi (s : WithTop ℝ≥0) from hv)
        (fun v ↦ A t v - A s v)
    · have hnot : v ∉ Ioi (s : WithTop ℝ≥0) := hv
      rw [Set.indicator_of_notMem hnot]
      have hvs : v ≤ (s : WithTop ℝ≥0) := le_of_not_gt hv
      symm
      dsimp only [A]
      rw [stoppedProcess_eq_of_ge (hvs.trans (WithTop.coe_le_coe.mpr hst)),
        stoppedProcess_eq_of_ge hvs, sub_self]
  have hsets : Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) \
      Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0) =
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    ext v
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · intro h
      exact ⟨lt_of_not_ge (fun hvs ↦ h.2 ⟨h.1.1, hvs⟩), h.1.2⟩
    · intro h
      exact ⟨⟨(WithTop.coe_le_coe.mpr (show (0 : ℝ≥0) ≤ s from bot_le)).trans_lt h.1, h.2⟩,
        fun hvs ↦ not_lt_of_ge hvs.2 h.1⟩
  change (∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ) = _
  calc
    (∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ) =
        ∫ v, A t v - A s v ∂μ := by rw [← integral_indicator measurableSet_Ioi, he]
    _ = (∫ v, A t v ∂μ) - ∫ v, A s v ∂μ := integral_sub hAt.1 hAs.1
    _ = μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) -
        μ.real (Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0)) := by rw [hAt.2, hAs.2]
    _ = μ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
      rw [← measureReal_sdiff
        (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst)) measurableSet_Ioc, hsets]

end ProbabilityTheory

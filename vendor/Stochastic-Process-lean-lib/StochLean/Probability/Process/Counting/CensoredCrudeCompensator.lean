/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoredCrudeRate
public import StochLean.Probability.Process.Counting.CensoredRNDensity

/-! # Actual crude-rate compensation with arbitrary dependent censoring

The crude rate is the right limit of the actual conditional-window quotient,
using joint arrival/censoring survival. The limit has been proved to exist
at almost every nonnegative time under absolute continuity of the actual
real arrival law; the definition's totalization elsewhere is not a claim
that the limit exists there. Zero survival uses real totalized division,
and is not interpreted as a conditional probability.

The true crude rate agrees almost everywhere in time with the actual cause
RN density divided by joint survival. This common time event identifies
every stopped primitive, hence the sole canonical compensator and the
local-martingale remainder in the genuine usual natural filtration of
both observed causes. No candidate compensator or supplied rate limit is
assumed. Censoring may depend arbitrarily on arrival, and ties are arrivals.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {T U : Ω → WithTop ℝ≥0}

/-- The actual crude right-window rate, totalized by the native filter limit.
Existence of this limit, and its conditional interpretation when survival
is positive, are separate conclusions rather than definition fields. -/
noncomputable def censoredCrudeRate (P : Measure Ω) (T U : Ω → WithTop ℝ≥0)
    (t : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun h : ℝ ↦
    (P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
      T ω < ((t + h).toNNReal : WithTop ℝ≥0) ∧
      (t.toNNReal : WithTop ℝ≥0) ≤ U ω} /
      P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
        (t.toNNReal : WithTop ℝ≥0) ≤ U ω}) / h)

/-- The actual crude rate equals the true arrival-before-censoring RN
density divided by joint survival at almost every nonnegative time.
No pointwise claim at every censoring atom is made. -/
theorem ae_censoredCrudeRate_eq_rnDeriv_div_survival [IsFiniteMeasure P]
    (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    let κ := (P.restrict {ω | T ω ≤ U ω}).map (fun ω ↦ ((T ω).untopA : ℝ))
    ∀ᵐ t : ℝ ∂volume, 0 ≤ t →
      censoredCrudeRate P T U t =
        (κ.rnDeriv volume t).toReal /
          P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
            (t.toNNReal : WithTop ℝ≥0) ≤ U ω} := by
  filter_upwards [ae_tendsto_censored_crude_window_rate hT hU hAC] with t ht hnonneg
  exact (ht hnonneg).limUnder_eq

open Classical in
/-- The sole actual censored-count compensator is the stopped integral
of the genuine crude right-window rate, without independence or an input
density/rate certificate. All observation times share one path event. -/
theorem predictableCompensator_censoredCount_eq_crudeRate_integral
    [IsProbabilityMeasure P] (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    let F := Filtration.natural _
      (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
    let hD := markedSingleJumpCount_compensator_domain
      (P := P) (hT.min hU) (measurableSet_le hT hU)
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
          censoredCrudeRate P T U x)
      P.completion := by
  apply (predictableCompensator_censoredCount_eq_rnDeriv_integral hT hU hAC).trans
  exact ae_of_all _ fun ω t ↦ by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_censoredCrudeRate_eq_rnDeriv_div_survival hT hU hAC] with x hx hmem
    have hu : (0 : ℝ) ≤
        ((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ) :=
      NNReal.coe_nonneg _
    rw [uIoc_of_le hu] at hmem
    exact (hx hmem.1.le).symm

open Classical in
/-- Subtracting the literal stopped crude-rate primitive from the actual
censored arrival count gives a local martingale in its genuine usual
observed-pair natural filtration. -/
theorem isLocalMartingale_censoredCount_sub_crudeRate_integral
    [IsProbabilityMeasure P] (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    let F := Filtration.natural _
      (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
    IsLocalMartingale
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        (if min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω then (1 : ℝ) else 0) -
          ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
            censoredCrudeRate P T U x)
      (F.usualAugmentation P) P.completion := by
  let F := Filtration.natural _
    (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
  let G := F.usualAugmentation P
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    if min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω then (1 : ℝ) else 0
  let A := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
      censoredCrudeRate P T U x
  have hD := markedSingleJumpCount_compensator_domain
    (P := P) (hT.min hU) (measurableSet_le hT hU)
  have hG : G.IsUsual P.completion := F.usualAugmentation_isUsual P
  let B := hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1 hG hD.2.1
  have hB := hD.2.2.hasLocallyIntegrableVariation.predictableCompensator_properties
    hD.1 hG hD.2.1
  have he : Indistinguishable B A P.completion :=
    predictableCompensator_censoredCount_eq_crudeRate_integral hT hU hAC
  have haA : Adapted G A := by
    intro t
    have hc : IsCompleteSubMeasurableSpace P.completion (G t) :=
      fun s hs ↦ G.mono bot_le s (hG.complete_initial s hs)
    exact hc.measurable_congr_ae (hB.1.stronglyAdapted.adapted t) (he.ae_eq t)
  let C₀ := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    if min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ ω ∈ {a : Ω | T a ≤ U a}
      then (1 : ℝ) else 0
  have heC : C₀ = C := by
    funext t ω
    dsimp only [C₀, C]
    by_cases hj : min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω
    · have hj₀ : min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧
          ω ∈ {a : Ω | T a ≤ U a} := ⟨hj.1, hj.2⟩
      rw [if_pos hj₀, if_pos hj]
    · have hj₀ : ¬ (min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧
          ω ∈ {a : Ω | T a ≤ U a}) := fun h ↦ hj ⟨h.1, h.2⟩
      rw [if_neg hj₀, if_neg hj]
  have haC : Adapted G C := by
    have ha₀ : Adapted G C₀ := hD.1
    rw [heC] at ha₀
    exact ha₀
  have hM : IsLocalMartingale (C₀ - B) G P.completion := hB.2.2.2.2
  rw [heC] at hM
  apply hM.congr hG (haC.sub haA)
  filter_upwards [he] with ω hω t
  change C t ω - B t ω = C t ω - A t ω
  rw [hω t]

end ProbabilityTheory

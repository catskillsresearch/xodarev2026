/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.MarkedSingleJumpDensity
public import StochLean.Probability.Process.Counting.CensoringWindow

/-! # The actual density-integral compensator under dependent censoring

The density is that of the original arrival law restricted to arrival
before or at censoring. Its denominator is the joint closed survival of
arrival and censoring, not the restricted arrival survival. The selected
compensator is taken in the genuine usual natural filtration of both
observed causes, with the mark first revealed at the observation.

The proof identifies the actual cause submeasure and observation survival,
then consumes the marked density-integral compensation theorem. Ties,
initial atoms and infinite lifetimes are retained. No independence or
candidate compensator is assumed. Identification of this density ratio
with a printed crude small-window rate is a separate limiting question.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

open Classical in
/-- The actual censored-arrival compensator is the stopped cause-density
integral divided by joint observation survival. The density represents the
true restricted arrival law, with ties assigned to the arrival cause. -/
theorem predictableCompensator_censoredCount_eq_density_integral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {T U : Ω → WithTop ℝ≥0} {f : ℝ → ℝ}
    (hT : Measurable T) (hU : Measurable U) (hf : Measurable f)
    (hden : ∀ c : ℝ≥0,
      (((P.restrict {ω | T ω ≤ U ω}).map T).restrict
        (Ioc (0 : WithTop ℝ≥0) (c : WithTop ℝ≥0))).map
          (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
            (volume.restrict (Ioc (0 : ℝ) (c : ℝ))).withDensity
              (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ c : ℝ≥0, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (c : ℝ)), 0 ≤ f x) :
    let F := Filtration.natural _
      (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
    let hD := markedSingleJumpCount_compensator_domain
      (P := P) (hT.min hU) (measurableSet_le hT hU)
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
          f x / P.real {w | (x.toNNReal : WithTop ℝ≥0) ≤ T w ∧
            (x.toNNReal : WithTop ℝ≥0) ≤ U w})
      P.completion := by
  have hρ := (censored_arrival_submeasure_eq_and_le (P := P) hT hU).1
  have hden' : ∀ c : ℝ≥0,
      (((P.restrict {ω | T ω ≤ U ω}).map (fun ω ↦ min (T ω) (U ω))).restrict
        (Ioc (0 : WithTop ℝ≥0) (c : WithTop ℝ≥0))).map
          (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
            (volume.restrict (Ioc (0 : ℝ) (c : ℝ))).withDensity
              (fun x ↦ ENNReal.ofReal (f x)) := by
    intro c
    rw [hρ]
    exact hden c
  apply (predictableCompensator_markedSingleJumpCount_eq_density_integral
    (P := P) (hT.min hU) (measurableSet_le hT hU) hf hden' hfn).trans
  exact ae_of_all _ fun ω t ↦ by
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [measureReal_def, measureReal_def, censored_survival_measure_eq hT hU]

end ProbabilityTheory

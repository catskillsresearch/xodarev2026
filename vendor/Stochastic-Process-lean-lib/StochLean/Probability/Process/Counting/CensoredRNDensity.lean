/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoredDensity
public import StochLean.Probability.Process.Counting.LifetimeRealDensity

/-! # The actual RN-density censored compensator

Absolute continuity of the real arrival law makes its actual
arrival-before-censoring submeasure absolutely continuous as well.
Its genuine Radon--Nikodym derivative supplies all finite positive
restriction densities, rather than receiving a density certificate as
an input. The corresponding actual censored compensator is therefore
the integral of this RN density divided by joint closed survival.

The marked observation's natural filtration and sole compensator are the
existing owners. The arrival and censoring lifetimes need not be
independent. Absolute continuity of the real arrival law itself rules out
an arrival atom at infinity; no separate initial or terminal moment is
assumed. This result does not assert the small-window crude-rate identity.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

open Classical in
/-- The sole censored-count compensator is the literal integral of the
actual cause law's RN density divided by joint closed survival. Only
absolute continuity of the original real arrival law is required. -/
theorem predictableCompensator_censoredCount_eq_rnDeriv_integral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {T U : Ω → WithTop ℝ≥0} (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    let κ := (P.restrict {ω | T ω ≤ U ω}).map (fun ω ↦ ((T ω).untopA : ℝ))
    let F := Filtration.natural _
      (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
    let hD := markedSingleJumpCount_compensator_domain
      (P := P) (hT.min hU) (measurableSet_le hT hU)
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
          (κ.rnDeriv volume x).toReal /
            P.real {w | (x.toNNReal : WithTop ℝ≥0) ≤ T w ∧
              (x.toNNReal : WithTop ℝ≥0) ≤ U w})
      P.completion := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ρ := (P.restrict {ω | T ω ≤ U ω}).map T
  let κ := (P.restrict {ω | T ω ≤ U ω}).map (fun ω ↦ ((T ω).untopA : ℝ))
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hmap : ρ.map φ = κ := Measure.map_map hφ hT
  have hκle : κ ≤ P.map (fun ω ↦ ((T ω).untopA : ℝ)) :=
    Measure.map_mono Measure.restrict_le_self (hφ.comp hT)
  have hκAC : κ ≪ volume := (Measure.absolutelyContinuous_of_le hκle).trans hAC
  have hρAC : ρ.map φ ≪ volume := by
    rw [hmap]
    exact hκAC
  have hdata := measurable_nonneg_and_map_untopA_eq_withDensity_rnDeriv ρ hρAC
  dsimp only at hdata
  rw [hmap] at hdata
  have hden : ∀ c : ℝ≥0,
      (ρ.restrict (Ioc (0 : WithTop ℝ≥0) (c : WithTop ℝ≥0))).map φ =
        (volume.restrict (Ioc (0 : ℝ) (c : ℝ))).withDensity
          (fun x ↦ ENNReal.ofReal (κ.rnDeriv volume x).toReal) := by
    intro c
    have h := map_restrict_Ioc_untopA_eq_withDensity_rnDeriv ρ hρAC c
    dsimp only at h
    rw [hmap] at h
    exact h
  exact predictableCompensator_censoredCount_eq_density_integral hT hU hdata.1 hden
    (fun _ ↦ ae_of_all _ hdata.2.1)

end ProbabilityTheory

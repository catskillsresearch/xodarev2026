/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.LifetimeRealWindow
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Actual RN densities of finite positive lifetime restrictions

Absolute continuity of the original real-coordinate lifetime law gives its
native RN density. Finiteness of the law makes the extended density finite
almost everywhere before its real value is used to reconstruct that law.

The same single density represents every finite positive lifetime cap,
with restriction performed before the real-coordinate pushforward. The
actual absolute-continuity hypothesis first rules out mass at infinity;
only on the common finite-lifetime event is the real interval preimage
identified with its original lifetime interval. The arbitrary totalized
value at infinity is never treated as a finite observation.

No alternative density selector, assumed cap-density formula, probability
normalization, or pointwise density continuity is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- The native real RN density of the actual lifetime pushforward is
measurable and nonnegative and reconstructs the original real law. -/
theorem measurable_nonneg_and_map_untopA_eq_withDensity_rnDeriv
    (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]
    (hAC : μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) :
    let ν := μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))
    let f : ℝ → ℝ := fun x ↦ (ν.rnDeriv volume x).toReal
    Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  intro ν f
  have hfinite : ∀ᵐ x ∂volume, ν.rnDeriv volume x ≠ ∞ :=
    Measure.rnDeriv_ne_top ν volume
  have he : (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[volume] ν.rnDeriv volume := by
    filter_upwards [hfinite] with x hx
    exact ENNReal.ofReal_toReal hx
  refine ⟨(ν.measurable_rnDeriv volume).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  calc
    ν = volume.withDensity (ν.rnDeriv volume) :=
      (Measure.withDensity_rnDeriv_eq ν volume hAC).symm
    _ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) :=
      withDensity_congr_ae he.symm

/-- Restricting the original lifetime law to any finite positive cap and
then taking its real coordinate gives the restricted native RN density of
the full real law. No exceptional infinite value is moved into the cap. -/
theorem map_restrict_Ioc_untopA_eq_withDensity_rnDeriv
    (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]
    (hAC : μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) (c : ℝ≥0) :
    let ν := μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))
    let f : ℝ → ℝ := fun x ↦ (ν.rnDeriv volume x).toReal
    (μ.restrict (Ioc (0 : WithTop ℝ≥0) (c : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
      (volume.restrict (Ioc (0 : ℝ) (c : ℝ))).withDensity
        (fun x ↦ ENNReal.ofReal (f x)) := by
  intro ν f
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hTop : μ {⊤} = 0 := measure_top_eq_zero_of_absolutelyContinuous_map_untopA μ hAC
  have hfinite : ∀ᵐ v ∂μ, v ≠ ⊤ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hTop
  have hpre : φ ⁻¹' Ioc (0 : ℝ) (c : ℝ) =ᵐ[μ]
      Ioc (0 : WithTop ℝ≥0) (c : WithTop ℝ≥0) := by
    filter_upwards [hfinite] with v hv
    cases v using WithTop.recTopCoe with
    | top => exact (hv rfl).elim
    | coe a =>
        apply propext
        change (0 < (a : ℝ) ∧ (a : ℝ) ≤ (c : ℝ)) ↔
          ((0 : WithTop ℝ≥0) < (a : WithTop ℝ≥0) ∧
            (a : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0))
        simp only [← NNReal.coe_zero, NNReal.coe_lt_coe, NNReal.coe_le_coe,
          ← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_le_coe]
  have hν : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) :=
    (measurable_nonneg_and_map_untopA_eq_withDensity_rnDeriv μ hAC).2.2
  calc
    (μ.restrict (Ioc (0 : WithTop ℝ≥0) (c : WithTop ℝ≥0))).map φ =
        ν.restrict (Ioc (0 : ℝ) (c : ℝ)) := by
      symm
      change (μ.map φ).restrict (Ioc (0 : ℝ) (c : ℝ)) = _
      rw [Measure.restrict_map hφ measurableSet_Ioc, Measure.restrict_congr_set hpre]
    _ = (volume.restrict (Ioc (0 : ℝ) (c : ℝ))).withDensity
        (fun x ↦ ENNReal.ofReal (f x)) := by
      rw [hν, restrict_withDensity measurableSet_Ioc]

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulus
public import Mathlib.Probability.Martingale.Basic

/-! # Conditional differences between two future grid values

Two forward conditional decrements of a supermartingale are nonnegative. Their
difference is therefore bounded in norm by the sum of the two actual conditional
moduli. Conditioning this inequality again yields the predictable energy bound.
The result concerns each fixed triple of times, not an uncountable AE intersection.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  {δ η : ℝ≥0} {G H : Ω → ℝ≥0∞} {t u v : ℝ≥0}

theorem Supermartingale.conditional_decrement_nonneg
    (hX : Supermartingale X F P) (htu : t ≤ u) :
    0 ≤ᵐ[P] P[X t - X u | F t] := by
  have he := condExp_sub (hX.integrable t) (hX.integrable u) (F t)
  rw [condExp_of_stronglyMeasurable (F.le t) (hX.stronglyAdapted t)
    (hX.integrable t)] at he
  filter_upwards [he, hX.2.1 t u htu] with ω heω hω
  simpa only [heω, Pi.zero_apply, Pi.sub_apply] using sub_nonneg.mpr hω

theorem Supermartingale.norm_condExp_sub_le_globalConditionalModuli
    (hX : Supermartingale X F P)
    (hG : IsGlobalConditionalIncrementModulus F P X δ G)
    (hH : IsGlobalConditionalIncrementModulus F P X η H)
    (hGfin : ∀ᵐ ω ∂P, G ω ≠ ∞) (hHfin : ∀ᵐ ω ∂P, H ω ≠ ∞)
    (htu : t ≤ u) (hu : u ≤ t + δ) (htv : t ≤ v) (hv : v ≤ t + η) :
    ∀ᵐ ω ∂P, ‖P[X u - X v | F t] ω‖ ≤ (G ω).toReal + (H ω).toReal := by
  have hident : X u - X v = (X t - X v) - (X t - X u) := by
    funext ω
    change X u ω - X v ω = (X t ω - X v ω) - (X t ω - X u ω)
    ring
  have he := condExp_sub ((hX.integrable t).sub (hX.integrable v))
    ((hX.integrable t).sub (hX.integrable u)) (F t)
  rw [← hident] at he
  filter_upwards [hG.conditional_increment_le htu hu, hH.conditional_increment_le htv hv,
    hX.conditional_decrement_nonneg htu, hX.conditional_decrement_nonneg htv,
    hGfin, hHfin, he] with ω hgu hhv hnu hnv hgf hhf heω
  have hbu : P[X t - X u | F t] ω ≤ (G ω).toReal := by
    simpa only [ENNReal.toReal_ofReal hnu] using ENNReal.toReal_mono hgf hgu
  have hbv : P[X t - X v | F t] ω ≤ (H ω).toReal := by
    simpa only [ENNReal.toReal_ofReal hnv] using ENNReal.toReal_mono hhf hhv
  rw [heω, Pi.sub_apply]
  calc
    _ ≤ ‖P[X t - X v | F t] ω‖ + ‖P[X t - X u | F t] ω‖ := norm_sub_le _ _
    _ = P[X t - X v | F t] ω + P[X t - X u | F t] ω := by
      rw [Real.norm_of_nonneg hnv, Real.norm_of_nonneg hnu]
    _ ≤ (G ω).toReal + (H ω).toReal := by linarith only [hbu, hbv]

theorem Supermartingale.norm_condExp_sub_le_condExp_globalConditionalModuli
    (hX : Supermartingale X F P)
    (hG : IsGlobalConditionalIncrementModulus F P X δ G)
    (hH : IsGlobalConditionalIncrementModulus F P X η H)
    (hGfin : ∀ᵐ ω ∂P, G ω ≠ ∞) (hHfin : ∀ᵐ ω ∂P, H ω ≠ ∞)
    (hGi : Integrable (fun ω ↦ (G ω).toReal) P)
    (hHi : Integrable (fun ω ↦ (H ω).toReal) P)
    (htu : t ≤ u) (hu : u ≤ t + δ) (htv : t ≤ v) (hv : v ≤ t + η) :
    ∀ᵐ ω ∂P, ‖P[X u - X v | F t] ω‖ ≤
      P[(fun ω ↦ (G ω).toReal + (H ω).toReal) | F t] ω := by
  have hi : Integrable (fun ω ↦ ‖P[X u - X v | F t] ω‖) P := integrable_condExp.norm
  have hb := hX.norm_condExp_sub_le_globalConditionalModuli hG hH hGfin hHfin htu hu htv hv
  have hce := condExp_mono (m := F t) hi (hGi.add hHi) hb
  rwa [condExp_of_stronglyMeasurable (F.le t) stronglyMeasurable_condExp.norm hi] at hce

end MeasureTheory

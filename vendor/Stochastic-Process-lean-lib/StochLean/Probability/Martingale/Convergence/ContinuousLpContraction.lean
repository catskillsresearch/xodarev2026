/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousClosure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Extending Lp convergence from integer times to the entire half-line

Conditional-expectation contraction controls every later coordinate by an
earlier integer-time error. This is an actual whole-half-line Lp convergence
argument. Almost-sure half-line convergence is not inferred from Lp convergence.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} {p : ℝ≥0∞}

theorem eLpNorm_increment_le_closing_error_of_one_le
    (hX : Martingale X F P) (hp : 1 ≤ p) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (X t - X s) p P ≤ eLpNorm (X s - Z) p P := by
  have hXs : StronglyMeasurable[F t] (X s) := (hX.stronglyAdapted s).mono (F.mono hst)
  have hce : P[Z - X s | F t] =ᵐ[P] X t - X s := by
    calc
      _ =ᵐ[P] P[Z | F t] - P[X s | F t] := condExp_sub hZ (hX.integrable s) (F t)
      _ =ᵐ[P] X t - X s := by
        rw [condExp_of_stronglyMeasurable (F.le t) hXs (hX.integrable s)]
        exact (hclose t).symm.sub Filter.EventuallyEq.rfl
  rw [← eLpNorm_congr_ae hce, eLpNorm_sub_comm (X s) Z]
  exact eLpNorm_condExp_le_eLpNorm _ hp

theorem eLpNorm_sub_closing_le_two_of_one_le
    (hX : Martingale X F P) (hp : 1 ≤ p) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (X t - Z) p P ≤ 2 * eLpNorm (X s - Z) p P := by
  have hb := hX.eLpNorm_increment_le_closing_error_of_one_le hp hZ hclose hst
  have he : X t - Z = (X t - X s) + (X s - Z) := by
    ext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hm (t : ℝ≥0) : AEStronglyMeasurable (X t) P :=
    ((hX.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
  rw [he]
  calc
    _ ≤ eLpNorm (X t - X s) p P + eLpNorm (X s - Z) p P :=
      eLpNorm_add_le ((hm t).sub (hm s)) ((hm s).sub hZ.aestronglyMeasurable) hp
    _ ≤ eLpNorm (X s - Z) p P + eLpNorm (X s - Z) p P := add_le_add hb le_rfl
    _ = _ := (two_mul _).symm

theorem tendsto_eLpNorm_of_integer_closing
    (hX : Martingale X F P) (hp : 1 ≤ p) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hn : Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) p P) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) p P) atTop (𝓝 0) := by
  have hmul : Tendsto (fun n : ℕ ↦ 2 * eLpNorm (X (n : ℝ≥0) - Z) p P) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hn
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨n, hnε⟩ := (ENNReal.tendsto_nhds_zero.mp hmul ε hε).exists
  filter_upwards [eventually_ge_atTop (n : ℝ≥0)] with t ht
  exact (hX.eLpNorm_sub_closing_le_two_of_one_le hp hZ hclose ht).trans hnε

end MeasureTheory.Martingale

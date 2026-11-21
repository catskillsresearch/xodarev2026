/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Caglad
public import StochLean.Probability.Process.Measurability.Progressive
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # Borel measurability of left-continuous and caglad paths

The original deterministic path is Borel measurable; no bound, right limit,
finite variation, or probabilistic exceptional set is needed. The existing
left-continuous progressive-measurability theorem on a one-point sample
space gives measurable paths stopped at integer horizons. These eventually
agree with the original path at every time, so their pointwise limit is
measurable. No new grid or path version is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem IsLeftContinuousPath.measurable {x : ℝ≥0 → ℝ}
    (hx : IsLeftContinuousPath x) : Measurable x := by
  let F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) := ⊥
  have hp : IsStronglyProgressive F (fun t (_ : Unit) ↦ x t) :=
    (stronglyAdapted_const' F x).isStronglyProgressive_of_leftContinuous (fun _ ↦ hx)
  have hm (T : ℝ≥0) : Measurable (fun t : ℝ≥0 ↦ x (min t T)) := by
    exact ((hp T).comp_measurable
      (((measurable_id.min measurable_const).subtype_mk
        (h := fun t : ℝ≥0 ↦ by change min t T ≤ T; exact min_le_right _ _)).prodMk
          (measurable_const (a := ())))).measurable
  apply measurable_of_tendsto_metrizable (fun n : ℕ ↦ hm (n : ℝ≥0))
  apply tendsto_pi_nhds.mpr
  intro t
  have he : (fun n : ℕ ↦ x (min t (n : ℝ≥0))) =ᶠ[atTop] fun _ ↦ x t := by
    obtain ⟨N, hN⟩ := exists_nat_ge t
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [min_eq_left (hN.trans (Nat.cast_le.mpr hn))]
  exact tendsto_const_nhds.congr' he.symm

theorem IsCagladPath.measurable {x : ℝ≥0 → ℝ} (hx : IsCagladPath x) : Measurable x :=
  hx.1.measurable

end ProbabilityTheory

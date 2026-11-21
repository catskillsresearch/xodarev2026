/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Potentials

A potential is a nonnegative supermartingale whose expectations vanish at
infinity. This analytic predicate works in discrete and continuous time;
the continuous-time source additionally requires cadlag paths. Adaptation
and integrability are supplied by the supermartingale hypothesis.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {F : Filtration ι mΩ} {X : ι → Ω → ℝ}

/-- Nonnegative supermartingality with expectations tending to zero.
Continuous-time path regularity is a separate hypothesis. -/
structure IsPotential (X : ι → Ω → ℝ) (F : Filtration ι mΩ) (P : Measure Ω) : Prop where
  supermartingale : Supermartingale X F P
  nonneg : ∀ t, ∀ᵐ ω ∂P, 0 ≤ X t ω
  tendsto_integral : Tendsto (fun t ↦ ∫ ω, X t ω ∂P) atTop (𝓝 0)

theorem IsPotential.tendsto_eLpNorm (hX : IsPotential X F P) :
    Tendsto (fun t ↦ eLpNorm (X t) 1 P) atTop (𝓝 0) := by
  have he (t) : eLpNorm (X t) 1 P = ENNReal.ofReal (∫ ω, X t ω ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.supermartingale.integrable t)]
    congr 1
    exact integral_congr_ae ((hX.nonneg t).mono fun _ hω ↦ Real.norm_of_nonneg hω)
  simp_rw [he]
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp hX.tendsto_integral
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using ht

end ProbabilityTheory

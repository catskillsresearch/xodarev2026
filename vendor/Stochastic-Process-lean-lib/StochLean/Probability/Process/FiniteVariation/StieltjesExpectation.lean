/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Stieltjes
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Actual expected Stieltjes increments of a martingale difference

Two increasing adapted paths whose difference is a martingale have the same
expected Stieltjes mass on predictable deterministic rectangles. This is
proved directly from their actual kernels and the martingale set-integral
identity, before any compensator theorem or predictable-integrand duality.
Initial values are arbitrary: Stieltjes measures record positive-time
increments and have no atom at zero.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X Y : ℝ≥0 → Ω → ℝ}

/-- The existing variation kernel of an increasing path records its actual
increment, not a new random measure or a normalized initial value. -/
theorem totalVariationKernel_Ioc_of_monotone (ha : Adapted F X)
    (hv : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hr : ∀ ω, IsRightContinuousPath (X · ω)) (hm : ∀ ω, Monotone (X · ω))
    {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    totalVariationKernel X ha hv hr ω (Ioc s t) = ENNReal.ofReal (X t ω - X s ω) := by
  rw [totalVariationKernel_Ioc X ha hv hr hst]
  simpa only [univ_inter] using
    ((hm ω).monotoneOn univ).eVariationOn_eq (mem_univ s) (mem_univ t)

/-- Equality of expected actual Stieltjes masses on `(s,t]` restricted to an
event already known at `s`. Only finite-time L1 and the true martingale
difference are used; no compensator or whole predictable duality is assumed. -/
theorem lintegral_totalVariationKernel_Ioc_eq_of_martingale_sub
    {P : Measure Ω} [IsFiniteMeasure P]
    (haX : Adapted F X) (hvX : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (haY : Adapted F Y) (hvY : ∀ ω, LocallyBoundedVariationOn (Y · ω) univ)
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) (hmY : ∀ ω, Monotone (Y · ω))
    (hiX : ∀ t, Integrable (X t) P) (hiY : ∀ t, Integrable (Y t) P)
    (hM : Martingale (X - Y) F P) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[F s] E) :
    (∫⁻ ω in E, totalVariationKernel X haX hvX hrX ω (Ioc s t) ∂P) =
      ∫⁻ ω in E, totalVariationKernel Y haY hvY hrY ω (Ioc s t) ∂P := by
  simp_rw [totalVariationKernel_Ioc_of_monotone haX hvX hrX hmX hst,
    totalVariationKernel_Ioc_of_monotone haY hvY hrY hmY hst]
  have hiXd : Integrable (fun ω ↦ X t ω - X s ω) (P.restrict E) :=
    ((hiX t).sub (hiX s)).integrableOn
  have hiYd : Integrable (fun ω ↦ Y t ω - Y s ω) (P.restrict E) :=
    ((hiY t).sub (hiY s)).integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal hiXd
    (ae_of_all _ fun ω ↦ sub_nonneg.mpr (hmX ω hst)),
    ← ofReal_integral_eq_lintegral_ofReal hiYd
      (ae_of_all _ fun ω ↦ sub_nonneg.mpr (hmY ω hst))]
  congr 1
  have hmean := hM.setIntegral_eq hst hE
  simp only [Pi.sub_apply] at hmean
  rw [integral_sub (hiX s).integrableOn (hiY s).integrableOn,
    integral_sub (hiX t).integrableOn (hiY t).integrableOn] at hmean
  rw [integral_sub (hiX t).integrableOn (hiX s).integrableOn,
    integral_sub (hiY t).integrableOn (hiY s).integrableOn]
  linarith only [hmean]

end ProbabilityTheory

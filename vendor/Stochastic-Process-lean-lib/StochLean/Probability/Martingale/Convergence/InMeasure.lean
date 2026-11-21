/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Coordinatewise probability limits of uniformly integrable martingales

Uniform integrability is required across the approximating sequence at each
fixed time, not uniformly over the whole time axis.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω T : Type*} [Preorder T] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration T mΩ}
  [SigmaFiniteFiltration P F] {X : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}

theorem martingale_of_tendstoInMeasure_uniformIntegrable
    (hX : ∀ n, Martingale (X n) F P) (ha : StronglyAdapted F Y)
    (hui : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hu : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Y t)) : Martingale Y F P := by
  have hi (t : T) : Integrable (Y t) P := (hui t).integrable_of_tendstoInMeasure (hu t)
  have hLp (t : T) : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl (by simp) (hui t).1
      (memLp_one_iff_integrable.mpr (hi t)) (hui t).2.1 (hu t)
  refine ⟨ha, fun s t hst ↦ ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun _ _ _ ↦ (hi s).integrableOn) ?_ (ha s).aestronglyMeasurable
  intro A hA _
  have hs := tendsto_setIntegral_of_L1' (Y s) (hi s).aestronglyMeasurable
    (Eventually.of_forall (fun n ↦ (hX n).integrable s)) (hLp s) A
  have ht := tendsto_setIntegral_of_L1' (Y t) (hi t).aestronglyMeasurable
    (Eventually.of_forall (fun n ↦ (hX n).integrable t)) (hLp t) A
  have heq (n : ℕ) : (∫ ω in A, X n s ω ∂P) = ∫ ω in A, X n t ω ∂P :=
    (hX n).setIntegral_eq hst hA
  exact tendsto_nhds_unique hs (ht.congr' (Eventually.of_forall fun n ↦ (heq n).symm))

end MeasureTheory

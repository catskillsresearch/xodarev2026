/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.InMeasure

/-! # Coordinatewise probability limits of uniformly integrable supermartingales

At each fixed time, uniform integrability of the approximating sequence and
convergence in measure give actual L1 convergence. Event-integral inequalities
then pass to the limit. Uniform integrability across all times, a cadlag limit,
or a martingale equality is not required.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω T : Type*} [Preorder T] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration T mΩ}
  [SigmaFiniteFiltration P F] {X : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}

/-- Coordinatewise probability convergence with coordinatewise uniform
integrability preserves the genuine supermartingale inequalities. -/
theorem supermartingale_of_tendstoInMeasure_uniformIntegrable
    (hX : ∀ n, Supermartingale (X n) F P) (ha : StronglyAdapted F Y)
    (hui : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hu : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Y t)) :
    Supermartingale Y F P := by
  have hi (t : T) : Integrable (Y t) P := (hui t).integrable_of_tendstoInMeasure (hu t)
  have hLp (t : T) : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top (hui t).1
      (memLp_one_iff_integrable.mpr (hi t)) (hui t).2.1 (hu t)
  have hneg : Submartingale (-Y) F P := by
    apply submartingale_of_setIntegral_le ha.neg (fun t ↦ (hi t).neg)
    intro s t hst A hA
    have hs := tendsto_setIntegral_of_L1' (Y s) (hi s).aestronglyMeasurable
      (Eventually.of_forall fun n ↦ (hX n).integrable s) (hLp s) A
    have ht := tendsto_setIntegral_of_L1' (Y t) (hi t).aestronglyMeasurable
      (Eventually.of_forall fun n ↦ (hX n).integrable t) (hLp t) A
    have he : (∫ ω in A, Y t ω ∂P) ≤ ∫ ω in A, Y s ω ∂P :=
      le_of_tendsto_of_tendsto' ht hs (fun n ↦ (hX n).setIntegral_le hst hA)
    change (∫ ω in A, -Y s ω ∂P) ≤ ∫ ω in A, -Y t ω ∂P
    simpa only [integral_neg] using neg_le_neg he
  simpa only [neg_neg] using hneg.neg

end MeasureTheory

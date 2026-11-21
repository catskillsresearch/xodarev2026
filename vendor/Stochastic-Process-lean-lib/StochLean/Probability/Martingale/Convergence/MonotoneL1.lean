/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.MonotonePaths
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations
public import Mathlib.Probability.Martingale.Convergence

/-! # Integrable terminal limits of increasing nonnegative processes

Increasing paths and a uniform first-moment bound give an integrable terminal
variable dominating every coordinate, hence UI and L1 convergence. All path
inequalities hold on one common event; no L2 or integrable supremum premise
is assumed. This is used for the actual discrete Doob compensating process.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem HasMonotonePaths.exists_integrable_limit_of_nonneg_of_integral_bounded
    (hm : HasMonotonePaths X P) (ha : Adapted F X) (hi : ∀ n, Integrable (X n) P)
    (hn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω) {C : ℝ} (hb : ∀ n, (∫ ω, X n ω ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, (∀ n, X n ω ≤ Z ω) ∧ Tendsto (fun n ↦ X n ω) atTop (𝓝 (Z ω))) ∧
      UniformIntegrable X 1 P ∧
      Tendsto (fun n ↦ eLpNorm (X n - Z) 1 P) atTop (𝓝 0) := by
  have hS := hm.submartingale ha hi
  have hbound (n : ℕ) : eLpNorm (X n) 1 P ≤ (Real.toNNReal C : ℝ≥0∞) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    have he : (∫ ω, ‖X n ω‖ ∂P) = ∫ ω, X n ω ∂P :=
      integral_congr_ae ((hn n).mono fun _ hω ↦ Real.norm_of_nonneg hω)
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hb n)
  let Z := F.limitProcess X P
  have hiZ : Integrable Z P := memLp_one_iff_integrable.mp (hS.memLp_limitProcess hbound)
  have hl := hS.ae_tendsto_limitProcess hbound
  have hle : ∀ᵐ ω ∂P, ∀ n, X n ω ≤ Z ω := by
    filter_upwards [hm, hl] with ω hmω hlω n
    exact hmω.ge_of_tendsto hlω n
  have hu : UniformIntegrable X 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hiZ)).mono_norm (fun n ↦ (hi n).aestronglyMeasurable)
    intro n
    filter_upwards [hn n, hle] with ω hnω hleω
    rw [Real.norm_of_nonneg hnω, Real.norm_of_nonneg (hnω.trans (hleω n))]
    exact hleω n
  exact ⟨Z, hiZ, hle.and hl, hu, hS.tendsto_eLpNorm_one_limitProcess hu⟩

end ProbabilityTheory

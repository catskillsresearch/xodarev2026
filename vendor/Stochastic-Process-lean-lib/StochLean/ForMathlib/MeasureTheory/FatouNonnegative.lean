/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Integrable nonnegative limits from uniformly bounded first moments

A direct consequence of native Lp Fatou, on arbitrary measure spaces. The
limit's integrability is a conclusion, not a premise hidden in a real integral.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem integrable_and_integral_le_of_nonneg_ae_tendsto
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hi : ∀ n, Integrable (f n) P) (hn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ f n ω)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)))
    (hC : 0 ≤ C) (hb : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    Integrable g P ∧ (∫ ω, g ω ∂P) ≤ C := by
  have hg : ∀ᵐ ω ∂P, 0 ≤ g ω := by
    filter_upwards [hl, ae_all_iff.mpr hn] with ω hlω hnω
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlω hnω
  have hnorm (n : ℕ) : eLpNorm (f n) 1 P ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    have he : (∫ ω, ‖f n ω‖ ∂P) = ∫ ω, f n ω ∂P :=
      integral_congr_ae ((hn n).mono fun _ hω ↦ Real.norm_of_nonneg hω)
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hlim : eLpNorm g 1 P ≤ ENNReal.ofReal C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hnorm)
      (fun n ↦ (hi n).aestronglyMeasurable) hl
  have hgi : Integrable g P := memLp_one_iff_integrable.mp
    ⟨aestronglyMeasurable_of_tendsto_ae _ (fun n ↦ (hi n).aestronglyMeasurable) hl,
      hlim.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hgi, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hgi] at hlim
  have he : (∫ ω, ‖g ω‖ ∂P) = ∫ ω, g ω ∂P :=
    integral_congr_ae (hg.mono fun _ hω ↦ Real.norm_of_nonneg hω)
  rw [he] at hlim
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hlim

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Signed Fatou control with convergent lower bounds

Subtracting an almost-everywhere and L1 convergent lower sequence reduces a
signed limit comparison to nonnegative Fatou. The upper sequence need not be
uniformly integrable or converge in L1. The proof works on any measure space.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem integral_le_of_ae_tendsto_of_L1_lower_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ} {C : ℝ}
    (hfi : ∀ n, Integrable (f n) P) (hgi : ∀ n, Integrable (g n) P)
    (hFi : Integrable F P) (hGi : Integrable G P)
    (hf : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω) atTop (𝓝 (F ω)))
    (hg : ∀ᵐ ω ∂P, Tendsto (fun n ↦ g n ω) atTop (𝓝 (G ω)))
    (hgL1 : Tendsto (fun n ↦ eLpNorm (g n - G) 1 P) atTop (𝓝 0))
    (hle : ∀ n, g n ≤ᵐ[P] f n) (hC : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    (∫ ω, F ω ∂P) ≤ C := by
  have hn (n) : 0 ≤ᵐ[P] f n - g n := (hle n).mono fun _ hω ↦ sub_nonneg.mpr hω
  have hN : ∀ᵐ ω ∂P, ∀ n, g n ω ≤ f n ω := eventually_countable_forall.mpr hle
  have hFG : 0 ≤ᵐ[P] F - G := by
    filter_upwards [hf, hg, hN] with ω hfω hgω hω
    exact sub_nonneg.mpr (le_of_tendsto_of_tendsto' hgω hfω hω)
  have hd : ∀ᵐ ω ∂P, Tendsto (fun n ↦ ENNReal.ofReal ((f n - g n) ω)) atTop
      (𝓝 (ENNReal.ofReal ((F - G) ω))) := by
    filter_upwards [hf, hg] with ω hfω hgω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hfω.sub hgω)
  have hFatou : (∫⁻ ω, ENNReal.ofReal ((F - G) ω) ∂P) ≤
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal ((f n - g n) ω) ∂P) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal ((f n - g n) ω)) atTop ∂P :=
        lintegral_congr_ae (hd.mono fun _ hω ↦ hω.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun n ↦
        ((hfi n).sub (hgi n)).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have he (n) : (∫⁻ ω, ENNReal.ofReal ((f n - g n) ω) ∂P) =
      ENNReal.ofReal ((∫ ω, f n ω ∂P) - ∫ ω, g n ω ∂P) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((hfi n).sub (hgi n)) (hn n)]
    simp only [Pi.sub_apply, integral_sub (hfi n) (hgi n)]
  have hGint := tendsto_integral_of_L1' G hGi.aestronglyMeasurable
    (Eventually.of_forall hgi) hgL1
  have hupper : Tendsto (fun n ↦ ENNReal.ofReal (C - ∫ ω, g n ω ∂P)) atTop
      (𝓝 (ENNReal.ofReal (C - ∫ ω, G ω ∂P))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub hGint)
  have hbound := hFatou.trans (liminf_le_liminf (Eventually.of_forall fun n ↦
    (he n).trans_le (ENNReal.ofReal_le_ofReal (sub_le_sub_right (hC n) _))))
  rw [hupper.liminf_eq, ← ofReal_integral_eq_lintegral_ofReal (hFi.sub hGi) hFG] at hbound
  simp only [Pi.sub_apply, integral_sub hFi hGi] at hbound
  have hCG : (∫ ω, G ω ∂P) ≤ C := by
    apply le_of_tendsto hGint
    exact Eventually.of_forall fun n ↦ (integral_mono_ae (hgi n) (hfi n) (hle n)).trans (hC n)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hCG)).mp hbound
  linarith

end MeasureTheory

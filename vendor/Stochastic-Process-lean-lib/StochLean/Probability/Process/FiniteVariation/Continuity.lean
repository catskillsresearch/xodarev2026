/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CagladIntegral
public import StochLean.Analysis.PathVariation.StieltjesIntegralContinuity

/-! # Pathwise locality and uniform convergence of FV integrals

Identical integrator/integrand paths have identical integral paths. Uniform
convergence on a compact horizon passes through the pathwise integral. The
common-event version requires no expected-variation bound.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

theorem finiteVariationIntegral_congr_path (Y : ℝ≥0 → Ω → ℝ)
    (hyv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ Y t ω) univ)
    (hyr : ∀ ω, IsRightContinuousPath (fun t ↦ Y t ω))
    {H G : ℝ≥0 → Ω → ℝ} {ω : Ω} (hXY : ∀ t, X t ω = Y t ω) (hHG : ∀ t, H t ω = G t ω) :
    ∀ t, finiteVariationIntegral X hv hr H t ω = finiteVariationIntegral Y hyv hyr G t ω :=
  congrFun (pathStieltjesIntegral_congr (hx := hv ω) (hr := hr ω)
    (hy := hyv ω) (hyr := hyr ω) (funext hXY) (funext hHG))

theorem indistinguishable_finiteVariationIntegral {P : Measure Ω}
    (Y : ℝ≥0 → Ω → ℝ)
    (hyv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ Y t ω) univ)
    (hyr : ∀ ω, IsRightContinuousPath (fun t ↦ Y t ω))
    {H G : ℝ≥0 → Ω → ℝ} (hXY : Indistinguishable X Y P) (hHG : Indistinguishable H G P) :
    Indistinguishable (finiteVariationIntegral X hv hr H)
      (finiteVariationIntegral Y hyv hyr G) P := by
  filter_upwards [hXY, hHG] with ω hω hHω
  exact finiteVariationIntegral_congr_path X hv hr Y hyv hyr hω hHω

theorem norm_finiteVariationIntegral_sub_le {H G : ℝ≥0 → Ω → ℝ} {T t : ℝ≥0} {ω : Ω}
    (hH : IntegrableOn (fun u ↦ H u ω) (Ioc 0 T)
      (totalVariationStieltjes (fun u ↦ X u ω) (hv ω) (hr ω)).measure)
    (hG : IntegrableOn (fun u ↦ G u ω) (Ioc 0 T)
      (totalVariationStieltjes (fun u ↦ X u ω) (hv ω) (hr ω)).measure)
    {C : ℝ} (hC : 0 ≤ C) (hHG : ∀ u ∈ Icc 0 T, ‖H u ω - G u ω‖ ≤ C) (ht : t ≤ T) :
    ‖finiteVariationIntegral X hv hr H t ω - finiteVariationIntegral X hv hr G t ω‖ ≤
      C * (|X 0 ω| + totalVariationProcess X T ω) :=
  norm_pathStieltjesIntegral_sub_le hH hG hC hHG ht

theorem tendstoUniformlyOn_finiteVariationIntegral {ι : Type*} {l : Filter ι}
    {H : ι → ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hH : ∀ i, IntegrableOn (fun u ↦ H i u ω) (Ioc 0 T)
      (totalVariationStieltjes (fun u ↦ X u ω) (hv ω) (hr ω)).measure)
    (hG : IntegrableOn (fun u ↦ G u ω) (Ioc 0 T)
      (totalVariationStieltjes (fun u ↦ X u ω) (hv ω) (hr ω)).measure)
    (hHG : TendstoUniformlyOn (fun i t ↦ H i t ω) (fun t ↦ G t ω) l (Icc 0 T)) :
    TendstoUniformlyOn (fun i t ↦ finiteVariationIntegral X hv hr (H i) t ω)
      (fun t ↦ finiteVariationIntegral X hv hr G t ω) l (Icc 0 T) :=
  tendstoUniformlyOn_pathStieltjesIntegral hH hG hHG

theorem tendstoUniformlyOn_finiteVariationIntegral_of_caglad
    {F : Filtration ℝ≥0 mΩ} {ι : Type*} {l : Filter ι}
    {H : ι → ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℝ}
    (hHa : ∀ i, Adapted F (H i)) (hHc : ∀ i ω, IsCagladPath (fun t ↦ H i t ω))
    (hGa : Adapted F G) (hGc : ∀ ω, IsCagladPath (fun t ↦ G t ω))
    {T : ℝ≥0} {ω : Ω}
    (hHG : TendstoUniformlyOn (fun i t ↦ H i t ω) (fun t ↦ G t ω) l (Icc 0 T)) :
    TendstoUniformlyOn (fun i t ↦ finiteVariationIntegral X hv hr (H i) t ω)
      (fun t ↦ finiteVariationIntegral X hv hr G t ω) l (Icc 0 T) :=
  tendstoUniformlyOn_finiteVariationIntegral X hv hr
    (fun i ↦ integrableOn_variationStieltjes_of_adapted_caglad X hv hr (hHa i) (hHc i) T ω)
    (integrableOn_variationStieltjes_of_adapted_caglad X hv hr hGa hGc T ω) hHG

theorem ae_locallyUniform_finiteVariationIntegral_of_caglad
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {H : ℕ → ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℝ}
    (hHa : ∀ i, Adapted F (H i)) (hHc : ∀ i ω, IsCagladPath (fun t ↦ H i t ω))
    (hGa : Adapted F G) (hGc : ∀ ω, IsCagladPath (fun t ↦ G t ω))
    (hHG : ∀ᵐ ω ∂P, ∀ T, TendstoUniformlyOn
      (fun i t ↦ H i t ω) (fun t ↦ G t ω) atTop (Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ T, TendstoUniformlyOn
      (fun i t ↦ finiteVariationIntegral X hv hr (H i) t ω)
      (fun t ↦ finiteVariationIntegral X hv hr G t ω) atTop (Icc 0 T) :=
  hHG.mono fun _ hω T ↦
    tendstoUniformlyOn_finiteVariationIntegral_of_caglad X hv hr hHa hHc hGa hGc (hω T)

end ProbabilityTheory

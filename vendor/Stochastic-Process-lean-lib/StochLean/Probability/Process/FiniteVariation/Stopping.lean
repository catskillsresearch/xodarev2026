/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CagladIntegral
public import StochLean.Analysis.PathVariation.StieltjesIntegralStopping
public import StochLean.Probability.Process.Stopping.Integrand
public import StochLean.Probability.Process.Path.Stopping

/-! # Stopping finite-variation integrals

Both stopping identities hold pathwise, with possibly infinite random times.
No stopping-time or integrability hypothesis is needed for these identities of
the totalized integrals. Source-domain regularity is proved separately.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

theorem locallyBoundedVariationOn_stoppedProcess
    (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    LocallyBoundedVariationOn (fun t ↦ stoppedProcess X τ t ω) univ := by
  cases hτ : τ ω with
  | top =>
      simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe] using hv ω
  | coe T =>
      simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using locallyBoundedVariationOn_comp_min (hv ω) T

theorem rightContinuous_stoppedProcess
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    IsRightContinuousPath (fun t ↦ stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top =>
      simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe] using hr ω
  | coe T =>
      simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using (hr ω).min_const T

theorem HasFiniteVariationPaths.stoppedProcess (hv : HasFiniteVariationPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasFiniteVariationPaths (stoppedProcess X τ) P := by
  filter_upwards [hv] with ω hω
  cases hτ : τ ω with
  | top =>
      simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
      simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using locallyBoundedVariationOn_comp_min hω T

theorem totalVariationProcess_stoppedProcess (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) :
    totalVariationProcess (stoppedProcess X τ) = stoppedProcess (totalVariationProcess X) τ := by
  funext t ω
  cases hτ : τ ω with
  | top => simp only [totalVariationProcess, MeasureTheory.stoppedProcess, hτ,
      min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
  | coe T =>
      simp only [totalVariationProcess, MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe]
      exact pathTotalVariation_comp_min (fun u ↦ X u ω) T t

variable (X) (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

theorem finiteVariationIntegral_stoppedProcess (H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    finiteVariationIntegral (stoppedProcess X τ) (locallyBoundedVariationOn_stoppedProcess hv τ)
      (rightContinuous_stoppedProcess hr τ) H =
        stoppedProcess (finiteVariationIntegral X hv hr H) τ := by
  funext t ω
  cases hτ : τ ω with
  | top =>
      simp only [finiteVariationIntegral, MeasureTheory.stoppedProcess, hτ,
        min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
  | coe T =>
      simp only [finiteVariationIntegral, MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe]
      exact pathStieltjesIntegral_comp_min (fun u ↦ X u ω) (hv ω) (hr ω) T (fun u ↦ H u ω) t

theorem finiteVariationIntegral_cutoffIntegrand (H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    finiteVariationIntegral X hv hr (cutoffIntegrand H τ) =
      stoppedProcess (finiteVariationIntegral X hv hr H) τ := by
  funext t ω
  cases hτ : τ ω with
  | top =>
      simp only [finiteVariationIntegral, cutoffIntegrand, hτ, le_top, if_true,
        MeasureTheory.stoppedProcess, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
  | coe T =>
      simp only [finiteVariationIntegral, cutoffIntegrand, hτ, WithTop.coe_le_coe,
        MeasureTheory.stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
      exact pathStieltjesIntegral_indicator_Iic (fun u ↦ X u ω) (hv ω) (hr ω) T (fun u ↦ H u ω) t

theorem isSemimartingale_finiteVariationIntegral_cutoffIntegrand
    {F : Filtration ℝ≥0 mΩ} [IsFiniteMeasure P] (ha : Adapted F X) (hF : F.IsUsual P)
    {H : ℝ≥0 → Ω → ℝ} (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsSemimartingale (finiteVariationIntegral X hv hr (cutoffIntegrand H τ)) F P :=
  isSemimartingale_finiteVariationIntegral_of_caglad X hv hr ha hF
    (adapted_cutoffIntegrand hHa hτ) (isCagladPath_cutoffIntegrand hHc τ)

end ProbabilityTheory

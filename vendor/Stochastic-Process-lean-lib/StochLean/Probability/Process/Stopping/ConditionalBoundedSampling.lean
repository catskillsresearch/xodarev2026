/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalCountableSampling
public import StochLean.Probability.Process.Stopping.Approximation
public import StochLean.Probability.Process.Measurability.Progressive
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded stopping-time sampling of dominated conditional projections

Countable upper stopping grids, conditional-expectation locality and dominated
right limits prove the sampling identity. The input is jointly measurable but
need not be adapted. No martingale or optional-projection theorem is presumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem sample_condExp_of_dominated_rightContinuous (σ : FiniteStoppingTime F)
    {T : ℝ≥0} (hσ : ∀ ω, σ ω ≤ T)
    (hmX : Measurable (Function.uncurry X)) (hpY : IsStronglyProgressive F Y)
    (hrX : HasRightContinuousPaths X P) (hrY : HasRightContinuousPaths Y P)
    {g : Ω → ℝ} (hg : Integrable g P)
    (hbX : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ g ω)
    (hbY : ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ g ω)
    (he : ∀ t, Y t =ᵐ[P] P[X t | F t]) :
    (fun ω ↦ Y (σ ω) ω) =ᵐ[P] P[(fun ω ↦ X (σ ω) ω) | σ.measurableSpace] := by
  have hmXσ (s : FiniteStoppingTime F) : AEStronglyMeasurable (fun ω ↦ X (s ω) ω) P := by
    have hms : Measurable[s.measurableSpace] s := s.isStoppingTime.measurable.untopD 0
    exact (hmX.comp
      ((hms.mono s.measurableSpace_le le_rfl).prodMk measurable_id)).aestronglyMeasurable
  have hmYσ (s : FiniteStoppingTime F) : StronglyMeasurable[s.measurableSpace]
      (fun ω ↦ Y (s ω) ω) :=
    (measurable_stoppedValue hpY s.isStoppingTime).stronglyMeasurable
  have hiX (t) : Integrable (X t) P := hg.mono'
    (hmX.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (hbX.mono fun _ hω ↦ hω t)
  have hiXσ (s : FiniteStoppingTime F) : Integrable (fun ω ↦ X (s ω) ω) P :=
    hg.mono' (hmXσ s) (hbX.mono fun ω hω ↦ hω (s ω))
  have hiYσ (s : FiniteStoppingTime F) : Integrable (fun ω ↦ Y (s ω) ω) P :=
    hg.mono' ((hmYσ s).mono s.measurableSpace_le).aestronglyMeasurable
      (hbY.mono fun ω hω ↦ hω (s ω))
  apply ae_eq_condExp_of_forall_setIntegral_eq σ.measurableSpace_le (hiXσ σ)
    (fun _ _ _ ↦ (hiYσ σ).integrableOn) ?_ (hmYσ σ).aestronglyMeasurable
  intro A hA _
  have hlim (Z : ℝ≥0 → Ω → ℝ)
      (hmZ : ∀ s : FiniteStoppingTime F, AEStronglyMeasurable (fun ω ↦ Z (s ω) ω) P)
      (hrZ : HasRightContinuousPaths Z P) (hbZ : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ g ω) :
      Tendsto (fun n ↦ ∫ ω in A, Z (σ.upperApprox T n ω) ω ∂P) atTop
        (𝓝 (∫ ω in A, Z (σ ω) ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence g
      (fun n ↦ (hmZ (σ.upperApprox T n)).restrict) hg.restrict
    · intro n
      exact ae_restrict_of_ae (hbZ.mono fun ω hω ↦ hω (σ.upperApprox T n ω))
    · apply ae_restrict_of_ae
      filter_upwards [hrZ] with ω hω
      exact (hω (σ ω)).tendsto.comp (σ.tendsto_upperApprox hσ ω)
  have heq (n : ℕ) :
      (∫ ω in A, Y (σ.upperApprox T n ω) ω ∂P) =
        ∫ ω in A, X (σ.upperApprox T n ω) ω ∂P := by
    have hle : σ.measurableSpace ≤ (σ.upperApprox T n).measurableSpace :=
      σ.isStoppingTime.measurableSpace_mono (σ.upperApprox T n).isStoppingTime
        (fun ω ↦ WithTop.coe_le_coe.mpr (σ.le_upperApprox hσ n ω))
    have hs := (σ.upperApprox T n).sample_condExp_of_countable_range
      (σ.countable_range_upperApprox T n) hiX (hiXσ _) he
    exact (integral_congr_ae (ae_restrict_of_ae hs)).trans
      (setIntegral_condExp (σ.upperApprox T n).measurableSpace_le (hiXσ _) (hle A hA))
  have hy := hlim Y
    (fun s ↦ ((hmYσ s).mono s.measurableSpace_le).aestronglyMeasurable) hrY hbY
  have hx := hlim X hmXσ hrX hbX
  exact tendsto_nhds_unique hy (hx.congr' (Eventually.of_forall fun n ↦ (heq n).symm))

theorem sample_condExp_of_dominated_rightContinuous_of_usual (σ : FiniteStoppingTime F)
    {T : ℝ≥0} (hσ : ∀ ω, σ ω ≤ T) (hF : F.IsUsual P)
    (hmX : Measurable (Function.uncurry X)) (haY : StronglyAdapted F Y)
    (hrX : HasRightContinuousPaths X P) (hrY : HasRightContinuousPaths Y P)
    {g : Ω → ℝ} (hg : Integrable g P)
    (hbX : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ g ω)
    (hbY : ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ g ω)
    (he : ∀ t, Y t =ᵐ[P] P[X t | F t]) :
    (fun ω ↦ Y (σ ω) ω) =ᵐ[P] P[(fun ω ↦ X (σ ω) ω) | σ.measurableSpace] := by
  obtain ⟨Z, hm, hpZ, hrZ⟩ :=
    haY.exists_isStronglyProgressive_modification_of_hasRightContinuousPaths hF hrY
  have hcZ : HasRightContinuousPaths Z P := Eventually.of_forall hrZ
  have hind := hm.indistinguishable_of_rightContinuous hrY hcZ
  have hbZ : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ g ω := by
    filter_upwards [hind, hbY] with ω hω hb t
    rw [← hω t]
    exact hb t
  have heZ := σ.sample_condExp_of_dominated_rightContinuous hσ hmX hpZ hrX hcZ hg hbX hbZ
    (fun t ↦ (hm t).symm.trans (he t))
  have heYZ : (fun ω ↦ Y (σ ω) ω) =ᵐ[P] (fun ω ↦ Z (σ ω) ω) :=
    hind.mono fun ω hω ↦ hω (σ ω)
  exact heYZ.trans heZ

end ProbabilityTheory.FiniteStoppingTime

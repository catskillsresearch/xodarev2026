/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUniformIntegrable

/-!
# Unbounded, almost-surely finite optional sampling

Bounded truncations converge eventually pointwise on the finite event. The
actual UI stopping families supply L1 convergence; conditional expectation
is an L1 contraction. Uniqueness of limits in measure gives the minimum
formula, and AE ordering gives optional sampling.

This is the AE-finite terminal case of Protter I.16. A possibly infinite
terminal stopping time needs an explicitly supplied terminal process value;
Mathlib's totalized evaluation at infinity is not that value.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem integrable_stoppedValue_of_ae_finite_continuous (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hp : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Integrable (stoppedValue X τ) P :=
  memLp_one_iff_integrable.mp ((hX.uniformIntegrable_stoppedValue_of_ae_finite_continuous hu
    hp hr (ι := Unit) (fun _ ↦ hτ) (fun _ ↦ hfinite)).memLp ())

/-- The terminal time is AE-finite, not necessarily bounded; the other time may be infinite. -/
theorem stoppedValue_min_ae_eq_condExp_of_ae_finite_continuous (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hp : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  let τn : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ min (τ ω) (n : ℝ≥0)
  let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ min (σ ω) (τn n ω)
  have hτn (n) : IsStoppingTime F (τn n) := hτ.min_const (n : ℝ≥0)
  have hρ (n) : IsStoppingTime F (ρ n) := hσ.min (hτn n)
  have hb (n) (ω) : τn n ω ≤ (n : ℝ≥0) := min_le_right _ _
  have hV := hX.uniformIntegrable_bounded_stoppedValue hu hp hr hτn
    (fun n ↦ ⟨(n : ℝ≥0), hb n⟩)
  have hU := hX.uniformIntegrable_bounded_stoppedValue hu hp hr hρ
    (fun n ↦ ⟨(n : ℝ≥0), fun _ ↦ (min_le_right _ _).trans (hb n _)⟩)
  have hVlim := ae_tendsto_stoppedValue_truncate (X := X) hfinite
  have hminfinite : ∀ᵐ ω ∂P, min (σ ω) (τ ω) ≠ ⊤ :=
    hfinite.mono (fun _ h ↦ ne_top_of_le_ne_top h (min_le_right _ _))
  have hUlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (ρ n) ω) atTop
      (𝓝 (stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) ω)) := by
    simpa only [ρ, τn, min_assoc] using
      (ae_tendsto_stoppedValue_truncate (X := X) hminfinite)
  have hi := hV.integrable_of_ae_tendsto hVlim
  have hVL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    hV.1 (hV.memLp_of_ae_tendsto hVlim) hV.2.1 hVlim
  have hbounded (n) : stoppedValue X (ρ n) =ᵐ[P]
      P[stoppedValue X (τn n) | hσ.measurableSpace] :=
    hX.stoppedValue_min_ae_eq_condExp_of_bounded hp hr hσ (hτn n) (hb n)
  have hnorm (n) : eLpNorm
      (stoppedValue X (ρ n) - P[stoppedValue X τ | hσ.measurableSpace]) 1 P ≤
      eLpNorm (stoppedValue X (τn n) - stoppedValue X τ) 1 P := by
    calc
      _ = eLpNorm (P[stoppedValue X (τn n) - stoppedValue X τ | hσ.measurableSpace]) 1 P := by
        apply eLpNorm_congr_ae
        exact ((hbounded n).sub EventuallyEq.rfl).trans
          (condExp_sub (memLp_one_iff_integrable.mp (hV.memLp n)) hi _).symm
      _ ≤ _ := eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hUL1 : Tendsto (fun n ↦ eLpNorm
      (stoppedValue X (ρ n) - P[stoppedValue X τ | hσ.measurableSpace]) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVL1
      (fun _ ↦ zero_le) hnorm
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae hU.1 hUlim)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hU.1
      integrable_condExp.aestronglyMeasurable hUL1)

theorem stoppedValue_ae_eq_condExp_of_ae_finite_continuous (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hp : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  refine EventuallyEq.trans ?_
    (hX.stoppedValue_min_ae_eq_condExp_of_ae_finite_continuous hu hp hr hσ hτ hfinite)
  filter_upwards [hle] with ω hω
  simp only [stoppedValue, min_eq_left hω]

theorem stoppedValue_ae_eq_condExp_of_ae_finite_usual (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  obtain ⟨Y, heq, hp, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  have hY := hX.congr hp.stronglyAdapted heq.ae_eq
  exact (heq.stoppedValue σ).trans
    ((hY.stoppedValue_ae_eq_condExp_of_ae_finite_continuous (hu.ae_eq heq.ae_eq)
      hp (ae_of_all _ hreg) hσ hτ hle hfinite).trans
        (condExp_congr_ae (heq.stoppedValue τ)).symm)

end MeasureTheory.Martingale

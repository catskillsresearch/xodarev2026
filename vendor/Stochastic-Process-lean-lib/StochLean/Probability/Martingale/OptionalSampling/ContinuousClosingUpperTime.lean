/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.FatouLowerL1
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousClosingIntegrability
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual

/-! # Unbounded upper stopping time for lower-closed supermartingales

The earlier stopping time is bounded; the later one can be infinite. Signed
Fatou is applied after subtracting the conditional expectations of the lower
closing input. Those lower bounds converge in L1 by native Levy upward
convergence. The original supermartingale is not assumed uniformly integrable.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Y Z : Ω → ℝ}

theorem condExp_actualLimit_stoppedValue_le_of_bounded_lower_time
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, σ ω ≤ T) :
    P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace] ≤ᵐ[P] stoppedValue X σ := by
  have hiσ := hX.integrable_stoppedValue_of_bounded hσ hb hr
  have hiτ := hX.integrable_stoppedValue_actualLimit_of_closing hF hr hY hclose hlim hτ
  have hmσ := (hX.stronglyAdapted.measurable_stoppedValue_of_usual hF hr hσ).stronglyMeasurable
  obtain ⟨N, hN⟩ := exists_nat_ge T
  let U (n : ℕ) (ω : Ω) : WithTop ℝ≥0 := min (τ ω) ((n + N : ℕ) : ℝ≥0)
  have hU (n) : IsStoppingTime F (U n) := hτ.min_const ((n + N : ℕ) : ℝ≥0)
  have hbU (n) (ω) : U n ω ≤ ((n + N : ℕ) : ℝ≥0) := min_le_right _ _
  have hσU (n) (ω) : σ ω ≤ U n ω := by
    apply le_min (hle ω)
    apply (hb ω).trans
    apply WithTop.coe_le_coe.mpr
    exact hN.trans (Nat.cast_le.mpr (by omega))
  let G : Filtration ℕ mΩ := ⟨fun n ↦ (hU n).measurableSpace, by
    intro i j hij
    apply (hU i).measurableSpace_mono (hU j)
    intro ω
    exact min_le_min_left _ (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (by omega))),
    fun n ↦ (hU n).measurableSpace_le⟩
  have hiU (n) : Integrable (stoppedValue X (U n)) P :=
    hX.integrable_stoppedValue_of_bounded (hU n) (hbU n) hr
  have hUlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (U n) ω) atTop
      (𝓝 (stoppedValueWithTerminal X Z τ ω)) := by
    filter_upwards [ae_tendsto_stoppedValue_truncate_withTerminal (τ := τ) hlim] with ω hω
    exact hω.comp (tendsto_add_atTop_nat N)
  have hset (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) :
      (∫ ω in A, stoppedValueWithTerminal X Z τ ω ∂P) ≤ ∫ ω in A, stoppedValue X σ ω ∂P := by
    have hgL1 : Tendsto (fun n ↦ eLpNorm
        (P[Y | G n] - P[Y | ⨆ n, G n]) 1 (P.restrict A)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_eLpNorm_condExp (ℱ := G) (μ := P) Y) (fun _ ↦ zero_le)
        (fun n ↦ eLpNorm_restrict_le _ _ _ _)
    apply integral_le_of_ae_tendsto_of_L1_lower_bound
      (fun n ↦ (hiU n).integrableOn)
      (fun _ ↦ (integrable_condExp : Integrable P[Y | G _] P).integrableOn)
      hiτ.integrableOn (integrable_condExp : Integrable P[Y | ⨆ n, G n] P).integrableOn
      (ae_restrict_of_ae hUlim) (ae_restrict_of_ae (tendsto_ae_condExp (ℱ := G) (μ := P) Y))
      hgL1
    · intro n
      exact ae_restrict_of_ae
        (hX.condExp_closing_le_stoppedValue_of_bounded hF hr hY hclose (hU n) (hbU n))
    · intro n
      have hs := hX.condExp_stoppedValue_ae_le_of_bounded hF hr hσ (hU n) (hσU n) (hbU n)
      calc
        _ = ∫ ω in A, P[stoppedValue X (U n) | hσ.measurableSpace] ω ∂P :=
          (setIntegral_condExp hσ.measurableSpace_le (hiU n) hA).symm
        _ ≤ _ := setIntegral_mono_ae integrable_condExp.integrableOn hiσ.integrableOn hs
  have hn := ae_le_condExp_of_forall_setIntegral_le hσ.measurableSpace_le hiσ.neg hiτ.neg
    hmσ.neg (fun A hA ↦ by
      simp only [Pi.neg_apply, integral_neg]
      exact neg_le_neg (hset A hA))
  filter_upwards [hn, condExp_neg (stoppedValueWithTerminal X Z τ) hσ.measurableSpace]
    with ω hnω heω
  rw [heω] at hnω
  exact neg_le_neg_iff.mp hnω

theorem condExp_closingProjection_stoppedValue_le_of_bounded_lower_time
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, σ ω ≤ T) :
    P[stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ | hσ.measurableSpace] ≤ᵐ[P]
      stoppedValue X σ := by
  obtain ⟨Z, _, hlim, _⟩ := hX.exists_integrable_limit_of_condExp_lower_bound hr hclose
  exact (condExp_mono (hX.integrable_stoppedValue_closingProjection hF hr hY hclose hτ)
    (hX.integrable_stoppedValue_actualLimit_of_closing hF hr hY hclose hlim hτ)
    (stoppedValue_closingProjection_le_actualLimit hclose hlim τ)).trans
      (hX.condExp_actualLimit_stoppedValue_le_of_bounded_lower_time
        hF hr hY hclose hlim hσ hτ hle hb)

end MeasureTheory.Supermartingale

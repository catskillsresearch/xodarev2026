/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Basic
public import StochLean.Probability.Process.Stopping.PredictableLimitPart
public import StochLean.Probability.Process.Stopping.JumpCoefficients
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Left continuity of stopping expectations from predictable jump means

An increasing sequence of everywhere-finite stopping times converges to a finite
stopping time. On the event where every term is strictly below the limit, the
limit restricted to that event is a genuinely predictable positive lifetime.
Elsewhere the sequence eventually equals its limit.

Class D gives uniform integrability of the actual sampled variables. Their
actual L1 limit is the terminal sample minus the zero-terminal jump at that
restricted predictable lifetime, not in general the terminal sample itself.
The jump's integrability is proved from this actual L1 limit and Class D before
the zero-mean hypothesis is used. In particular no nonintegrable Bochner
integral default is used to establish a probabilistic identity.

No supermartingale or adaptedness hypothesis is needed in addition to Class D
and the stated common cadlag event. No initial normalization is needed: the
strict-limit event excludes a limit at zero, and its complementary lifetime is
infinite with explicitly zero jump value. This expectation continuity does not
assert that predictable jumps vanish or that their occurrence probabilities
vanish.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Zero means of actual positive predictable jumps imply continuity of the
expectations along increasing finite stopping times. The finite limit need not
have a deterministic bound. -/
theorem IsClassD.tendsto_integral_finiteStoppingTime_of_monotone_of_predictable_jump_mean_zero
    (hD : IsClassD X F P) (hc : HasCadlagPaths X P) (hF : F.IsUsual P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (σ : ℕ → FiniteStoppingTime F) (τ : FiniteStoppingTime F)
    (hm : ∀ ω, Monotone (fun n ↦ σ n ω))
    (hlim : ∀ ω, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))) :
    Tendsto (fun n ↦ ∫ ω, X (σ n ω) ω ∂P) atTop
      (𝓝 (∫ ω, X (τ ω) ω ∂P)) := by
  classical
  let A : Set Ω := {ω | ∀ n, σ n ω < τ ω}
  let Γ : Ω → WithTop ℝ≥0 := restrictedStoppingTime τ.withTop A
  let J : Ω → ℝ := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) Γ
  let L : Ω → ℝ := fun ω ↦ X (τ ω) ω - J ω
  have hle (n : ℕ) (ω : Ω) : σ n ω ≤ τ ω := by
    apply ge_of_tendsto (hlim ω)
    filter_upwards [eventually_ge_atTop n] with k hk
    exact hm ω hk
  have hmcoe (ω : Ω) : Monotone (fun n ↦ (σ n ω : WithTop ℝ≥0)) :=
    fun _ _ hij ↦ WithTop.coe_le_coe.mpr (hm ω hij)
  have hsup (ω : Ω) : (⨆ n, (σ n ω : WithTop ℝ≥0)) = (τ ω : WithTop ℝ≥0) :=
    tendsto_nhds_unique (tendsto_atTop_iSup (hmcoe ω))
      (WithTop.continuous_coe.continuousAt.tendsto.comp (hlim ω))
  have hΓ : IsPredictableStoppingTime F Γ P := by
    have hh := isPredictableStoppingTime_iSup_restricted_strict
      (fun n ↦ (σ n).isStoppingTime) hmcoe hF
    change IsPredictableStoppingTime F
      (restrictedStoppingTime (fun ω ↦ (τ ω : WithTop ℝ≥0))
        {ω | ∀ n, σ n ω < τ ω}) P
    simpa only [hsup, WithTop.coe_lt_coe] using hh
  have hΓpos : ∀ᵐ ω ∂P, 0 < Γ ω := by
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · change 0 < restrictedStoppingTime τ.withTop A ω
      rw [restrictedStoppingTime_of_mem τ.withTop hω]
      exact WithTop.coe_lt_coe.mpr (lt_of_le_of_lt bot_le (hω 0))
    · change 0 < restrictedStoppingTime τ.withTop A ω
      rw [restrictedStoppingTime_of_notMem τ.withTop hω]
      exact WithTop.coe_lt_top 0
  have hpath : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (σ n ω) ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hc] with ω hcω
    by_cases hω : ω ∈ A
    · have ht : 0 < τ ω := lt_of_le_of_lt bot_le (hω 0)
      have heJ : J ω = jumpProcess X (τ ω) ω :=
        stoppedValueWithTerminal_jump_eq_of_eq_coe
          (restrictedStoppingTime_of_mem τ.withTop hω)
      have heL : L ω = leftLimitProcess X (τ ω) ω := by
        dsimp only [L]
        rw [heJ]
        change X (τ ω) ω - (X (τ ω) ω - leftLimitProcess X (τ ω) ω) = _
        ring
      rw [heL]
      exact (hcω.tendsto_leftLimitProcess (ne_of_gt ht)).comp
        (tendsto_nhdsWithin_iff.mpr ⟨hlim ω, Eventually.of_forall hω⟩)
    · have heJ : J ω = 0 :=
        stoppedValueWithTerminal_of_top (restrictedStoppingTime_of_notMem τ.withTop hω)
      have heL : L ω = X (τ ω) ω := by simp only [L, heJ, sub_zero]
      rw [heL]
      obtain ⟨n, hn⟩ := not_forall.mp hω
      have hen : σ n ω = τ ω := le_antisymm (hle n ω) (le_of_not_gt hn)
      apply tendsto_atTop_of_eventually_const (i₀ := n)
      intro k hk
      have hek : σ k ω = τ ω :=
        le_antisymm (hle k ω) (hen ▸ hm ω hk)
      rw [hek]
  have hu : UniformIntegrable (fun n ω ↦ X (σ n ω) ω) 1 P :=
    hD.uniformIntegrable_finiteStoppingTime σ
  have hiL : Integrable L P := hu.integrable_of_ae_tendsto hpath
  have hL1 : Tendsto (fun n ↦ eLpNorm ((fun ω ↦ X (σ n ω) ω) - L) 1 P)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
      (memLp_one_iff_integrable.mpr hiL) hu.2.1 hpath
  have hiτ := hD.integrable_finiteStoppingTime_value τ
  have heJ : (fun ω ↦ X (τ ω) ω) - L = J := by
    funext ω
    change X (τ ω) ω - (X (τ ω) ω - J ω) = J ω
    ring
  have hiJ : Integrable J P := heJ ▸ hiτ.sub hiL
  have hEL : (∫ ω, L ω ∂P) = ∫ ω, X (τ ω) ω ∂P := by
    change (∫ ω, X (τ ω) ω - J ω ∂P) = _
    rw [integral_sub hiτ hiJ, hreg Γ hΓ hΓpos, sub_zero]
  have he := tendsto_integral_of_L1' L hiL.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hD.integrable_finiteStoppingTime_value (σ n)) hL1
  rwa [hEL] at he

end ProbabilityTheory

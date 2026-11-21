/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.StoppingTimeReindex
public import StochLean.Probability.Process.Stopping.AnnouncingSigma
public import StochLean.Probability.Process.Path.LeftLimit
public import Mathlib.Probability.Martingale.Convergence

/-! # Identifying an announcing conditional-expectation limit

An actual conditional-expectation identity along an announcing sequence
identifies the stopped left limit with conditional expectation strictly
before the target time. Native Levy upward convergence uses the existing
stopping-time filtration and announcing sigma-field identity.

The target is positive and finite on one common full-measure event. Strict
announcing then makes every approximating time finite on that same event,
where the cadlag left-limit identification takes place. No meaning at an
infinite time is assigned by an `untopA` fallback.

This is a limit-identification lemma, not an optional-sampling assertion.
Its consumers must prove the actual announcing conditional identities from
their own sampling hypotheses.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.IsAnnouncingSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ}
  {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

/-- Actual announcing CE identities have the before-field CE as their common
limit, and cadlag paths identify that limit with the actual stopped left limit. -/
theorem stopped_leftLimit_ae_eq_condExp_before
    (hs : IsAnnouncingSequence F P τ σ) (hτ : IsStoppingTime F τ)
    (hcomplete : IsCompleteSubMeasurableSpace P (F 0)) (hc : HasCadlagPaths M P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (he : ∀ n, stoppedValue M (σ n) =ᵐ[P] P[V | (hs.isStoppingTime n).measurableSpace]) :
    stoppedValue (leftLimitProcess M) τ =ᵐ[P] P[V | hτ.measurableSpaceBefore] := by
  have hmono : Monotone σ := fun _ _ hnm ω ↦ hs.monotone ω hnm
  let G : Filtration ℕ mΩ := F.stoppingTimeReindex σ hs.isStoppingTime hmono
  have heG : hτ.measurableSpaceBefore = ⨆ n, G n :=
    hs.measurableSpaceBefore_eq_iSup hτ hcomplete
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ P[V | G n] ω) atTop
      (𝓝 (P[V | hτ.measurableSpaceBefore] ω)) := by
    rw [heG]
    exact tendsto_ae_condExp (ℱ := G) (μ := P) V
  filter_upwards [hc, hpos, hfinite, hs.tendsto, ae_all_iff.mpr he, hlim]
    with ω hcω hpω hfω hsω heω hlω
  have hσfinite (n : ℕ) : σ n ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfω (hs.strict n ω hpω).le
  have hp : 0 < (τ ω).untopA := by
    have h := hpω
    lift τ ω to ℝ≥0 using hfω with t ht
    exact WithTop.coe_lt_coe.mp h
  have hlt (n : ℕ) : (σ n ω).untopA < (τ ω).untopA := by
    have h := hs.strict n ω hpω
    lift σ n ω to ℝ≥0 using hσfinite n with s hsval
    lift τ ω to ℝ≥0 using hfω with t htval
    exact WithTop.coe_lt_coe.mp h
  have htend : Tendsto (fun n ↦ (σ n ω).untopA) atTop (𝓝[<] (τ ω).untopA) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(WithTop.tendsto_untopA hfω).comp hsω, Eventually.of_forall hlt⟩
  have hleft : Tendsto (fun n ↦ stoppedValue M (σ n) ω) atTop
      (𝓝 (stoppedValue (leftLimitProcess M) τ ω)) :=
    (hcω.tendsto_leftLimitProcess (ne_of_gt hp)).comp htend
  exact tendsto_nhds_unique hleft (hlω.congr fun n ↦ (heω n).symm)

end ProbabilityTheory.IsAnnouncingSequence

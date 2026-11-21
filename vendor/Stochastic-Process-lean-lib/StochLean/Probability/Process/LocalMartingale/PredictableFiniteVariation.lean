/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.JumpSampling
public import StochLean.Probability.Process.FiniteVariation.IntegrableJumps
public import StochLean.Probability.Process.FiniteVariation.DisjointPredictableJumps
public import StochLean.Probability.Process.LocalMartingale.ContinuousFiniteVariation
public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpIntegrableTerminal

/-! # Predictable finite-variation local martingales are constant

The actual masked UI fundamental sequence has zero conditional jump means
at predictable lifetimes. Its stopped jumps are before-measurable because
the original predictable FV jump coefficient is before-measurable. Thus
they vanish. Localization and the already constructed predictable jump
cover remove every positive jump, and continuous FV constancy finishes.

No local integrability of variation, naturality, or integrability of the
initial value is assumed. An arbitrary initial random value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

section FiniteMeasure

variable [IsFiniteMeasure P]

/-- At a positive predictable lifetime, the actual zero-terminal jump of
a predictable FV local martingale vanishes. The lifetime may be infinite. -/
theorem IsLocalMartingale.stopped_jumpWithTerminal_ae_eq_zero_of_predictable_finiteVariation
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hp : IsStronglyPredictable F X) (hv : HasFiniteVariationPaths X P)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsPredictableStoppingTime F σ P)
    (hpos : ∀ᵐ ω ∂P, 0 < σ ω) :
    stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ =ᵐ[P] 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := hX.2.2
  let E (n : ℕ) : Set Ω := {ω | 0 < ρ n ω}
  let Y (n : ℕ) := MeasureTheory.stoppedProcess (fun t ↦ (E n).indicator (X t)) (ρ n)
  let J := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ
  let K (n : ℕ) := (E n).indicator ({ω | σ ω ≤ ρ n ω}.indicator J)
  have hmJ : StronglyMeasurable[hσ.1.measurableSpaceBefore] J :=
    hp.stronglyMeasurable_stopped_jump_before_of_finiteVariation hF hX.2.1 hv hσ.1
  have hE (n : ℕ) : MeasurableSet[F 0] (E n) := by
    simpa only [E, WithTop.coe_zero, compl_ofPred, not_le] using
      (hρ.1.isStoppingTime n 0).compl
  have hKzero (n : ℕ) : K n =ᵐ[P] 0 := by
    have hcap : MeasurableSet[hσ.1.measurableSpaceBefore] {ω | σ ω ≤ ρ n ω} := by
      simpa only [compl_ofPred, not_lt] using
        ((hρ.1.isStoppingTime n).measurableSet_lt_before hσ.1).compl
    have hmK : StronglyMeasurable[hσ.1.measurableSpaceBefore] (K n) :=
      (hmJ.indicator hcap).indicator (hσ.1.le_measurableSpaceBefore _ (hE n))
    have hcY : HasCadlagPaths (Y n) P := (hX.2.1.indicator (E n)).stoppedProcess (ρ n)
    obtain ⟨hi, hz⟩ :=
      (hρ.2.2 n).1.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
        (hρ.2.2 n).2 hF hcY hσ hpos
    have he : stoppedValueWithTerminal (jumpProcess (Y n)) (fun _ ↦ (0 : ℝ)) σ =ᵐ[P]
        K n := hX.2.1.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess (E n) (ρ n) σ
    have hiK : Integrable (K n) P := hi.congr he
    have hCE : P[K n | hσ.1.measurableSpaceBefore] =ᵐ[P] 0 :=
      (condExp_congr_ae he).symm.trans hz
    rwa [condExp_of_stronglyMeasurable hσ.1.measurableSpaceBefore_le_ambient hmK hiK] at hCE
  have hall : ∀ᵐ ω ∂P, ∀ n, K n ω = 0 := by
    rw [ae_all_iff]
    exact hKzero
  filter_upwards [hall, hρ.1.tendsto_top] with ω hzero hlim
  cases hs : σ ω with
  | top => exact stoppedValueWithTerminal_jump_eq_zero_of_top hs
  | coe t =>
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
    have hEω : ω ∈ E n := lt_of_le_of_lt bot_le hn
    have hcap : ω ∈ {ω | σ ω ≤ ρ n ω} := by
      change σ ω ≤ ρ n ω
      rw [hs]
      exact hn.le
    simpa only [K, J, Pi.zero_apply, indicator_of_mem hEω, indicator_of_mem hcap] using hzero n

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure P]

/-- The constructed countable predictable cover turns individual zero
jump samples into one common event with no positive-time jumps. -/
theorem IsLocalMartingale.ae_jumpProcess_eq_zero_of_predictable_finiteVariation
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hp : IsStronglyPredictable F X) (hv : HasFiniteVariationPaths X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 → jumpProcess X t ω = 0 := by
  obtain ⟨σ, hσ, hpos, _, hcover⟩ :=
    hp.exists_positive_disjoint_predictableStoppingTime_cover_jumps hF hX.2.1 hv
  have hz (n : ℕ) :=
    hX.stopped_jumpWithTerminal_ae_eq_zero_of_predictable_finiteVariation hF hp hv
      (hσ n) (Eventually.of_forall (hpos n))
  have hall : ∀ᵐ ω ∂P, ∀ n,
      stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (σ n) ω = 0 := by
    rw [ae_all_iff]
    exact hz
  filter_upwards [hall, hcover] with ω hzero hc t ht
  by_contra hj
  obtain ⟨n, hn⟩ := hc t (pos_iff_ne_zero.mpr ht) hj
  exact hj ((stoppedValueWithTerminal_jump_eq_of_eq_coe hn).symm.trans (hzero n))

/-- Continuity is derived from the zero-jump conclusion, not imposed on
an arbitrary finite-variation local martingale. -/
theorem IsLocalMartingale.hasContinuousPaths_of_predictable_finiteVariation
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hp : IsStronglyPredictable F X) (hv : HasFiniteVariationPaths X P) :
    HasContinuousPaths X P :=
  hX.2.1.hasContinuousPaths_of_jumpProcess_eq_zero
    (hX.ae_jumpProcess_eq_zero_of_predictable_finiteVariation hF hp hv)

/-- Protter III.15 retains an arbitrary, possibly nonintegrable initial
value. It uses only the existing continuous FV local-martingale theorem. -/
theorem IsLocalMartingale.indistinguishable_initial_of_predictable_finiteVariation
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hp : IsStronglyPredictable F X) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable X (fun _ ↦ X 0) P :=
  IsContinuousLocalMartingale.indistinguishable_initial_of_finiteVariation
    ⟨hX, hX.hasContinuousPaths_of_predictable_finiteVariation hF hp hv⟩ hF hv

/-- Zero initial value is an explicit extra assumption; the source
initial jump is not removed by the positive-time argument. -/
theorem IsLocalMartingale.indistinguishable_zero_of_predictable_finiteVariation
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hp : IsStronglyPredictable F X) (hv : HasFiniteVariationPaths X P)
    (h0 : X 0 =ᵐ[P] 0) : Indistinguishable X 0 P := by
  filter_upwards [hX.indistinguishable_initial_of_predictable_finiteVariation hF hp hv, h0]
    with ω hc hz t
  exact (hc t).trans hz

end ProbabilityMeasure

end ProbabilityTheory

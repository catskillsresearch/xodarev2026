/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations
public import StochLean.Probability.Process.Path.Cadlag

/-!
# Protter local martingales and Klenke localization

The canonical local martingale uses masked stopped UI martingales (Protter I.6).
Klenke's unmasked localizer is witness data, not a competing process hierarchy.
The unmasked bridge requires integrability of the initial value. Time is `ℝ≥0`;
stopping times have values in `WithTop ℝ≥0`, and stopped processes are only
evaluated at finite deterministic times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Deterministic-time UI, in addition to the canonical Mathlib martingale predicate.
This is not the stopping-time Class D predicate. -/
def IsUIMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Martingale X F P ∧ UniformIntegrable X 1 P

/-- Protter I.6 reducing time: the unmasked stopped process is a UI martingale.
The fundamental sequence instead reduces the masked process. -/
def IsReducingStoppingTime (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (τ : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime F τ ∧ IsUIMartingale (stoppedProcess X τ) F P

/-- A monotone sequence of reducing times tending to infinity almost surely. -/
def IsFundamentalSequence (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (τ : ℕ → Ω → WithTop ℝ≥0) : Prop :=
  IsPreLocalizingSequence F τ P ∧ Monotone τ ∧
    ∀ n, IsUIMartingale
      (stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)) F P

/-- Canonical Protter local martingale. Path regularity holds on one common event. -/
def IsLocalMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧ ∃ τ, IsFundamentalSequence X F P τ

def IsContinuousLocalMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsLocalMartingale X F P ∧ HasContinuousPaths X P

/-- Klenke 21.66 source witness: stopped processes are unmasked UI martingales. -/
def IsKlenkeLocalizingSequence (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (τ : ℕ → Ω → WithTop ℝ≥0) : Prop :=
  IsPreLocalizingSequence F τ P ∧ Monotone τ ∧
    ∀ n, IsUIMartingale (stoppedProcess X (τ n)) F P

/-- CM-SQ-REF01: finite-time square integrability, with no global L2 bound. -/
def IsSquareIntegrableMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Martingale X F P ∧ ∀ t, MemLp (X t) 2 P

theorem IsFundamentalSequence.isLocalizingSequence {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsFundamentalSequence X F P τ) : IsLocalizingSequence F τ P :=
  { hτ.1 with mono := ae_of_all _ fun ω _ _ hnm ↦ hτ.2.1 hnm ω }

theorem IsFundamentalSequence.isReducingStoppingTime_masked {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsFundamentalSequence X F P τ) (n : ℕ) :
    IsReducingStoppingTime (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) F P (τ n) :=
  ⟨hτ.1.isStoppingTime n, hτ.2.2 n⟩

theorem IsLocalMartingale.locally_ui (hX : IsLocalMartingale X F P) :
    Locally (fun Y ↦ IsUIMartingale Y F P) F X P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  exact ⟨τ, hτ.isLocalizingSequence, hτ.2.2⟩

theorem IsUIMartingale.isLocalMartingale (hX : IsUIMartingale X F P)
    (hcad : HasCadlagPaths X P) : IsLocalMartingale X F P := by
  refine ⟨hX.1.stronglyAdapted.adapted, hcad, fun _ _ ↦ ⊤,
    (isLocalizingSequence_const_top F P).toIsPreLocalizingSequence,
    fun _ _ _ _ ↦ le_rfl, fun n ↦ ?_⟩
  simpa using hX

theorem IsUIMartingale.isContinuousLocalMartingale (hX : IsUIMartingale X F P)
    (hcont : HasContinuousPaths X P) : IsContinuousLocalMartingale X F P :=
  ⟨hX.isLocalMartingale hcont.hasCadlagPaths, hcont⟩

private theorem martingale_indicator_initial (hX : Martingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Martingale (fun t ↦ s.indicator (X t)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted t).indicator (F.mono bot_le s hs), ?_⟩
  intro s' t hst
  refine (condExp_indicator (hX.integrable t) (F.mono bot_le s hs)).trans ?_
  filter_upwards [hX.condExp_ae_eq hst] with ω hω
  by_cases h : ω ∈ s <;> simp [h, hω]

theorem IsUIMartingale.indicator_initial (hX : IsUIMartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsUIMartingale (fun t ↦ s.indicator (X t)) F P :=
  ⟨martingale_indicator_initial hX.1 hs, hX.2.indicator (F.le 0 s hs)⟩

theorem IsKlenkeLocalizingSequence.isFundamentalSequence
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsKlenkeLocalizingSequence X F P τ) :
    IsFundamentalSequence X F P τ := by
  refine ⟨hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hs : MeasurableSet[F 0] {ω | 0 < τ n ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using
      (hτ.1.isStoppingTime n 0).compl
  simpa only [stoppedProcess_indicator_comm'] using (hτ.2.2 n).indicator_initial hs

theorem IsKlenkeLocalizingSequence.isLocalMartingale
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsKlenkeLocalizingSequence X F P τ)
    (hadapt : Adapted F X) (hcad : HasCadlagPaths X P) : IsLocalMartingale X F P :=
  ⟨hadapt, hcad, τ, hτ.isFundamentalSequence⟩

/-- Every unmasked Klenke witness forces integrability at time zero. -/
theorem IsKlenkeLocalizingSequence.integrable_initial
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsKlenkeLocalizingSequence X F P τ) :
    Integrable (X 0) P := by
  have h := (hτ.2.2 0).1.integrable 0
  have heq : stoppedProcess X (τ 0) 0 = X 0 :=
    funext fun _ ↦ stoppedProcess_eq_of_le bot_le
  rwa [heq] at h

/-- Exact pointwise split used by the reverse source bridge; stopping at zero retains `X 0`. -/
theorem stoppedProcess_eq_masked_add_initial (τ : Ω → WithTop ℝ≥0) :
    stoppedProcess X τ =
      (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) +
        (fun _ ↦ {ω | τ ω = 0}.indicator (X 0)) := by
  ext t ω
  simp only [Pi.add_apply]
  rw [stoppedProcess_indicator_comm]
  by_cases h : τ ω = 0
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < τ ω} by simp [h]),
      Set.indicator_of_mem (show ω ∈ {ω | τ ω = 0} from h), zero_add]
    have hle : τ ω ≤ (t : WithTop ℝ≥0) := h ▸ bot_le
    rw [stoppedProcess_eq_of_ge hle]
    have hzero : τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := h
    rw [hzero]
    rfl
  · have hp : 0 < τ ω := lt_of_le_of_ne bot_le (Ne.symm h)
    simp [h, hp]

theorem IsFundamentalSequence.isKlenkeLocalizingSequence
    [SigmaFiniteFiltration P F] {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsFundamentalSequence X F P τ) (hadapt : Adapted F X)
    (hinit : Integrable (X 0) P) : IsKlenkeLocalizingSequence X F P τ := by
  refine ⟨hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hs : MeasurableSet[F 0] {ω | τ n ω = 0} :=
    (hτ.1.isStoppingTime n).measurableSet_eq 0
  have hi := hinit.indicator (F.le 0 _ hs)
  have hm := martingale_const_fun F P ((hadapt.stronglyAdapted 0).indicator hs) hi
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ {ω | τ n ω = 0}.indicator (X 0)) 1 P :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hi)
  rw [stoppedProcess_eq_masked_add_initial]
  exact ⟨(hτ.2.2 n).1.add hm, (hτ.2.2 n).2.add hu le_rfl⟩

/-- The same fundamental sequence is an unmasked localizer once the initial value is integrable. -/
theorem IsLocalMartingale.exists_klenkeLocalizingSequence [SigmaFiniteFiltration P F]
    (hX : IsLocalMartingale X F P) (hinit : Integrable (X 0) P) :
    ∃ τ, IsKlenkeLocalizingSequence X F P τ := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  exact ⟨τ, hτ.isKlenkeLocalizingSequence hX.1 hinit⟩

theorem exists_klenkeLocalizingSequence_iff [SigmaFiniteFiltration P F]
    (hadapt : Adapted F X) (hcad : HasCadlagPaths X P) :
    (∃ τ, IsKlenkeLocalizingSequence X F P τ) ↔
      IsLocalMartingale X F P ∧ Integrable (X 0) P := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨hτ.isLocalMartingale hadapt hcad, hτ.integrable_initial⟩
  · rintro ⟨hX, hinit⟩
    exact hX.exists_klenkeLocalizingSequence hinit

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Stability
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Iterated localization

The stable property used internally is the conjunction of the canonical UI
martingale and common-event cadlag predicates. Mathlib's diagonal extraction
and local-property idempotence are reused. An explicit tail infimum converts
its AE-monotone witness to the everywhere-monotone fundamental sequence used
by this project. No local-martingale theorem is assumed as a structure field.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem isStable_cadlagUIMartingale (hF : F.IsUsual P) :
    IsStable F (fun Y ↦ IsUIMartingale Y F P ∧ HasCadlagPaths Y P) := by
  intro Y hY τ hτ
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using (hτ 0).compl
  have hcad := hY.2.indicator {ω | 0 < τ ω}
  exact ⟨(hY.1.indicator_initial hs).stoppedProcess_of_usual hF
    hcad.hasRightContinuousPaths hτ, hcad.stoppedProcess τ⟩

omit [IsFiniteMeasure P] in
theorem IsLocalMartingale.locally_cadlagUI (hX : IsLocalMartingale X F P) :
    Locally (fun Y ↦ IsUIMartingale Y F P ∧ HasCadlagPaths Y P) F X P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  exact ⟨τ, hτ.isLocalizingSequence, fun n ↦
    ⟨hτ.2.2 n, (hX.2.1.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)⟩⟩

omit [IsFiniteMeasure P] in
/-- Adaptedness is recovered from the actual localizations and relative completeness. -/
theorem IsPreLocalizingSequence.adapted_of_masked {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (ha : ∀ n, Adapted F
      (stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n))) : Adapted F X := by
  intro t
  let U n := stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n) t
  have hm : StronglyMeasurable[F t] (fun ω ↦ limUnder atTop (fun n ↦ U n ω)) := by
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder (fun n ↦ (ha n t).stronglyMeasurable)
  have heq : (fun ω ↦ limUnder atTop (fun n ↦ U n ω)) =ᵐ[P] X t := by
    filter_upwards [hτ.ae_eventually_masked_stoppedProcess_eq (X := X) t] with ω hω
    have he : (fun n ↦ U n ω) =ᶠ[atTop] (fun _ ↦ X t ω) := hω
    exact (tendsto_const_nhds.congr' he.symm).limUnder_eq
  have hc : IsCompleteSubMeasurableSpace P (F t) := fun A hA ↦
    F.mono bot_le A (hF.complete_initial A hA)
  exact hc.measurable_congr_ae hm.measurable heq

theorem isLocalMartingale_of_locally_cadlagUI (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsUIMartingale Y F P ∧ HasCadlagPaths Y P) F X P) :
    IsLocalMartingale X F P := by
  let : F.IsRightContinuous := hF.rightContinuous
  obtain ⟨τ, hτ, hu⟩ := hL
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ ⨅ j ≥ n, τ j ω
  have hσ : IsLocalizingSequence F σ P := hτ.toIsPreLocalizingSequence.isLocalizingSequence_biInf
  have hsmall (n : ℕ) : σ n ≤ τ n := fun _ ↦ (iInf_le _ n).trans (iInf_le _ le_rfl)
  refine ⟨hτ.toIsPreLocalizingSequence.adapted_of_masked hF
    (fun n ↦ (hu n).1.1.stronglyAdapted.adapted), hcad,
    σ, hσ.toIsPreLocalizingSequence, ?_, fun n ↦ ?_⟩
  · intro n m hnm ω
    exact iInf_le_iInf_of_subset (fun j hj ↦ hnm.trans hj)
  · rw [stoppedProcess_indicator_comm',
      ← stoppedProcess_stoppedProcess_of_le_right (hsmall n),
      ← stoppedProcess_indicator_comm']
    convert ((isStable_cadlagUIMartingale hF) _ (hu n) (σ n) (hσ.isStoppingTime n)).1 using 2
    ext t
    rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
    congr with ω
    exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h (hsmall n ω)⟩, fun h ↦ h.1⟩

/-- Protter I.48(e): an adaptedness hypothesis is not added; it is recovered above. -/
theorem isLocalMartingale_of_locally_localMartingale (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P) (hL : Locally (fun Y ↦ IsLocalMartingale Y F P) F X P) :
    IsLocalMartingale X F P := by
  let : F.IsRightContinuous := hF.rightContinuous
  apply isLocalMartingale_of_locally_cadlagUI hF hcad
  exact (isStable_cadlagUIMartingale hF).locally_induction
    (fun _ hY ↦ hY.locally_cadlagUI) hL

/-- Protter I.50: local martingales may be localized by true, not necessarily UI, martingales. -/
theorem isLocalMartingale_of_locally_martingale (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P) (hL : Locally (fun Y ↦ Martingale Y F P) F X P) :
    IsLocalMartingale X F P := by
  obtain ⟨τ, hτ, hu⟩ := hL
  apply isLocalMartingale_of_locally_localMartingale hF hcad
  exact ⟨τ, hτ, fun n ↦ (hu n).isLocalMartingale
    ((hcad.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n))⟩

/-- Protter I.49 on the source cadlag process domain; finite-time L2 is sufficient. -/
theorem isLocalMartingale_of_locally_squareIntegrableMartingale (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P) :
    IsLocalMartingale X F P :=
  isLocalMartingale_of_locally_martingale hF hcad (hL.mono (fun _ h ↦ h.1))

end ProbabilityTheory

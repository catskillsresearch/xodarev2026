/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorLocalization
public import StochLean.Probability.Process.UCP.PredictableConsistentLocalization
public import StochLean.Probability.Process.LocalMartingale.Localization

/-! # Actual predictable compensators of locally integrable variation

The actually constructed integrable local compensators have proved stopped
consistency. Predictable UCP completion supplies their actual global limit.
Stopping recovers each level, proving local integrable variation and the
local-martingale remainder through the existing native masked-localization
theorem. The localizer retains its original almost-sure monotonicity; no
pointwise monotonicity or additional convergence is required as input.

The compensator is normalized exactly at zero and is unique against any
predictable finite-variation competitor with a local-martingale remainder.
No second compensator selector or local process hierarchy is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual compensator existence on the locally integrable-variation domain.
The original initial value is integrable but need not vanish; it remains in
the local martingale. Neither consistency nor a proposed predictable part
is supplied to this source theorem. -/
theorem HasLocallyIntegrableVariation.exists_unique_predictable_compensator_of_integrable_initial
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧ IsLocalMartingale (X - A) F P ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale (X - B) F P → Indistinguishable A B P := by
  obtain ⟨τ, C, hτ, hC, hcons⟩ :=
    hv.exists_consistent_predictable_compensator_localization ha hF hc hi0
  have hp (n : ℕ) := (hC n).1
  have hcc (n : ℕ) := (hC n).2.1
  have hc0 (n : ℕ) := (hC n).2.2.1
  have hcv (n : ℕ) := (hC n).2.2.2.1
  have hU (n : ℕ) := (hC n).2.2.2.2
  obtain ⟨Y, hpY, hcY, hCY, hrY, _⟩ :=
    hτ.toIsPreLocalizingSequence.exists_predictable_cadlag_limit_of_stopped_consistency
      hF hp (fun n ↦ Eventually.of_forall (hcc n)) hcons
  have hY0 : Y 0 =ᵐ[P] 0 :=
    hCY.ae_eq_initial (fun n ↦ Eventually.of_forall fun ω ↦ congrFun (hc0 n) ω)
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ Y 0
  have haI : Adapted F I := fun t ↦
    (hpY.stronglyAdapted.adapted 0).mono (F.mono bot_le) le_rfl
  have hpI : IsStronglyPredictable F I :=
    haI.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  let A := Y - I
  have hpA : IsStronglyPredictable F A := hpY.sub hpI
  have hcA (ω : Ω) : IsCadlagPath (A · ω) := (hcY ω).sub
    (IsContinuousPath.isCadlagPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ Y 0 ω)))
  have hA0 : A 0 = 0 := funext fun _ ↦ sub_self _
  have heYA : Indistinguishable Y A P := by
    filter_upwards [hY0] with ω hω t
    change Y t ω = Y t ω - Y 0 ω
    rw [hω]
    exact (sub_zero _).symm
  have hr (n : ℕ) : Indistinguishable (stoppedProcess A (τ n)) (C n) P :=
    (heYA.symm.stoppedProcess (τ n)).trans (hrY n)
  have hvA : HasLocallyIntegrableVariation A F P :=
    hasLocallyIntegrableVariation_iff_exists_stopped.mpr
      ⟨τ, hτ, fun n ↦ (hcv n).congr (hr n).symm⟩
  have haM : Adapted F (X - A) := ha.sub hpA.stronglyAdapted.adapted
  have hcM : HasCadlagPaths (X - A) P := hc.sub (Eventually.of_forall hcA)
  have hu (n : ℕ) : IsUIMartingale (stoppedProcess (X - A) (τ n)) F P := by
    apply (hU n).congr
      (haM.stronglyAdapted.stoppedProcess_of_usual hF hcM.hasRightContinuousPaths
        (hτ.isStoppingTime n)).adapted
    filter_upwards [hr n] with ω hω t
    change stoppedProcess X (τ n) t ω - C n t ω =
      stoppedProcess X (τ n) t ω - stoppedProcess A (τ n) t ω
    rw [hω t]
  have hM : IsLocalMartingale (X - A) F P := by
    apply isLocalMartingale_of_locally_cadlagUI hF hcM
    refine ⟨τ, hτ, fun n ↦ ⟨?_, (hcM.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)⟩⟩
    have hs : MeasurableSet[F 0] {ω | 0 < τ n ω} := by
      simpa only [WithTop.coe_zero, compl_ofPred, not_le] using
        (hτ.isStoppingTime n 0).compl
    simpa only [stoppedProcess_indicator_comm', bot_eq_zero] using (hu n).indicator_initial hs
  refine ⟨A, hpA, hcA, hA0, hvA, hM, ?_⟩
  intro B hpB hvB hB0 hMB
  have hAB0 : A 0 =ᵐ[P] B 0 := by
    filter_upwards [hB0] with ω hω
    exact (congrFun hA0 ω).trans hω.symm
  have he : Indistinguishable ((X - A) + A) ((X - B) + B) P := by
    filter_upwards with ω t
    simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]
  exact (indistinguishable_parts_of_predictable_finiteVariation_decomposition hF
    hM hMB hpA hpB hvA.hasFiniteVariationPaths hvB hAB0 he).1

end ProbabilityTheory

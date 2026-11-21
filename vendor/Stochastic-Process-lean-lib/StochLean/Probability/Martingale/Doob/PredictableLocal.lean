/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableClassD
public import StochLean.Probability.Martingale.Doob.PredictableUniqueness
public import StochLean.Probability.Martingale.Doob.NormExitClassD
public import StochLean.Probability.Martingale.Doob.StoppedCompensatorMean
public import StochLean.Probability.Process.Stopping.PredictableProcess
public import StochLean.Probability.Process.UCP.PredictableConsistentLocalization
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import StochLean.ForMathlib.MeasureTheory.FatouNonnegative

/-! # General local Doob--Meyer decomposition

Actual capped norm exits give Class D stopped supermartingales. The general
Class D theorem constructs each predictable increasing part. Uniqueness, not
a supplied consistency assumption, identifies their stopped restrictions.
Predictable UCP completion then constructs the actual global compensator.

Its local integrable variation and the local martingale both use these same
actual exit times. Finite-time integrability and the sharp expectation bound
follow from bounded optional sampling and nonnegative Fatou; no uniform
integrability or L1 convergence of the original stopped process is assumed.
The compensator starts exactly at zero. The arbitrary integrable initial
value of the original supermartingale stays in the local martingale.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual capped exits construct a stopped-consistent family of predictable
increasing integrable-variation compensators, with no Class D hypothesis
on the original supermartingale. Consistency is a proved conclusion. -/
theorem Supermartingale.exists_predictable_doob_localization
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ A : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, IsStronglyPredictable F (A n) ∧ HasCadlagPaths (A n) P ∧
        A n 0 = 0 ∧ HasMonotonePaths (A n) P ∧ HasIntegrableVariation (A n) P ∧
        IsUIMartingale (stoppedProcess X (cappedNormExitSequence X n) + A n) F P) ∧
      ∀ n m, n ≤ m →
        Indistinguishable (stoppedProcess (A m) (cappedNormExitSequence X n)) (A n) P := by
  have hτ := hX.stronglyAdapted.adapted.isLocalizingSequence_cappedNormExitSequence hF hc
  have hex (n : ℕ) : ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasIntegrableVariation A P ∧
      IsUIMartingale (stoppedProcess X (cappedNormExitSequence X n) + A) F P := by
    have hs := hX.stoppedProcess_of_usual hF hc.hasRightContinuousPaths (hτ.isStoppingTime n)
    obtain ⟨A, _, hp, hca, h0, hm, hv, _, hM, _⟩ :=
      hs.exists_predictable_doob_of_classD
        (hX.isClassD_stoppedProcess_cappedNormExitSequence hF hc n)
        hF (hc.stoppedProcess (cappedNormExitSequence X n))
    exact ⟨A, hp, hca, h0, hm, hv, hM⟩
  choose A hp hca h0 hm hv hM using hex
  refine ⟨A, fun n ↦ ⟨hp n, hca n, h0 n, hm n, hv n, hM n⟩, ?_⟩
  intro n m hnm
  have hcm := (hc.stoppedProcess (cappedNormExitSequence X m)).add (hca m)
  have hcn := (hc.stoppedProcess (cappedNormExitSequence X n)).add (hca n)
  have hsmall : Martingale
      (stoppedProcess X (cappedNormExitSequence X n) +
        stoppedProcess (A m) (cappedNormExitSequence X n)) F P := by
    simpa only [stoppedProcess_add,
      stoppedProcess_stoppedProcess_of_le_right (monotone_cappedNormExitSequence X hnm)]
      using (hM m).1.stoppedProcess_of_usual hF hcm.hasRightContinuousPaths
        (hτ.isStoppingTime n)
  apply indistinguishable_of_predictable_finiteVariation_localMartingale_add hF
    (hsmall.isLocalMartingale
      ((hc.stoppedProcess (cappedNormExitSequence X n)).add
        ((hca m).stoppedProcess (cappedNormExitSequence X n))))
    ((hM n).isLocalMartingale hcn)
    ((hp m).stoppedProcess (hτ.isStoppingTime n)) (hp n)
    ((hm m).stoppedProcess (cappedNormExitSequence X n)).hasFiniteVariationPaths
    (hm n).hasFiniteVariationPaths
  filter_upwards with ω
  rw [stoppedProcess_eq_of_le (u := A m) (i := (0 : ℝ≥0)) bot_le]
  exact (congrFun (h0 m) ω).trans (congrFun (h0 n) ω).symm

/-- Protter III.16: every cadlag supermartingale on a usual probability
space has a predictable increasing locally integrable-variation compensator
starting exactly at zero. Its compensated process is a local martingale,
and each compensator coordinate is integrable with the sharp expectation
bound. There is no Class D, regularity, jump bound, or proposed-part input. -/
theorem Supermartingale.exists_predictable_doob_local_decomposition
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale (X + A) F P ∧
      (∀ t, Integrable (A t) P ∧
        (∫ ω, A t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P) := by
  obtain ⟨B, hb, hcons⟩ := hX.exists_predictable_doob_localization hF hc
  have hp (n : ℕ) := (hb n).1
  have hbc (n : ℕ) := (hb n).2.1
  have hb0 (n : ℕ) := (hb n).2.2.1
  have hbm (n : ℕ) := (hb n).2.2.2.1
  have hbv (n : ℕ) := (hb n).2.2.2.2.1
  have hM (n : ℕ) := (hb n).2.2.2.2.2
  let τ := cappedNormExitSequence X
  have hτ : IsLocalizingSequence F τ P :=
    hX.stronglyAdapted.adapted.isLocalizingSequence_cappedNormExitSequence hF hc
  obtain ⟨Y, hpY, hcY, _, hrY, hmY, _, hY0, _, hevent⟩ :=
    hτ.toIsPreLocalizingSequence.exists_predictable_cadlag_monotone_limit_of_stopped_consistency
      hF hp hbc hcons hbm (fun n ↦ Eventually.of_forall fun ω ↦ congrFun (hb0 n) ω)
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
  have hmA : HasMonotonePaths A P := hmY.congr heYA
  have hr (n : ℕ) : Indistinguishable (stoppedProcess A (τ n)) (B n) P :=
    (heYA.symm.stoppedProcess (τ n)).trans (hrY n)
  have hvA : HasLocallyIntegrableVariation A F P :=
    hasLocallyIntegrableVariation_iff_exists_stopped.mpr
      ⟨τ, hτ, fun n ↦ (hbv n).congr (hr n).symm⟩
  have hcadA : HasCadlagPaths A P := Eventually.of_forall hcA
  have haM : Adapted F (X + A) := hX.stronglyAdapted.adapted.add hpA.stronglyAdapted.adapted
  have hcadM : HasCadlagPaths (X + A) P := hc.add hcadA
  have hu (n : ℕ) : IsUIMartingale (stoppedProcess (X + A) (τ n)) F P := by
    apply (hM n).congr
      (haM.stronglyAdapted.stoppedProcess_of_usual hF hcadM.hasRightContinuousPaths
        (hτ.isStoppingTime n)).adapted
    filter_upwards [hr n] with ω hω t
    change stoppedProcess X (τ n) t ω + B n t ω =
      stoppedProcess X (τ n) t ω + stoppedProcess A (τ n) t ω
    rw [hω t]
  have hK : IsKlenkeLocalizingSequence (X + A) F P τ :=
    ⟨hτ.toIsPreLocalizingSequence, monotone_cappedNormExitSequence X, hu⟩
  refine ⟨A, hpA, hcA, hA0, hmA, hvA, hK.isLocalMartingale haM hcadM, ?_⟩
  intro t
  have hsi (n : ℕ) : Integrable (stoppedProcess X (τ n) t) P :=
    (hX.stoppedProcess_of_usual hF hc.hasRightContinuousPaths
      (hτ.isStoppingTime n)).integrable t
  have hbi (n : ℕ) : Integrable (B n t) P := by
    have he : B n t = (stoppedProcess X (τ n) + B n) t - stoppedProcess X (τ n) t := by
      funext ω
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [he]
    exact ((hM n).1.integrable t).sub (hsi n)
  have hbn (n : ℕ) : ∀ᵐ ω ∂P, 0 ≤ B n t ω := by
    filter_upwards [hbm n] with ω hω
    have hz := congrFun (hb0 n) ω
    have h := hω (bot_le : (0 : ℝ≥0) ≤ t)
    change B n 0 ω ≤ B n t ω at h
    simpa only [hz, Pi.zero_apply] using h
  have hmean (n : ℕ) :
      (∫ ω, B n t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P :=
    (hM n).1.integral_compensator_le_supermartingale_drop hX hF
      hc.hasRightContinuousPaths (hτ.isStoppingTime n)
      (Eventually.of_forall fun ω ↦ congrFun (hb0 n) ω) t (hbi n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ B n t ω) atTop (𝓝 (A t ω)) := by
    filter_upwards [hevent, heYA] with ω hω heω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω t] with n hn
    exact ((hn t le_rfl).trans (heω t)).symm
  exact integrable_and_integral_le_of_nonneg_ae_tendsto hbi hbn hlim
    ((integral_nonneg_of_ae (hbn 0)).trans (hmean 0)) hmean

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousBounded
public import StochLean.Probability.Martingale.Doob.ContinuousUniqueness
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedStopping
public import StochLean.Probability.Martingale.MonotonePaths
public import StochLean.Probability.Process.Stopping.CadlagExitLocalization
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumpStability

/-! # Consistent continuous compensators along capped norm exits

A zero-initial cadlag supermartingale with uniformly bounded positive-time
jumps has bounded stopped processes along the actual capped open norm exits.
The bounded construction therefore supplies a continuous increasing
compensator and an L2 closing variable at each level.

Consistency is a conclusion: stopping the larger-level martingale at a
smaller exit and using the native minimum identity produces a second
continuous finite-variation compensator of the same stopped process.
Continuous-compensator uniqueness identifies the two on one path event.

The result is a local family. No Class D patching or global martingale
decomposition is asserted here. The jump assumption concerns the norm of
every positive-time jump, not just jumps whose signed value is positive.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {c : ℝ}

/-- Apply the actual bounded dyadic construction to each actual norm exit.
The overshoot bound uses the common bound on positive-time jump norms. -/
theorem Supermartingale.exists_continuous_doob_decomposition_stopped_cappedNormExitSequence
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (h0 : X 0 =ᵐ[P] 0) (hb : 0 ≤ c)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ c) (n : ℕ) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      MemLp L 2 P ∧
      (∀ t, stoppedProcess X (cappedNormExitSequence X n) t + A t =ᵐ[P] P[L | F t]) ∧
      Martingale (stoppedProcess X (cappedNormExitSequence X n) + A) F P ∧
      HasCadlagPaths (stoppedProcess X (cappedNormExitSequence X n) + A) P ∧
      UniformIntegrable (stoppedProcess X (cappedNormExitSequence X n) + A) 1 P ∧
      (∀ t, MemLp (A t) 2 P ∧
        MemLp (stoppedProcess X (cappedNormExitSequence X n) t + A t) 2 P) ∧
      TendstoUCP P (dyadicDoobStep (stoppedProcess X (cappedNormExitSequence X n)) F P)
        atTop A := by
  have hτ := hX.stronglyAdapted.adapted.isStoppingTime_cappedNormExitSequence hF hc n
  have hs := hX.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hτ
  have hbound : ∀ᵐ ω ∂P, ∀ t,
      ‖stoppedProcess X (cappedNormExitSequence X n) t ω‖ ≤ ((n + 1 : ℕ) : ℝ) + c :=
    (hc.ae_norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound h0 hb hj).mono
      fun _ hω ↦ hω n
  exact hs.exists_continuous_doob_decomposition_of_bound hF
    (hc.stoppedProcess (cappedNormExitSequence X n))
    (hJ.stoppedProcess hc (cappedNormExitSequence X n)) (by positivity) hbound

/-- Continuous increasing compensators of actual capped norm exits are
automatically consistent. This comparison does not use any jump classification. -/
theorem Supermartingale.continuous_doob_localization_consistency
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {A : ℕ → ℝ≥0 → Ω → ℝ}
    (hcont : ∀ n ω, Continuous (A n · ω)) (hzero : ∀ n, A n 0 = 0)
    (hmono : ∀ n, HasMonotonePaths (A n) P)
    (hM : ∀ n, Martingale (stoppedProcess X (cappedNormExitSequence X n) + A n) F P) :
    ∀ n m, n ≤ m →
      Indistinguishable (stoppedProcess (A m) (cappedNormExitSequence X n)) (A n) P := by
  intro n m hnm
  have hτn := hX.stronglyAdapted.adapted.isStoppingTime_cappedNormExitSequence hF hc n
  have hAmcont : HasContinuousPaths (A m) P := Eventually.of_forall (hcont m)
  have hMmc : HasCadlagPaths
      (stoppedProcess X (cappedNormExitSequence X m) + A m) P :=
    (hc.stoppedProcess (cappedNormExitSequence X m)).add hAmcont.hasCadlagPaths
  have hstop := (hM m).stoppedProcess_of_usual hF hMmc.hasRightContinuousPaths hτn
  have hMsmall : Martingale
      (stoppedProcess X (cappedNormExitSequence X n) +
        stoppedProcess (A m) (cappedNormExitSequence X n)) F P := by
    simpa only [stoppedProcess_add,
      stoppedProcess_stoppedProcess_of_le_right (monotone_cappedNormExitSequence X hnm)]
      using hstop
  have hAstop0 : stoppedProcess (A m) (cappedNormExitSequence X n) 0 =ᵐ[P] 0 := by
    refine Eventually.of_forall fun ω ↦ ?_
    exact (stoppedProcess_eq_of_le (u := A m) (i := (0 : ℝ≥0))
      (τ := cappedNormExitSequence X n) (ω := ω) bot_le).trans (congrFun (hzero m) ω)
  exact indistinguishable_of_continuous_finiteVariation_martingale_add_zero hF hMsmall (hM n)
    (hAmcont.stoppedProcess (cappedNormExitSequence X n)) (Eventually.of_forall (hcont n))
    ((hmono m).stoppedProcess (cappedNormExitSequence X n)).hasFiniteVariationPaths
    (hmono n).hasFiniteVariationPaths hAstop0
    (Eventually.of_forall fun ω ↦ congrFun (hzero n) ω)

/-- The individually constructed compensators form a consistent family.
The closing variables and actual dyadic convergence are retained, and the
stopped consistency identity is proved rather than required as input. -/
theorem Supermartingale.exists_consistent_continuous_doob_localization_of_jump_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (h0 : X 0 =ᵐ[P] 0) (hb : 0 ≤ c)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ c) :
    ∃ (A : ℕ → ℝ≥0 → Ω → ℝ) (L : ℕ → Ω → ℝ),
      (∀ n, Adapted F (A n) ∧ IsStronglyPredictable F (A n) ∧
        (∀ ω, Continuous (A n · ω)) ∧ A n 0 = 0 ∧ HasMonotonePaths (A n) P ∧
        HasFiniteVariationPaths (A n) P ∧ MemLp (L n) 2 P ∧
        (∀ t, stoppedProcess X (cappedNormExitSequence X n) t + A n t =ᵐ[P]
          P[L n | F t]) ∧
        Martingale (stoppedProcess X (cappedNormExitSequence X n) + A n) F P ∧
        HasCadlagPaths (stoppedProcess X (cappedNormExitSequence X n) + A n) P ∧
        UniformIntegrable (stoppedProcess X (cappedNormExitSequence X n) + A n) 1 P ∧
        (∀ t, MemLp (A n t) 2 P ∧
          MemLp (stoppedProcess X (cappedNormExitSequence X n) t + A n t) 2 P) ∧
        TendstoUCP P (dyadicDoobStep (stoppedProcess X (cappedNormExitSequence X n)) F P)
          atTop (A n)) ∧
      ∀ n m, n ≤ m →
        Indistinguishable (stoppedProcess (A m) (cappedNormExitSequence X n)) (A n) P := by
  choose A L hdata using fun n ↦
    hX.exists_continuous_doob_decomposition_stopped_cappedNormExitSequence hF hc hJ h0 hb hj n
  refine ⟨A, L, hdata, hX.continuous_doob_localization_consistency hF hc
    (fun n ↦ (hdata n).2.2.1) (fun n ↦ (hdata n).2.2.2.1)
    (fun n ↦ (hdata n).2.2.2.2.1) ?_⟩
  intro n
  obtain ⟨_, _, _, _, _, _, _, _, hM, _, _, _, _⟩ := hdata n
  exact hM

end MeasureTheory

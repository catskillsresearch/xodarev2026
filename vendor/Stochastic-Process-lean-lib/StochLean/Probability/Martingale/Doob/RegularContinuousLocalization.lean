/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularContinuousBounded
public import StochLean.Probability.Martingale.Doob.RegularStopping
public import StochLean.Probability.Martingale.Doob.ContinuousLocalization

/-! # Continuous compensators of actual bounded-jump regular localizations

The zero-mean condition for positive predictable jumps survives arbitrary
stopping. Actual capped norm exits of a zero-initial process with bounded jumps
are uniformly bounded at each level, including their overshoots. The bounded
regular source theorem therefore constructs their continuous compensators.

The same continuous finite-variation uniqueness proof used by the original TI
construction gives stopped consistency. No local compensator or compatibility
certificate is a source input, and no TI jump condition is imposed.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {c : ℝ}

/-- Apply the actual bounded dyadic construction to each actual norm exit.
The overshoot bound uses the common bound on positive-time jump norms. -/
theorem Supermartingale.exists_continuous_doob_stopped_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (h0 : X 0 =ᵐ[P] 0) (hb : 0 ≤ c)
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
  exact hs.exists_continuous_doob_decomposition_of_bound_of_predictable_jump_mean_zero hF
    (hc.stoppedProcess (cappedNormExitSequence X n)) (by positivity) hbound
    (fun ρ hρ hpos ↦ hc.integral_stopped_jump_stoppedProcess_eq_zero hF hτ hreg hρ hpos)

/-- The individually constructed compensators form a consistent family.
The closing variables and actual dyadic convergence are retained, and the
stopped consistency identity is proved rather than required as input. -/
theorem Supermartingale.exists_consistent_doob_localization_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (h0 : X 0 =ᵐ[P] 0) (hb : 0 ≤ c)
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
    hX.exists_continuous_doob_stopped_of_predictable_jump_mean_zero hF hc hreg h0 hb hj n
  refine ⟨A, L, hdata, hX.continuous_doob_localization_consistency hF hc
    (fun n ↦ (hdata n).2.2.1) (fun n ↦ (hdata n).2.2.2.1)
    (fun n ↦ (hdata n).2.2.2.2.1) ?_⟩
  intro n
  obtain ⟨_, _, _, _, _, _, _, _, hM, _, _, _, _⟩ := hdata n
  exact hM

end MeasureTheory

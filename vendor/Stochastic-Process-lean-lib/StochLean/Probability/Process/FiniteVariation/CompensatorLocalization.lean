/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorIntegrable
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.Stopping.PredictableProcess
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping

/-! # Actual consistent local compensators of locally integrable variation

The existing unmasked localization criterion supplies native localizers with
almost-sure monotonicity. The actual integrable-variation compensator theorem
constructs each stopped level. At time zero the stopped original process is
still the original initial random value, whose integrability is retained.

For two ordered levels, their stopping order is used only on the native
common full-measure event. The double-stopped larger martingale agrees
indistinguishably with the smaller stopped original process minus the stopped
larger compensator. Its adapted target is established before transferring the
martingale property. Existing uniqueness then proves consistency.

No pointwise-monotone replacement of the localizers, new local predicate,
global compensator selector, or assumed consistency is introduced.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual local compensators are predictable, globally IV at each
level, and stopped-consistent. The native localizing sequence is only
almost surely monotone, and the initial value of X need not vanish. -/
theorem HasLocallyIntegrableVariation.exists_consistent_predictable_compensator_localization
    (hX : HasLocallyIntegrableVariation X F P) (ha : Adapted F X)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) :
    ∃ (τ : ℕ → Ω → WithTop ℝ≥0) (B : ℕ → ℝ≥0 → Ω → ℝ),
      IsLocalizingSequence F τ P ∧
      (∀ n, IsStronglyPredictable F (B n) ∧ (∀ ω, IsCadlagPath (B n · ω)) ∧
        B n 0 = 0 ∧ HasIntegrableVariation (B n) P ∧
        IsUIMartingale (stoppedProcess X (τ n) - B n) F P) ∧
      ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (B m) (τ n)) (B n) P := by
  obtain ⟨τ, hτ, hv⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hX
  have haτ (n : ℕ) : Adapted F (stoppedProcess X (τ n)) :=
    (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths
      (hτ.isStoppingTime n)).adapted
  have h0τ (n : ℕ) : stoppedProcess X (τ n) 0 = X 0 := by
    funext ω
    exact stoppedProcess_eq_of_le (u := X) (τ := τ n) (i := (0 : ℝ≥0)) bot_le
  have hi0τ (n : ℕ) : Integrable (stoppedProcess X (τ n) 0) P := by
    rw [h0τ n]
    exact hi0
  have hex (n : ℕ) : ∃ B : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F B ∧ (∀ ω, IsCadlagPath (B · ω)) ∧ B 0 = 0 ∧
      HasIntegrableVariation B P ∧ IsUIMartingale (stoppedProcess X (τ n) - B) F P ∧
      ∀ C : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F C → HasFiniteVariationPaths C P →
        C 0 =ᵐ[P] 0 → IsLocalMartingale (stoppedProcess X (τ n) - C) F P →
        Indistinguishable B C P := by
    obtain ⟨B, hpB, hcB, hB0, hvB, huB, _, huniq⟩ :=
      (hv n).exists_unique_predictable_compensator (haτ n) hF
        (hc.stoppedProcess (τ n)) (hi0τ n)
    exact ⟨B, hpB, hcB, hB0, hvB, huB, huniq⟩
  choose B hpB hcB hB0 hvB huB huniq using hex
  have hcadB (n : ℕ) : HasCadlagPaths (B n) P := Eventually.of_forall (hcB n)
  refine ⟨τ, B, hτ, fun n ↦ ⟨hpB n, hcB n, hB0 n, hvB n, huB n⟩, ?_⟩
  intro n m hnm
  have hpStop : IsStronglyPredictable F (stoppedProcess (B m) (τ n)) :=
    (hpB m).stoppedProcess (hτ.isStoppingTime n)
  have hcStop : HasCadlagPaths (stoppedProcess (B m) (τ n)) P :=
    (hcadB m).stoppedProcess (τ n)
  have hvStop : HasIntegrableVariation (stoppedProcess (B m) (τ n)) P :=
    (hvB m).stoppedProcess (hpB m).stronglyAdapted.adapted hF (hcadB m)
      (hτ.isStoppingTime n)
  have hStop0 : stoppedProcess (B m) (τ n) 0 =ᵐ[P] 0 := by
    filter_upwards with ω
    rw [stoppedProcess_eq_of_le (u := B m) (τ := τ n) (i := (0 : ℝ≥0)) bot_le]
    exact congrFun (hB0 m) ω
  have hcadLarge := (hc.stoppedProcess (τ m)).sub (hcadB m)
  have hLarge := (huB m).1.stoppedProcess_of_usual hF hcadLarge.hasRightContinuousPaths
    (hτ.isStoppingTime n)
  have he : Indistinguishable
      (stoppedProcess (stoppedProcess X (τ m) - B m) (τ n))
      (stoppedProcess X (τ n) - stoppedProcess (B m) (τ n)) P := by
    filter_upwards [hτ.mono] with ω hω t
    change stoppedProcess (stoppedProcess X (τ m)) (τ n) t ω -
        stoppedProcess (B m) (τ n) t ω =
      stoppedProcess X (τ n) t ω - stoppedProcess (B m) (τ n) t ω
    rw [stoppedProcess_stoppedProcess]
    change X ((min (t : WithTop ℝ≥0) (min (τ n ω) (τ m ω))).untopA) ω -
        stoppedProcess (B m) (τ n) t ω =
      X ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) ω -
        stoppedProcess (B m) (τ n) t ω
    rw [min_eq_left (hω hnm)]
  have haSmall : Adapted F
      (stoppedProcess X (τ n) - stoppedProcess (B m) (τ n)) :=
    (haτ n).sub hpStop.stronglyAdapted.adapted
  have hSmall : Martingale
      (stoppedProcess X (τ n) - stoppedProcess (B m) (τ n)) F P :=
    hLarge.congr haSmall.stronglyAdapted he.ae_eq
  exact (huniq n (stoppedProcess (B m) (τ n)) hpStop hvStop.hasFiniteVariationPaths
    hStop0 (hSmall.isLocalMartingale ((hc.stoppedProcess (τ n)).sub hcStop))).symm

end ProbabilityTheory

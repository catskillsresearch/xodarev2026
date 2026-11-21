/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorInitial
public import StochLean.Probability.Process.FiniteVariation.CompensatorMonotone

/-! # Increasing locally integrable-variation compensators

Centering the source by its original initial value preserves monotone paths
and locally integrable variation, even when that initial value is not L1.
The existing masked Protter initial-value local martingale centers the actual
remainder as well. Intersecting the source and candidate localizers gives
actual global-IV stopped pairs, with only almost-sure monotonicity of the
native localizing sequence.

The proved global-IV comparison gives monotonicity at each stopped level.
On the common full-measure event of those conclusions and divergence of the
localizers, every finite pair of times is eventually unstopped. This proves
monotonicity on the whole original candidate path. The final existence
consumer calls the actual local compensator construction, with no candidate
or initial-integrability assumption supplied by the caller.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X A : ℝ≥0 → Ω → ℝ}

/-- A normalized predictable locally IV compensator of an increasing locally
IV source is increasing. Neither initial value is assumed integrable; the
candidate's initial value is only zero almost surely. -/
theorem HasLocallyIntegrableVariation.hasMonotonePaths_predictable_compensator
    (hvX : HasLocallyIntegrableVariation X F P) (haX : Adapted F X)
    (hF : F.IsUsual P) (hcX : HasCadlagPaths X P) (hmX : HasMonotonePaths X P)
    (hpA : IsStronglyPredictable F A) (hvA : HasLocallyIntegrableVariation A F P)
    (hA0 : A 0 =ᵐ[P] 0) (hM : IsLocalMartingale (X - A) F P) :
    HasMonotonePaths A P := by
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let Y := X - I
  have hI : IsContinuousLocalMartingale I F P :=
    isContinuousLocalMartingale_const_initial (haX 0)
  have haI : Adapted F I := hI.1.1
  have hcI : HasCadlagPaths I P := hI.2.hasCadlagPaths
  have hvI : HasLocallyIntegrableVariation I F P :=
    (hasIntegrableVariation_const (P := P) (X 0)).hasLocallyIntegrableVariation
  have hvY : HasLocallyIntegrableVariation Y F P := hvX.sub hvI haX haI hF hcX hcI
  have haY : Adapted F Y := haX.sub haI
  have hcY : HasCadlagPaths Y P := hcX.sub hcI
  have hmY : HasMonotonePaths Y P := by
    filter_upwards [hmX] with ω hω s t hst
    exact sub_le_sub (hω hst) le_rfl
  have hY0 : Y 0 = 0 := by
    funext ω
    exact sub_self (X 0 ω)
  have heMY : (X - A) - I = Y - A := by
    funext t ω
    change (X t ω - A t ω) - X 0 ω = (X t ω - X 0 ω) - A t ω
    ring
  have hMY : IsLocalMartingale (Y - A) F P := heMY ▸ hM.sub hI.1 hF
  have hcA : HasCadlagPaths A P := by
    have heA : X - (X - A) = A := by
      funext t ω
      change X t ω - (X t ω - A t ω) = A t ω
      ring
    exact heA ▸ hcX.sub hM.2.1
  obtain ⟨τ, hτ, hvYτ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hvY
  obtain ⟨σ, hσ, hvAσ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hvA
  let ρ := min τ σ
  have hρ : IsLocalizingSequence F ρ P := hτ.min hσ
  have hmStop (n : ℕ) : HasMonotonePaths (stoppedProcess A (ρ n)) P := by
    have haYτ : Adapted F (stoppedProcess Y (τ n)) :=
      (haY.stronglyAdapted.stoppedProcess_of_usual hF hcY.hasRightContinuousPaths
        (hτ.isStoppingTime n)).adapted
    have haAσ : Adapted F (stoppedProcess A (σ n)) :=
      ((hpA.stoppedProcess (hσ.isStoppingTime n)).stronglyAdapted).adapted
    have hy := (hvYτ n).stoppedProcess haYτ hF (hcY.stoppedProcess (τ n))
      (hσ.isStoppingTime n)
    have ha := (hvAσ n).stoppedProcess haAσ hF (hcA.stoppedProcess (σ n))
      (hτ.isStoppingTime n)
    have heY : σ n ⊓ τ n = ρ n := by
      funext ω
      exact min_comm (σ n ω) (τ n ω)
    have heA : τ n ⊓ σ n = ρ n := rfl
    rw [stoppedProcess_stoppedProcess, heY] at hy
    rw [stoppedProcess_stoppedProcess, heA] at ha
    have haYρ : Adapted F (stoppedProcess Y (ρ n)) :=
      (haY.stronglyAdapted.stoppedProcess_of_usual hF hcY.hasRightContinuousPaths
        (hρ.isStoppingTime n)).adapted
    have he0 : stoppedProcess Y (ρ n) 0 = Y 0 := by
      funext ω
      exact stoppedProcess_eq_of_le (u := Y) (τ := ρ n) (i := (0 : ℝ≥0)) bot_le
    have hiY0 : Integrable (stoppedProcess Y (ρ n) 0) P := by
      rw [he0, hY0]
      exact ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩
    have hAρ0 : stoppedProcess A (ρ n) 0 =ᵐ[P] 0 := by
      filter_upwards [hA0] with ω hω
      rw [stoppedProcess_eq_of_le (u := A) (τ := ρ n) (i := (0 : ℝ≥0)) bot_le]
      exact hω
    have hMρ : IsLocalMartingale
        (stoppedProcess Y (ρ n) - stoppedProcess A (ρ n)) F P := by
      change IsLocalMartingale (stoppedProcess (Y - A) (ρ n)) F P
      exact hMY.stoppedProcess hF (hρ.isStoppingTime n)
    exact hy.hasMonotonePaths_predictable_compensator haYρ hF
      (hcY.stoppedProcess (ρ n)) hiY0 (hmY.stoppedProcess (ρ n))
      (hpA.stoppedProcess (hρ.isStoppingTime n)) ha hAρ0 hMρ
  filter_upwards [hρ.tendsto_top, ae_all_iff.mpr hmStop] with ω hlim hω s t hst
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
  have hs : (s : WithTop ℝ≥0) ≤ ρ n ω := (WithTop.coe_le_coe.mpr hst).trans hn.le
  have ht : (t : WithTop ℝ≥0) ≤ ρ n ω := hn.le
  have hh := hω n hst
  change stoppedProcess A (ρ n) s ω ≤ stoppedProcess A (ρ n) t ω at hh
  rwa [stoppedProcess_eq_of_le hs, stoppedProcess_eq_of_le ht] at hh

/-- Actual increasing predictable compensator existence and uniqueness on
the locally integrable-variation domain, without an initial L1 hypothesis. -/
theorem HasLocallyIntegrableVariation.exists_unique_monotone_predictable_compensator
    (hvX : HasLocallyIntegrableVariation X F P) (haX : Adapted F X)
    (hF : F.IsUsual P) (hcX : HasCadlagPaths X P) (hmX : HasMonotonePaths X P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale (X - A) F P ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale (X - B) F P → Indistinguishable A B P := by
  obtain ⟨A, hpA, hcA, hA0, hvA, hM, huniq⟩ :=
    hvX.exists_unique_predictable_compensator haX hF hcX
  have hmA := hvX.hasMonotonePaths_predictable_compensator haX hF hcX hmX hpA hvA
    (Eventually.of_forall fun ω ↦ congrFun hA0 ω) hM
  exact ⟨A, hpA, hcA, hA0, hmA, hvA, hM, huniq⟩

end ProbabilityTheory

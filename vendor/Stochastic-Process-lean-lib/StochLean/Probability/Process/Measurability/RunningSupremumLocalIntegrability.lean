/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.RunningSupremum
public import StochLean.Probability.Process.Measurability.RunningJumpSupremum
public import StochLean.Probability.Process.Path.RunningJumpSupremumStopping

/-! # Local integrability from running norm to running jumps

For any adapted AE-cadlag process on a usual filtration, native local
integrability of its original running norm supremum implies the same for
its actual all-times running jump supremum. The existing localizing sequence
is reused unchanged. Only coordinate integrability is assumed, not a
whole-path integrable envelope or any martingale property.

The actual masked stopping identities transfer both suprema to the same
localized process. Its cadlag paths give the factor-two bound and genuine
compact finiteness before real conversion; usual adaptedness supplies
measurability. Initial values and zero lifetimes retain the native mask
semantics, without any moment assumption or finite-measure restriction.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Native local integrability of the original running norm supremum
controls the actual running jump supremum along the same localizing times.
No martingale, specialness, initial moment, or finite measure is assumed. -/
theorem Adapted.locally_integrable_runningJumpSupremum_of_denseRunningSupremum
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hS : Locally (fun Y ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (denseRunningSupremum (fun s v ↦ ‖X s v‖) t ω).toReal) P) :
    Locally (fun Y ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (eRunningJumpSupremum X t ω).toReal) P := by
  obtain ⟨τ, hτ, hiτ⟩ := hS
  refine ⟨τ, hτ, fun n T ↦ ?_⟩
  let Y := stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hcMask := hc.indicator {ω | 0 < τ n ω}
  have hcY : HasCadlagPaths Y P := hcMask.stoppedProcess (τ n)
  have haMask : Adapted F (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) :=
    ha.indicator_initial ((hτ.isStoppingTime n).measurableSet_gt 0)
  have haY : Adapted F Y :=
    (haMask.stronglyAdapted.stoppedProcess_of_usual hF hcMask.hasRightContinuousPaths
      (hτ.isStoppingTime n)).adapted
  have hiS : Integrable (fun ω ↦
      (denseRunningSupremum (fun s v ↦ ‖Y s v‖) T ω).toReal) P := by
    apply (hiτ n T).congr
    filter_upwards [hc] with ω hω
    exact (denseRunningSupremum_norm_masked_stoppedProcess hω.1 (τ n) T).symm
  have hmJ : Measurable (eRunningJumpSupremum Y T) :=
    ((haY.eRunningJumpSupremum_of_usual hF hcY) T).mono (F.le T) le_rfl
  have hiJ : Integrable (fun ω ↦ (eRunningJumpSupremum Y T ω).toReal) P := by
    apply (hiS.const_mul 2).mono' hmJ.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hcY] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hfS := hω.denseRunningSupremum_norm_ne_top T
    have hfJ := hω.eRunningJumpSupremum_ne_top T
    have hf2 : 2 * denseRunningSupremum (fun t v ↦ ‖Y t v‖) T ω ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) hfS
    have ht := (ENNReal.toReal_le_toReal hfJ hf2).mpr (hω.eRunningJumpSupremum_le_two_mul T)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using ht
  apply hiJ.congr
  filter_upwards [hc] with ω hω
  exact hω.eRunningJumpSupremum_toReal_masked_stoppedProcess (τ n) T

end MeasureTheory

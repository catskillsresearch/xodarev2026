/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Multiplication
public import StochLean.Probability.Process.Path.CadlagBounded

/-! # UCP multiplication by a fixed locally bounded or cadlag process

The generic version explicitly assumes measurable output deviations. The
cadlag version derives that measurability from coordinate measurability and
right continuity. No integrability or uniform sample-point bound is imposed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {Y H : ℝ≥0 → Ω → ℝ} {Z : ℕ → ℝ≥0 → Ω → ℝ}

theorem TendstoUCP.mul_right_of_locallyBounded (hu : TendstoUCP P Z atTop Y)
    (hm : ∀ n T, AEMeasurable (compactDeviation (Z n * H) (Y * H) T) P)
    (hb : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ≤ T, ‖H t ω‖ ≤ C) :
    TendstoUCP P (fun n ↦ Z n * H) atTop (Y * H) := by
  apply tendstoUCP_of_subseq_ae_compactDeviation_of_aemeasurable hm
  intro ns hns
  obtain ⟨k, _, hk⟩ := (hu.comp hns).exists_seq_ae_locallyUniform
  refine ⟨k, ?_⟩
  filter_upwards [hk, hb] with ω hω hHω T
  exact tendsto_compactDeviation_mul_right (hω T) (hHω T)

theorem TendstoUCP.mul_right_of_cadlag (hu : TendstoUCP P Z atTop Y)
    (hmZ : ∀ n t, Measurable (Z n t)) (hmY : ∀ t, Measurable (Y t))
    (hmH : ∀ t, Measurable (H t))
    (hrZ : ∀ n, HasCadlagPaths (Z n) P) (hrY : HasCadlagPaths Y P)
    (hrH : HasCadlagPaths H P) :
    TendstoUCP P (fun n ↦ Z n * H) atTop (Y * H) := by
  apply hu.mul_right_of_locallyBounded
  · intro n T
    exact aemeasurable_compactDeviation
      (fun t ↦ (hmZ n t).mul (hmH t)) (fun t ↦ (hmY t).mul (hmH t))
      ((hrZ n).mul hrH).hasRightContinuousPaths (hrY.mul hrH).hasRightContinuousPaths T
  · filter_upwards [hrH] with ω hω T
    obtain ⟨C, _, hC⟩ := hω.exists_norm_bound_Icc T
    exact ⟨C, fun t ht ↦ hC t ⟨bot_le, ht⟩⟩

theorem TendstoUCP.mul_left_of_cadlag (hu : TendstoUCP P Z atTop Y)
    (hmZ : ∀ n t, Measurable (Z n t)) (hmY : ∀ t, Measurable (Y t))
    (hmH : ∀ t, Measurable (H t))
    (hrZ : ∀ n, HasCadlagPaths (Z n) P) (hrY : HasCadlagPaths Y P)
    (hrH : HasCadlagPaths H P) :
    TendstoUCP P (fun n ↦ H * Z n) atTop (H * Y) := by
  simpa only [mul_comm] using hu.mul_right_of_cadlag hmZ hmY hmH hrZ hrY hrH

end ProbabilityTheory

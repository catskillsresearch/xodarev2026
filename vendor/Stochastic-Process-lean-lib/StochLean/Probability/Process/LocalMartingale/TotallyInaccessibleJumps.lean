/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.NonnegativePredictableJump
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumpTests
public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Totally inaccessible nonnegative local-martingale jumps

Actual masked UI localization proves zero jumps at each predictable test.
The genuine large-jump covering theorem then supplies the existing
countable totally-inaccessible-jump property for the original process.

Subtracting an actual continuous process preserves every positive-time
jump on one event. Consequently, a cadlag process with nonnegative jumps
and a local-martingale remainder after such subtraction also has totally
inaccessible jumps. The continuous process need not start at zero; the
source initial jump is deliberately outside this classification.
No finite variation, initial moment, or target classification certificate
is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M X A : ℝ≥0 → Ω → ℝ}

/-- A native local martingale with nonnegative positive-time jumps has a
genuine countable totally inaccessible covering of those jumps. -/
theorem IsLocalMartingale.hasTotallyInaccessibleJumps_of_nonneg_jumps
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → 0 ≤ jumpProcess M t ω) :
    HasTotallyInaccessibleJumps F M P :=
  hM.1.hasTotallyInaccessibleJumps_of_predictable_tests hF hM.2.1
    (fun _ hσ ↦ hM.ae_jumpProcess_eq_zero_at_predictable_of_nonneg_jumps hF hj hσ)

/-- An actual continuous subtraction and local-martingale remainder
classify the original nonnegative positive-time jumps as totally
inaccessible. No predictability, finite variation or adaptedness of the
continuous term is separately needed for this jump-graph conclusion. -/
theorem hasTotallyInaccessibleJumps_of_localMartingale_sub_continuous
    (hM : IsLocalMartingale (X - A) F P) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hcA : HasContinuousPaths A P)
    (hjX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → 0 ≤ jumpProcess X t ω) :
    HasTotallyInaccessibleJumps F X P := by
  have he : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      jumpProcess (X - A) t ω = jumpProcess X t ω := by
    filter_upwards [hcX, hcA] with ω hX hA t ht
    rw [hX.jumpProcess_sub hA.isCadlagPath, hA.jumpProcess_eq_zero ht.ne', sub_zero]
  have hjM : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → 0 ≤ jumpProcess (X - A) t ω := by
    filter_upwards [he, hjX] with ω hω hj t ht
    rw [hω t ht]
    exact hj t ht
  obtain ⟨σ, hσ, hcover⟩ := hM.hasTotallyInaccessibleJumps_of_nonneg_jumps hF hjM
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [he, hcover] with ω heω hcω t ht hj
  apply hcω t ht
  rw [heω t ht]
  exact hj

end ProbabilityTheory

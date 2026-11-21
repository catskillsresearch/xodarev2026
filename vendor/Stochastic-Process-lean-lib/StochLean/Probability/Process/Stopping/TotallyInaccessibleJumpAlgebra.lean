/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps
public import StochLean.Probability.Process.Path.LeftLimitAddition
public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Linear stability of totally inaccessible positive-time jumps

Actual countable jump coverings are combined without enumerating any new
jumps. The path hypotheses justify exact jump algebra on one common event.
Continuous corrections need no initial normalization: the covering predicate
concerns positive-time jumps and does not constrain the source initial value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem HasTotallyInaccessibleJumps.add
    (hX : HasTotallyInaccessibleJumps F X P) (hY : HasTotallyInaccessibleJumps F Y P)
    (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    HasTotallyInaccessibleJumps F (X + Y) P := by
  classical
  obtain ⟨σ, hσ, hcovX⟩ := hX
  obtain ⟨ρ, hρ, hcovY⟩ := hY
  let θ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦
    if n.unpair.2 = 0 then σ n.unpair.1 else ρ n.unpair.1
  refine ⟨θ, ?_, ?_⟩
  · intro n
    dsimp only [θ]
    split_ifs
    · exact hσ _
    · exact hρ _
  · filter_upwards [hcX, hcY, hcovX, hcovY] with ω hx hy hcx hcy
    intro t ht hj
    by_cases hz : jumpProcess X t ω = 0
    · have hne : jumpProcess Y t ω ≠ 0 := by
        intro he
        apply hj
        rw [hx.jumpProcess_add hy, hz, he, zero_add]
      obtain ⟨n, hn⟩ := hcy t ht hne
      exact ⟨Nat.pair n 1, by simpa only [θ, Nat.unpair_pair, one_ne_zero, if_false] using hn⟩
    · obtain ⟨n, hn⟩ := hcx t ht hz
      exact ⟨Nat.pair n 0, by simpa only [θ, Nat.unpair_pair, ite_true] using hn⟩

theorem HasTotallyInaccessibleJumps.const_mul
    (hX : HasTotallyInaccessibleJumps F X P) (hcX : HasCadlagPaths X P) (c : ℝ) :
    HasTotallyInaccessibleJumps F (fun t ω ↦ c * X t ω) P := by
  obtain ⟨σ, hσ, hcover⟩ := hX
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hcX, hcover] with ω hc hω
  intro t ht hj
  apply hω t ht
  intro hz
  apply hj
  rw [hc.jumpProcess_const_mul, hz, mul_zero]

theorem HasTotallyInaccessibleJumps.neg
    (hX : HasTotallyInaccessibleJumps F X P) (hcX : HasCadlagPaths X P) :
    HasTotallyInaccessibleJumps F (-X) P := by
  simpa only [neg_one_mul, Pi.neg_def] using hX.const_mul hcX (-1)

theorem HasTotallyInaccessibleJumps.sub
    (hX : HasTotallyInaccessibleJumps F X P) (hY : HasTotallyInaccessibleJumps F Y P)
    (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    HasTotallyInaccessibleJumps F (X - Y) P := by
  have hcneg : HasCadlagPaths (-Y) P := hcY.continuous_comp continuous_neg
  simpa only [sub_eq_add_neg] using hX.add (hY.neg hcY) hcX hcneg

theorem HasTotallyInaccessibleJumps.add_continuous
    (hX : HasTotallyInaccessibleJumps F X P) (hcX : HasCadlagPaths X P)
    (hcY : HasContinuousPaths Y P) : HasTotallyInaccessibleJumps F (X + Y) P :=
  hX.add (hcY.hasTotallyInaccessibleJumps F) hcX
    (hcY.mono fun _ hω ↦ IsContinuousPath.isCadlagPath hω)

theorem HasTotallyInaccessibleJumps.sub_continuous
    (hX : HasTotallyInaccessibleJumps F X P) (hcX : HasCadlagPaths X P)
    (hcY : HasContinuousPaths Y P) : HasTotallyInaccessibleJumps F (X - Y) P :=
  hX.sub (hcY.hasTotallyInaccessibleJumps F) hcX
    (hcY.mono fun _ hω ↦ IsContinuousPath.isCadlagPath hω)

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.FiniteExtension
public import StochLean.Probability.Brownian.Construction
public import StochLean.Probability.Brownian.QuadraticVariationMoments

/-! # Genuine partition dependence and the order of Brownian QV quantifiers

A deterministic continuous path is extracted from the constructed Brownian law.
Its dyadic square sums converge to one, but another genuine nested admissible
infinite sequence, chosen from that path, gives zero at the same horizon.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

open BrownianReal

theorem exists_continuous_partition_dependent_quadraticVariation :
    ∃ (x : ℝ≥0 → ℝ) (P : ℕ → LocallyFinitePartition), Continuous x ∧
      IsAdmissiblePartitionSequence P ∧
      HasQuadraticVariationAlong (fun n ↦ (P n).restrict 1) x 0 ∧
      HasQuadraticVariationAlong (fun n ↦ (LocallyFinitePartition.dyadic n).restrict 1) x 1 := by
  have hm : Summable (fun n ↦ (((LocallyFinitePartition.dyadic n).restrict 1).mesh : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ NNReal.coe_nonneg _) _
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    intro n
    have h := (LocallyFinitePartition.dyadic n).restrict_mesh_le 1 |>.trans
      (LocallyFinitePartition.uniform_mesh_le ((1 / 2 : ℝ≥0) ^ n) (pow_pos (by norm_num) n))
    exact_mod_cast ENNReal.coe_le_coe.mp h
  have hqv := isBrownianReal_brownianCoordinate.toIsPreBrownianReal
    |>.ae_quadraticVariationAlong_of_summable_mesh hm
  obtain ⟨ω, hω⟩ := hqv.exists
  have hx := continuous_brownianCoordinate ω
  obtain ⟨P, hP, hq⟩ := exists_admissible_zeroQuadraticVariation (T := 1) hx.continuousOn
  exact ⟨_, P, hx, hP, hq, hω⟩

/-- The null set may depend on the prescribed admissible sequence. There is no
single probability-one event on which the time bracket works for every sequence. -/
theorem IsBrownianReal.not_ae_forall_admissible_quadraticVariation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ¬ (∀ᵐ ω ∂P, ∀ π : ℕ → LocallyFinitePartition, IsAdmissiblePartitionSequence π →
      HasQuadraticVariationAlong (fun n ↦ (π n).restrict 1) (B · ω) 1) := by
  intro h
  obtain ⟨ω, hc, hω⟩ := (hB.cont.and h).exists
  obtain ⟨π, hπ, hz⟩ := exists_admissible_zeroQuadraticVariation (T := 1) hc.continuousOn
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique hz (hω π hπ)
  norm_num at he

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.ReflectionLaw
public import StochLean.Probability.Brownian.QuadraticVariationMoments
public import StochLean.Probability.Conditional.Symmetry
public import StochLean.Analysis.PathVariation.TotalVariation

/-! # Brownian cross increments conditionally centered by finer square sums

Flipping one cell changes the sign of its cross product with any different cell, but preserves
the square sum on every finer partition. The argument concerns the joint law with the entire
sequence of finer sums, not merely pairwise independence.
-/

@[expose] public section

open MeasureTheory Set Filter Finset StochLean
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem measurable_quadraticVariationSum (π : TimePartition T) :
    Measurable (quadraticVariationSum π) := by
  unfold quadraticVariationSum TimePartition.increment
  fun_prop

theorem IsPreBrownianReal.condExp_partitionIncrement_mul_eq_zero
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (π : TimePartition T) (ρ : ℕ → TimePartition T) (hρ : ∀ n, (ρ n).Refines π)
    {i j : Fin π.size} (hij : i ≠ j) :
    P[(fun ω ↦ π.increment (B · ω) i * π.increment (B · ω) j) |
      (inferInstance : MeasurableSpace (ℕ → ℝ)).comap
        (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω))] =ᵐ[P] 0 := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hp (k : Fin π.size) : MemLp (fun ω ↦ π.increment (B · ω) k) 2 P :=
    (hB.hasLaw_partitionIncrement π k).hasGaussianLaw.memLp_two
  have hpath : Measurable (fun ω ↦ (B · ω)) := measurable_pi_lambda _ hBm
  have hQ : Measurable (fun f : ℝ≥0 → ℝ ↦ fun n ↦ quadraticVariationSum (ρ n) f) :=
    measurable_pi_lambda _ (fun n ↦ measurable_quadraticVariationSum (ρ n))
  apply condExp_eq_zero_of_joint_neg ((hp i).integrable_mul (hp j)) (hQ.comp hpath)
  have hobs : Measurable (fun f : ℝ≥0 → ℝ ↦
      (π.increment f i * π.increment f j, fun n ↦ quadraticVariationSum (ρ n) f)) := by
    apply Measurable.prodMk _ hQ
    unfold TimePartition.increment
    fun_prop
  have hid := (hB.identDistrib_flipInterval hBm (π.left_le_right i)).comp hobs
  have heq : (fun ω ↦
      (π.increment (ProbabilityTheory.flipInterval B (π.left i) (π.right i) · ω) i *
        π.increment (ProbabilityTheory.flipInterval B (π.left i) (π.right i) · ω) j,
        fun n ↦ quadraticVariationSum (ρ n)
          (ProbabilityTheory.flipInterval B (π.left i) (π.right i) · ω))) =
      (fun ω ↦ (-(π.increment (B · ω) i * π.increment (B · ω) j),
        fun n ↦ quadraticVariationSum (ρ n) (B · ω))) := by
    funext ω
    apply Prod.ext
    · change π.increment (flipIntervalPath (B · ω) (π.left i) (π.right i)) i *
        π.increment (flipIntervalPath (B · ω) (π.left i) (π.right i)) j = _
      rw [π.increment_flipIntervalPath_self, π.increment_flipIntervalPath_of_ne _ hij,
        neg_mul]
    · funext n
      exact quadraticVariationSum_flipIntervalPath (ρ n) (B · ω) (π.left_le_right i)
        (hρ n ⟨i.castSucc, rfl⟩) (hρ n ⟨i.succ, rfl⟩)
  simpa only [Function.comp_def, heq, Pi.mul_apply] using hid

/-- Fine square sums remove every cross term of the terminal square. This equality does not
yet require the current square sum itself to be measurable in the conditioning sigma-field. -/
theorem IsPreBrownianReal.condExp_terminal_sq_eq_condExp_quadraticVariationSum
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (π : TimePartition T) (ρ : ℕ → TimePartition T) (hρ : ∀ n, (ρ n).Refines π) :
    P[(fun ω ↦ (B T ω) ^ 2) |
      (inferInstance : MeasurableSpace (ℕ → ℝ)).comap
        (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω))] =ᵐ[P]
    P[(fun ω ↦ quadraticVariationSum π (B · ω)) |
      (inferInstance : MeasurableSpace (ℕ → ℝ)).comap
        (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω))] := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let Z : Fin π.size → Ω → ℝ := fun i ω ↦ π.increment (B · ω) i
  let G := (inferInstance : MeasurableSpace (ℕ → ℝ)).comap
    (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω))
  have hp (i : Fin π.size) : MemLp (Z i) 2 P :=
    (hB.hasLaw_partitionIncrement π i).hasGaussianLaw.memLp_two
  have hcross (i j : Fin π.size) (hij : i ≠ j) : P[Z i * Z j | G] =ᵐ[P] 0 :=
    hB.condExp_partitionIncrement_mul_eq_zero hBm π ρ hρ hij
  have hsum := condExp_sq_sum_of_cross_zero Z hp G hcross
  have hdiag := condExp_finsetSum (s := Finset.univ)
    (fun i _ ↦ (hB.memLp_partitionIncrement_sq π i).integrable (by norm_num)) G
  have hzero : (fun ω ↦ (B T ω) ^ 2) =ᵐ[P] (fun ω ↦ (∑ i, Z i ω) ^ 2) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp only [Z, π.sum_increment, hω, sub_zero]
  apply (condExp_congr_ae hzero).trans
  apply hsum.trans
  convert hdiag.symm using 1
  congr 1
  funext ω
  simp only [Finset.sum_apply, quadraticVariationSum]

/-- When the current partition is included, the terminal conditional square is exactly its
quadratic increment sum. No mesh or rate hypothesis is needed for this finite identity. -/
theorem IsPreBrownianReal.condExp_terminal_sq_eq_quadraticVariationSum
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (π : TimePartition T) (ρ : ℕ → TimePartition T) (hρ : ∀ n, (ρ n).Refines π)
    (hfirst : ρ 0 = π) :
    P[(fun ω ↦ (B T ω) ^ 2) |
      (inferInstance : MeasurableSpace (ℕ → ℝ)).comap
        (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω))] =ᵐ[P]
      fun ω ↦ quadraticVariationSum π (B · ω) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply (hB.condExp_terminal_sq_eq_condExp_quadraticVariationSum hBm π ρ hρ).trans
  have hQ : Measurable (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω)) :=
    measurable_pi_lambda _ (fun n ↦ (measurable_quadraticVariationSum (ρ n)).comp
      (measurable_pi_lambda _ hBm))
  have hm := (measurable_pi_apply 0).comp
    (comap_measurable (fun ω n ↦ quadraticVariationSum (ρ n) (B · ω)))
  have hm' := hm.stronglyMeasurable
  simp only [Function.comp_def, hfirst] at hm'
  exact Eventually.of_forall (congrFun (condExp_of_stronglyMeasurable hQ.comap_le hm'
    ((hB.memLp_quadraticVariationSum π).integrable (by norm_num))))

end ProbabilityTheory

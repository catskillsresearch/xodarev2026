/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.BoundedInProbability
public import StochLean.Probability.Process.Semimartingale.Quasimartingale
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # The conditional-variation sign integrand

For a deterministic partition, the coefficient on each interval is the sign
that turns the conditional expected increment into its absolute value.  The
zero case is assigned coefficient `-1`; consequently every coefficient has
norm exactly one and the resulting source simple predictable process belongs
to the unit ball without an exceptional-set convention.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ} {Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- Coefficient which pairs the forward increment with the absolute value of
the conditional backward increment. -/
noncomputable def conditionalVariationCoefficient {T : ℝ≥0}
    (π : StochLean.TimePartition T) (i : Fin π.size) : Ω → ℝ :=
  fun ω ↦ if 0 ≤ Q[X (π.left i) - X (π.right i) | F (π.left i)] ω then -1 else 1

theorem measurable_conditionalVariationCoefficient {T : ℝ≥0}
    (π : StochLean.TimePartition T) (i : Fin π.size) :
    Measurable[F (π.left i)]
      (conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i) := by
  let D : Ω → ℝ := Q[X (π.left i) - X (π.right i) | F (π.left i)]
  have hD : Measurable[F (π.left i)] D := stronglyMeasurable_condExp.measurable
  exact Measurable.piecewise (measurableSet_le measurable_const hD)
    measurable_const measurable_const

@[simp] theorem norm_conditionalVariationCoefficient {T : ℝ≥0}
    (π : StochLean.TimePartition T) (i : Fin π.size) (ω : Ω) :
    ‖conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i ω‖ = 1 := by
  rw [conditionalVariationCoefficient]
  split_ifs <;> norm_num

/-- Deterministic-partition source representation used to read conditional
variation from elementary integrals. -/
noncomputable def conditionalVariationSignRep {T : ℝ≥0}
    (π : StochLean.TimePartition T) : SimplePredictableRep F where
  partition := StoppingTimePartition.deterministic F π
  initial := fun _ ↦ 0
  measurable_initial := measurable_const
  coefficient := conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π
  measurable_coefficient := fun i ↦ by
    change Measurable[(isStoppingTime_const F (π.left i)).measurableSpace]
      (conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i)
    rw [IsStoppingTime.measurableSpace_const]
    exact measurable_conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i

theorem conditionalVariationSignRep_toProcess_norm_le_one {T : ℝ≥0}
    (π : StochLean.TimePartition T) (t : ℝ≥0) (ω : Ω) :
    ‖(conditionalVariationSignRep (F := F) (Q := Q) (X := X) π).toProcess t ω‖ ≤ 1 := by
  rw [SimplePredictableRep.toProcess]
  by_cases ht : t = 0
  · simp [ht, conditionalVariationSignRep]
  · rw [if_neg ht]
    change ‖∑ j : Fin π.size,
      if π.left j < t ∧ t ≤ π.right j then
        conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π j ω
      else 0‖ ≤ 1
    by_cases hcell : ∃ i : Fin π.size, π.left i < t ∧ t ≤ π.right i
    · obtain ⟨i, hi⟩ := hcell
      rw [Fintype.sum_eq_single i]
      · rw [if_pos]
        · rw [norm_conditionalVariationCoefficient
            (F := F) (Q := Q) (X := X) π i ω]
        · exact hi
      · intro j hji
        rcases lt_or_gt_of_ne hji with hji | hij
        · have hle : π.right j ≤ π.left i :=
            π.monotone_point (show j.succ ≤ i.castSucc from hji)
          have : ¬(π.left j < t ∧ t ≤ π.right j) := fun hj ↦
            (not_le_of_gt hi.1) (hj.2.trans hle)
          rw [if_neg]
          simpa [StochLean.TimePartition.left, StochLean.TimePartition.right] using this
        · have hle : π.right i ≤ π.left j :=
            π.monotone_point (show i.succ ≤ j.castSucc from hij)
          have : ¬(π.left j < t ∧ t ≤ π.right j) := fun hj ↦
            (not_lt_of_ge (hi.2.trans hle)) hj.1
          rw [if_neg]
          simpa [StochLean.TimePartition.left, StochLean.TimePartition.right] using this
    · have hnone : ∀ i : Fin π.size, ¬(π.left i < t ∧ t ≤ π.right i) :=
        fun i hi ↦ hcell ⟨i, hi⟩
      change ‖∑ j : Fin π.size,
        if π.left j < t ∧ t ≤ π.right j then
          conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π j ω
        else 0‖ ≤ 1
      simp only [if_neg (hnone _), sum_const_zero, norm_zero]
      norm_num

theorem conditionalVariationSignRep_isSimplePredictable {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    IsSimplePredictable
      (conditionalVariationSignRep (F := F) (Q := Q) (X := X) π).toProcess F :=
  ⟨conditionalVariationSignRep (F := F) (Q := Q) (X := X) π, rfl⟩

/-- Every conditional-variation sign integral lies in the same unit
elementary-integral image used by the bounded-in-probability argument. -/
theorem conditionalVariationSignRep_integral_mem_unitElementaryIntegralSet {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    (conditionalVariationSignRep (F := F) (Q := Q) (X := X) π).integral X ∈
      unitElementaryIntegralSet X F := by
  let R := conditionalVariationSignRep (F := F) (Q := Q) (X := X) π
  let hR : IsSimplePredictable R.toProcess F :=
    conditionalVariationSignRep_isSimplePredictable (F := F) (Q := Q) (X := X) π
  refine ⟨R.toProcess, hR, ?_, ?_⟩
  · exact fun t ω ↦ conditionalVariationSignRep_toProcess_norm_le_one
      (F := F) (Q := Q) (X := X) π t ω
  · exact (hR.elementaryIntegral_eq R rfl X).symm

theorem conditionalVariationSignRep_integral_eq_sum {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    (conditionalVariationSignRep (F := F) (Q := Q) (X := X) π).integral X =
      fun ω ↦ ∑ i : Fin π.size,
        conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i ω *
          (X (π.right i) ω - X (π.left i) ω) := by
  funext ω
  simp [SimplePredictableRep.integral, conditionalVariationSignRep,
    StoppingTimePartition.deterministic, StochLean.TimePartition.left,
    StochLean.TimePartition.right]
  rfl

section FiniteMeasure

variable [IsFiniteMeasure Q]

theorem integrable_conditionalVariationCoefficient_mul_increment
    {R : Measure Ω} (hi : ∀ t, Integrable (X t) Q) {T : ℝ≥0}
    (π : StochLean.TimePartition T) (i : Fin π.size) :
    Integrable (fun ω ↦
      conditionalVariationCoefficient (F := F) (Q := R) (X := X) π i ω *
        (X (π.right i) ω - X (π.left i) ω)) Q := by
  have hb : ∀ᵐ ω ∂Q,
      ‖conditionalVariationCoefficient (F := F) (Q := R) (X := X) π i ω‖ ≤ 1 := by
    filter_upwards [] with ω
    rw [norm_conditionalVariationCoefficient (F := F) (Q := R) (X := X) π i ω]
  simpa only [Pi.sub_apply] using
    ((hi (π.right i)).sub (hi (π.left i))).bdd_mul (c := 1)
      ((measurable_conditionalVariationCoefficient
        (F := F) (Q := R) (X := X) π i).mono
          (F.le (π.left i)) le_rfl).aestronglyMeasurable hb

theorem integrable_conditionalVariationSignRep_integral
    {R : Measure Ω} (hi : ∀ t, Integrable (X t) Q) {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    Integrable
      ((conditionalVariationSignRep (F := F) (Q := R) (X := X) π).integral X) Q := by
  rw [conditionalVariationSignRep_integral_eq_sum]
  exact integrable_finsetSum Finset.univ fun i _ ↦
    integrable_conditionalVariationCoefficient_mul_increment
      (F := F) (Q := Q) (R := R) (X := X) hi π i

/-- The sign coefficient converts one forward increment into the absolute
conditional decrement after integration. -/
theorem integral_conditionalVariationCoefficient_mul_increment
    (hi : ∀ t, Integrable (X t) Q) {T : ℝ≥0}
    (π : StochLean.TimePartition T) (i : Fin π.size) :
    (∫ ω, conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i ω *
        (X (π.right i) ω - X (π.left i) ω) ∂Q) =
      ∫ ω, |Q[X (π.left i) - X (π.right i) | F (π.left i)] ω| ∂Q := by
  let c := conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i
  let d : Ω → ℝ := X (π.left i) - X (π.right i)
  let e : Ω → ℝ := X (π.right i) - X (π.left i)
  have heq : e = -d := by
    funext ω
    simp only [e, d, Pi.sub_apply, Pi.neg_apply]
    ring
  have he : Integrable e Q := (hi (π.right i)).sub (hi (π.left i))
  have hce : Q[e | F (π.left i)] =ᵐ[Q] -Q[d | F (π.left i)] := by
    rw [heq]
    exact condExp_neg d (F (π.left i))
  have hprod : Integrable (c * e) Q := by
    change Integrable (fun ω ↦
      conditionalVariationCoefficient (F := F) (Q := Q) (X := X) π i ω *
        (X (π.right i) ω - X (π.left i) ω)) Q
    exact integrable_conditionalVariationCoefficient_mul_increment
      (F := F) (Q := Q) (R := Q) (X := X) hi π i
  have hpull : Q[c * e | F (π.left i)] =ᵐ[Q] c * Q[e | F (π.left i)] :=
    condExp_mul_of_stronglyMeasurable_left
      (measurable_conditionalVariationCoefficient
        (F := F) (Q := Q) (X := X) π i).stronglyMeasurable hprod he
  have hsign : c * (-Q[d | F (π.left i)]) =ᵐ[Q]
      fun ω ↦ |Q[d | F (π.left i)] ω| := by
    filter_upwards [] with ω
    change (if 0 ≤ Q[d | F (π.left i)] ω then -1 else 1) *
        (-Q[d | F (π.left i)] ω) = |Q[d | F (π.left i)] ω|
    by_cases h : 0 ≤ Q[d | F (π.left i)] ω
    · simp [h, abs_of_nonneg h]
    · have h' : Q[d | F (π.left i)] ω < 0 := lt_of_not_ge h
      simp [h, abs_of_neg h']
  have hmul : c * Q[e | F (π.left i)] =ᵐ[Q]
      c * (-Q[d | F (π.left i)]) := by
    filter_upwards [hce] with ω hω
    exact congrArg (fun z ↦ c ω * z) hω
  have hall : Q[c * e | F (π.left i)] =ᵐ[Q]
      fun ω ↦ |Q[d | F (π.left i)] ω| :=
    hpull.trans (hmul.trans hsign)
  change (∫ ω, (c * e) ω ∂Q) = ∫ ω, |Q[d | F (π.left i)] ω| ∂Q
  exact (integral_condExp (F.le (π.left i))).symm.trans (integral_congr_ae hall)

/-- The expectation of the full sign integral is the sum of the absolute
conditional decrements along the deterministic partition. -/
theorem integral_conditionalVariationSignRep_integral
    (hi : ∀ t, Integrable (X t) Q) {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    (∫ ω, (conditionalVariationSignRep (F := F) (Q := Q) (X := X) π).integral X ω ∂Q) =
      ∑ i, ∫ ω, |Q[X (π.left i) - X (π.right i) | F (π.left i)] ω| ∂Q := by
  rw [conditionalVariationSignRep_integral_eq_sum]
  rw [integral_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i hi'
    exact integral_conditionalVariationCoefficient_mul_increment
      (F := F) (Q := Q) (X := X) hi π i
  · intro i hi'
    exact integrable_conditionalVariationCoefficient_mul_increment
      (F := F) (Q := Q) (R := Q) (X := X) hi π i

/-- The expected conditional-variation sum splits into the sign elementary
integral and the artificial terminal-zero tail. -/
theorem integral_conditionalVariationSum_eq_signRep_add_terminal
    (hi : ∀ t, Integrable (X t) Q) {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    (∫ ω, conditionalVariationSum X F Q π ω ∂Q) =
      (∫ ω, (conditionalVariationSignRep
          (F := F) (Q := Q) (X := X) π).integral X ω ∂Q) +
        ∫ ω, |X T ω| ∂Q := by
  have hterms : ∀ i : Fin π.size,
      Integrable (fun ω ↦
        |Q[X (π.left i) - X (π.right i) | F (π.left i)] ω|) Q :=
    fun i ↦ (integrable_condExp
      (f := X (π.left i) - X (π.right i)) (m := F (π.left i))).abs
  rw [show conditionalVariationSum X F Q π = fun ω ↦
      (∑ i, |Q[X (π.left i) - X (π.right i) | F (π.left i)] ω|) +
        |X T ω| by
      funext ω
      simp only [conditionalVariationSum, sub_zero]]
  rw [integral_add (integrable_finsetSum Finset.univ fun i _ ↦ hterms i) (hi T).abs,
    integral_finset_sum Finset.univ (fun i _ ↦ hterms i),
    integral_conditionalVariationSignRep_integral (F := F) (Q := Q) (X := X) hi π]

end FiniteMeasure

end ProbabilityTheory

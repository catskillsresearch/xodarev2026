/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TotalVariation
public import StochLean.Analysis.PathVariation.UniformPartition
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Data.Real.Sign
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.TietzeExtension

/-!
# Protter I.56: naive pathwise integration forces finite variation

For a finite partition, evaluation of a continuous integrand at the left endpoints,
followed by pairing with the increments of a path, is a continuous linear functional.
Tietze extension shows that its operator norm dominates the one-variation sum of the
path.  The uniform boundedness principle therefore turns pointwise convergence of
all such left sums into a uniform bound on the variation sums.  Their deterministic
mesh limit is the total variation.

The last theorem is Protter I.56 for the dyadic rational partitions of `[0,1]`.
The preceding theorem is slightly stronger: refinement is not needed, only strict
partitions whose mesh tends to zero.

The stochastic measurable-selection observation in the paragraph following the
numbered theorem is not folded into this deterministic statement: it additionally
requires selecting random continuous integrands on the infinite-variation event.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction BigOperators

namespace StochLean

variable {T : ℝ≥0}

namespace TimePartition

/-- A partition's left endpoint, regarded as a point of its compact time interval. -/
def leftPoint (π : TimePartition T) (i : Fin π.size) : Set.Icc (0 : ℝ≥0) T :=
  ⟨π.left i, bot_le, (π.point_le_horizon i.castSucc)⟩

/-- The naive left-endpoint sum against the increments of `x`. -/
def naiveLeftSum (π : TimePartition T) (x : ℝ≥0 → ℝ)
    (h : Set.Icc (0 : ℝ≥0) T →ᵇ ℝ) : ℝ :=
  ∑ i, h (π.leftPoint i) * π.increment x i

/-- The naive left sum as a continuous linear functional of the integrand. -/
noncomputable def naiveLeftSumCLM (π : TimePartition T) (x : ℝ≥0 → ℝ) :
    (Set.Icc (0 : ℝ≥0) T →ᵇ ℝ) →L[ℝ] ℝ :=
  ∑ i, (π.increment x i) •
    BoundedContinuousFunction.evalCLM ℝ (π.leftPoint i)

@[simp]
theorem naiveLeftSumCLM_apply (π : TimePartition T) (x : ℝ≥0 → ℝ)
    (h : Set.Icc (0 : ℝ≥0) T →ᵇ ℝ) :
    π.naiveLeftSumCLM x h = π.naiveLeftSum x h := by
  simp [naiveLeftSumCLM, naiveLeftSum, mul_comm]

/-- On a strict partition, the one-variation sum is bounded by the operator norm of
the corresponding naive left-sum functional.  The witnessing integrand is a
continuous extension of the signs of the increments at the left endpoints. -/
theorem pVariationSum_one_le_norm_naiveLeftSumCLM (π : TimePartition T)
    (hπ : StrictMono π.point) (x : ℝ≥0 → ℝ) :
    pVariationSum 1 π x ≤ ‖π.naiveLeftSumCLM x‖ := by
  classical
  let e : Fin π.size → Set.Icc (0 : ℝ≥0) T := π.leftPoint
  let s : Set (Set.Icc (0 : ℝ≥0) T) := Set.range e
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.castSucc_injective π.size
    apply hπ.injective
    exact congrArg Subtype.val hij
  have hsfinite : s.Finite := Set.finite_range e
  let _ : Finite s := hsfinite.to_subtype
  let index : s → Fin π.size := fun y ↦ Classical.choose y.property
  have hindex (y : s) : e (index y) = y.1 := Classical.choose_spec y.property
  have hindex_e (i : Fin π.size) : index ⟨e i, Set.mem_range_self i⟩ = i := by
    apply he
    exact hindex ⟨e i, Set.mem_range_self i⟩
  have hsign_norm (r : ℝ) : ‖Real.sign r‖ ≤ 1 := by
    rcases Real.sign_apply_eq r with hr | hr | hr <;> simp [hr]
  let signOnLeft : s →ᵇ ℝ :=
    { toFun := fun y ↦ Real.sign (π.increment x (index y))
      continuous_toFun := continuous_of_discreteTopology
      map_bounded' := ⟨2, fun y z ↦ by
        calc
          dist (Real.sign (π.increment x (index y)))
              (Real.sign (π.increment x (index z)))
              ≤ ‖Real.sign (π.increment x (index y))‖ +
                  ‖Real.sign (π.increment x (index z))‖ := dist_le_norm_add_norm _ _
          _ ≤ 1 + 1 := add_le_add (hsign_norm _) (hsign_norm _)
          _ = 2 := by norm_num⟩ }
  have hsignOnLeft_norm : ‖signOnLeft‖ ≤ 1 :=
    (BoundedContinuousFunction.norm_le zero_le_one).2 fun y ↦ hsign_norm _
  obtain ⟨g, hg_norm, hg_restrict⟩ :=
    BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed
      signOnLeft hsfinite.isClosed
  have hg_norm_le : ‖g‖ ≤ 1 := hg_norm.trans_le hsignOnLeft_norm
  have hg_left (i : Fin π.size) :
      g (π.leftPoint i) = Real.sign (π.increment x i) := by
    have h := DFunLike.congr_fun hg_restrict ⟨e i, Set.mem_range_self i⟩
    change g (e i) = Real.sign (π.increment x (index ⟨e i, Set.mem_range_self i⟩)) at h
    simpa only [hindex_e i] using h
  have hsign_mul (r : ℝ) : Real.sign r * r = |r| := by
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · rw [Real.sign_of_neg hr, abs_of_neg hr]
      ring
    · simp
    · rw [Real.sign_of_pos hr, abs_of_pos hr]
      ring
  have hsum : π.naiveLeftSum x g = ∑ i, |π.increment x i| := by
    unfold naiveLeftSum
    apply sum_congr rfl
    intro i _
    rw [hg_left, hsign_mul]
  have hsum_nonneg : 0 ≤ π.naiveLeftSum x g := by
    rw [hsum]
    exact sum_nonneg fun _ _ ↦ abs_nonneg _
  calc
    pVariationSum 1 π x = ∑ i, |π.increment x i| := pVariationSum_one π x
    _ = π.naiveLeftSum x g := hsum.symm
    _ = ‖π.naiveLeftSumCLM x g‖ := by
      rw [naiveLeftSumCLM_apply, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    _ ≤ ‖π.naiveLeftSumCLM x‖ :=
      (π.naiveLeftSumCLM x).unit_le_opNorm g hg_norm_le

end TimePartition

namespace LocallyFinitePartition

/-- Finite restrictions of locally finite partitions use their sorted endpoint set,
so their endpoint enumeration is strict. -/
theorem strictMono_restrict (P : LocallyFinitePartition) (T : ℝ≥0) :
    StrictMono (P.restrict T).point := by
  unfold restrict
  exact TimePartition.ofFinset_strictMono _ _ _ _

end LocallyFinitePartition

/-- General uniform-boundedness form of Protter I.56.  Right continuity is needed
only on the compact interval, and the partitions need not be nested. -/
theorem boundedVariationOn_of_tendsto_naiveLeftSum
    (x : ℝ≥0 → ℝ)
    (hx : ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      ContinuousWithinAt x (Set.Icc t T) t)
    (π : ℕ → TimePartition T)
    (hπ : ∀ n, StrictMono (π n).point)
    (hmesh : Tendsto (fun n ↦ (((π n).mesh : ℝ))) atTop (𝓝 0))
    (hconv : ∀ h : Set.Icc (0 : ℝ≥0) T →ᵇ ℝ, ∃ a : ℝ,
      Tendsto (fun n ↦ (π n).naiveLeftSum x h) atTop (𝓝 a)) :
    BoundedVariationOn x (Set.Icc 0 T) := by
  have hpointwise : ∀ h : Set.Icc (0 : ℝ≥0) T →ᵇ ℝ,
      ∃ C : ℝ, ∀ n, ‖(π n).naiveLeftSumCLM x h‖ ≤ C := by
    intro h
    obtain ⟨a, ha⟩ := hconv h
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ha).exists_norm_le
    refine ⟨C, fun n ↦ ?_⟩
    rw [TimePartition.naiveLeftSumCLM_apply]
    exact hC _ ⟨n, rfl⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun n ↦ (π n).naiveLeftSumCLM x) hpointwise
  have hvariation (n : ℕ) : pVariationSum 1 (π n) x ≤ C :=
    ((π n).pVariationSum_one_le_norm_naiveLeftSumCLM (hπ n) x).trans (hC n)
  have hlimit : Tendsto
      (fun n ↦ ENNReal.ofReal (pVariationSum 1 (π n) x)) atTop
      (𝓝 (eVariationOn x (Set.Icc 0 T))) := by
    apply tendsto_oneVariationSum_of_ceiling_tendsto
    intro t ht
    apply (hx t ht).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨TimePartition.ceilingPoint_tendsto hmesh ht.2,
      Eventually.of_forall (fun n ↦ ?_)⟩
    have hle := (π n).min_le_ceilingPoint t
    rw [min_eq_left ht.2] at hle
    exact ⟨hle, (π n).ceilingPoint_le_horizon t⟩
  have htotal : eVariationOn x (Set.Icc 0 T) ≤ ENNReal.ofReal C :=
    le_of_tendsto hlimit <| Eventually.of_forall fun n ↦
      ENNReal.ofReal_le_ofReal (hvariation n)
  exact (htotal.trans_lt ENNReal.ofReal_lt_top).ne

/-- **Protter I.56 (Naive Integration).**  Let `x` be right-continuous on `[0,1]`.
If, along the dyadic rational partitions, every continuous integrand's naive
left-endpoint sums converge, then `x` has finite variation on `[0,1]`. -/
theorem protter_I_56_naiveIntegration_impossible
    (x : ℝ≥0 → ℝ)
    (hx : ∀ t ∈ Set.Icc (0 : ℝ≥0) 1,
      ContinuousWithinAt x (Set.Icc t 1) t)
    (hconv : ∀ h : C(Set.Icc (0 : ℝ≥0) 1, ℝ), ∃ a : ℝ,
      Tendsto (fun n ↦ ((LocallyFinitePartition.dyadic n).restrict 1).naiveLeftSum x
          (BoundedContinuousFunction.mkOfCompact h))
        atTop (𝓝 a)) :
    BoundedVariationOn x (Set.Icc 0 1) := by
  apply boundedVariationOn_of_tendsto_naiveLeftSum x hx
    (fun n ↦ (LocallyFinitePartition.dyadic n).restrict 1)
  · exact fun n ↦ (LocallyFinitePartition.dyadic n).strictMono_restrict 1
  · exact NNReal.tendsto_coe.mpr
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ 1))
  · intro h
    have heq : BoundedContinuousFunction.mkOfCompact h.toContinuousMap = h := by
      ext t
      rfl
    simpa only [heq] using hconv h.toContinuousMap

/-- Impossibility form of Protter I.56: an infinite-variation right-continuous
path admits a continuous integrand for which the dyadic naive left sums have no
finite real limit. -/
theorem exists_continuous_naiveLeftSum_not_tendsto_of_not_boundedVariation
    (x : ℝ≥0 → ℝ)
    (hx : ∀ t ∈ Set.Icc (0 : ℝ≥0) 1,
      ContinuousWithinAt x (Set.Icc t 1) t)
    (hvar : ¬ BoundedVariationOn x (Set.Icc 0 1)) :
    ∃ h : C(Set.Icc (0 : ℝ≥0) 1, ℝ), ¬ ∃ a : ℝ,
      Tendsto (fun n ↦ ((LocallyFinitePartition.dyadic n).restrict 1).naiveLeftSum x
          (BoundedContinuousFunction.mkOfCompact h))
        atTop (𝓝 a) := by
  classical
  by_contra h
  apply hvar
  apply protter_I_56_naiveIntegration_impossible x hx
  intro g
  by_contra hg
  exact h ⟨g, hg⟩

end StochLean

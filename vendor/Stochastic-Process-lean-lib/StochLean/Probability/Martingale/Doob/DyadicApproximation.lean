/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.DyadicSkeleton
public import StochLean.Probability.Process.Stopping.Approximation
public import StochLean.Probability.Process.Filtration.SubmartingaleReindex
public import StochLean.Probability.Process.Path.Cadlag
public import StochLean.Probability.Martingale.Doob.BoundedEnergy

/-! # The native discrete Doob decomposition on the existing dyadic grids

The increasing part is exactly Mathlib's `predictablePart` of the negative
sampled process. Its real-time extension uses the ceiling index: the value
on `(k / 2^n, (k+1) / 2^n]` is the next predictable coefficient. In particular,
adaptedness follows from predecessor measurability, not from measurability
at the possibly future ceiling time. No continuous-time compensator or
convergence as the mesh tends to zero is asserted here.
-/

@[expose] public section

open Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- These sampling times belong to the existing locally finite dyadic grid. -/
theorem dyadicDoob_grid_mem (n k : ℕ) :
    (k : ℝ≥0) / (2 ^ n : ℕ) ∈ (StochLean.LocallyFinitePartition.dyadic n).points := by
  change ∃ j : ℕ, (j : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n = _
  refine ⟨k, ?_⟩
  simp [div_eq_mul_inv]

/-- Monotone deterministic restriction of the original filtration. -/
noncomputable def dyadicDoobFiltration (F : Filtration ℝ≥0 mΩ) (n : ℕ) : Filtration ℕ mΩ :=
  F.reindex (fun k ↦ (k : ℝ≥0) / (2 ^ n : ℕ)) (by
    intro i j hij
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity))

@[simp] theorem dyadicDoobFiltration_apply (F : Filtration ℝ≥0 mΩ) (n k : ℕ) :
    dyadicDoobFiltration F n k = F ((k : ℝ≥0) / (2 ^ n : ℕ)) := rfl

/-- The actual predictable part of the negative dyadic restriction. -/
noncomputable def dyadicDoobIncreasing (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) (n : ℕ) : ℕ → Ω → ℝ :=
  predictablePart (-(fun k : ℕ ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ))))
    (dyadicDoobFiltration F n) P

/-- The ceiling, hence left-step, extension of the native predictable part. -/
noncomputable def dyadicDoobStep (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ dyadicDoobIncreasing X F P n (Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t))

variable (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)

theorem dyadicDoobIncreasing_eq_sum (n k : ℕ) :
    dyadicDoobIncreasing X F P n k =
      ∑ i ∈ Finset.range k,
        P[X ((i : ℝ≥0) / (2 ^ n : ℕ)) -
          X (((i + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ)) |
          F ((i : ℝ≥0) / (2 ^ n : ℕ))] := by
  simp only [dyadicDoobIncreasing, predictablePart, Pi.neg_apply, neg_sub_neg,
    dyadicDoobFiltration_apply]

@[simp] theorem dyadicDoobIncreasing_zero (n : ℕ) :
    dyadicDoobIncreasing X F P n 0 = 0 := predictablePart_zero

@[simp] theorem dyadicDoobStep_zero (n : ℕ) :
    dyadicDoobStep X F P n 0 = 0 := by simp [dyadicDoobStep]

theorem dyadicDoobIncreasing_add_one (n k : ℕ) :
    dyadicDoobIncreasing X F P n (k + 1) = dyadicDoobIncreasing X F P n k +
      P[X ((k : ℝ≥0) / (2 ^ n : ℕ)) -
        X (((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ)) |
        F ((k : ℝ≥0) / (2 ^ n : ℕ))] := by
  simpa only [dyadicDoobIncreasing, Pi.neg_apply, neg_sub_neg,
    dyadicDoobFiltration_apply] using
    predictablePart_add_one (f := -(fun k : ℕ ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ))))
      (ℱ := dyadicDoobFiltration F n) (μ := P) k

theorem dyadicDoobIncreasing_increment (n k : ℕ) :
    dyadicDoobIncreasing X F P n (k + 1) - dyadicDoobIncreasing X F P n k =
      P[X ((k : ℝ≥0) / (2 ^ n : ℕ)) -
        X (((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ)) |
        F ((k : ℝ≥0) / (2 ^ n : ℕ))] := by
  rw [dyadicDoobIncreasing_add_one, add_sub_cancel_left]

theorem dyadicDoobIncreasing_isStronglyPredictable (n : ℕ) :
    IsStronglyPredictable (dyadicDoobFiltration F n) (dyadicDoobIncreasing X F P n) :=
  isPredictable_predictablePart

theorem dyadicDoobIncreasing_stronglyMeasurable_add_one (n k : ℕ) :
    StronglyMeasurable[F ((k : ℝ≥0) / (2 ^ n : ℕ))]
      (dyadicDoobIncreasing X F P n (k + 1)) :=
  stronglyAdapted_predictablePart k

theorem dyadicDoobIncreasing_integrable (n k : ℕ) :
    Integrable (dyadicDoobIncreasing X F P n k) P := by
  rw [dyadicDoobIncreasing_eq_sum]
  fun_prop

/-- The index in the step extension is exactly the existing upper-grid index. -/
theorem dyadicDoobStep_grid_time (n : ℕ) (t : ℝ≥0) :
    (Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) : ℝ≥0) / (2 ^ n : ℕ) =
      dyadicRightGrid n t := (dyadicRightGrid_eq n t).symm

@[simp] theorem dyadicDoobStep_at_grid (n k : ℕ) :
    dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ n : ℕ)) =
      dyadicDoobIncreasing X F P n k := by
  have hp : ((2 ^ n : ℕ) : ℝ≥0) ≠ 0 := by positivity
  have hc : ((2 ^ n : ℕ) : ℝ≥0) * ((k : ℝ≥0) / (2 ^ n : ℕ)) = (k : ℝ≥0) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hp]
  simp only [dyadicDoobStep, hc, Nat.ceil_natCast]

/-- Each step includes its right endpoint and excludes its left endpoint. -/
theorem dyadicDoobStep_eq_on_Ioc (n k : ℕ) {t : ℝ≥0}
    (ht : (k : ℝ≥0) / (2 ^ n : ℕ) < t)
    (ht' : t ≤ ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ)) :
    dyadicDoobStep X F P n t = dyadicDoobIncreasing X F P n (k + 1) := by
  have hp : (0 : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) := by positivity
  have hc : Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) = k + 1 := by
    apply le_antisymm
    · apply Nat.ceil_le.mpr
      simpa [mul_comm] using (le_div_iff₀ hp).mp ht'
    · apply Nat.add_one_le_ceil_iff.mpr
      simpa [mul_comm] using (div_lt_iff₀ hp).mp ht
  simp only [dyadicDoobStep, hc]

/-- Predictability supplies the predecessor sigma-algebra, even when the
ceiling time is strictly later than the time at which the step is evaluated. -/
theorem dyadicDoobStep_stronglyAdapted (n : ℕ) :
    StronglyAdapted F (dyadicDoobStep X F P n) := by
  intro t
  cases hc : Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) with
  | zero => simp only [dyadicDoobStep, hc, dyadicDoobIncreasing_zero]
            exact stronglyMeasurable_zero
  | succ k =>
    have hp : (0 : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) := by positivity
    have hk : (k : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) * t :=
      Nat.lt_ceil.mp (by rw [hc]; exact Nat.lt_succ_self k)
    have hkt : (k : ℝ≥0) / (2 ^ n : ℕ) ≤ t := by
      apply (div_le_iff₀ hp).mpr
      simpa only [mul_comm] using hk.le
    simpa only [dyadicDoobStep, hc, Nat.succ_eq_add_one] using
      (dyadicDoobIncreasing_stronglyMeasurable_add_one X F P n k).mono (F.mono hkt)

theorem dyadicDoobStep_adapted (n : ℕ) : Adapted F (dyadicDoobStep X F P n) :=
  (dyadicDoobStep_stronglyAdapted X F P n).adapted

theorem dyadicDoobStep_integrable (n : ℕ) (t : ℝ≥0) :
    Integrable (dyadicDoobStep X F P n t) P :=
  dyadicDoobIncreasing_integrable X F P n _

/-- Left continuity is a pointwise consequence of the ceiling convention. -/
theorem dyadicDoobStep_isLeftContinuousPath (n : ℕ) (ω : Ω) :
    IsLeftContinuousPath (fun t ↦ dyadicDoobStep X F P n t ω) := by
  intro t
  by_cases ht : t = 0
  · subst t
    have hi : Set.Iic (0 : ℝ≥0) = {0} := Set.Iic_bot
    rw [hi]
    exact continuousWithinAt_singleton
  have hp : (0 : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) := by positivity
  have hcpos : 0 < Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) :=
    Nat.ceil_pos.mpr (mul_pos hp (pos_iff_ne_zero.mpr ht))
  obtain ⟨k, hc⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcpos)
  have hlo : (k : ℝ≥0) / (2 ^ n : ℕ) < t := by
    apply (div_lt_iff₀ hp).mpr
    have h := Nat.lt_ceil.mp (show k < Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) by
      rw [hc]; exact Nat.lt_succ_self k)
    simpa only [mul_comm] using h
  have hhi : t ≤ ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ) := by
    apply (le_div_iff₀ hp).mpr
    have h := Nat.le_ceil (((2 ^ n : ℕ) : ℝ≥0) * t)
    rw [hc] at h
    simpa only [Nat.succ_eq_add_one, mul_comm] using h
  apply continuousWithinAt_const.congr_of_eventuallyEq _ rfl
  filter_upwards [Ioc_mem_nhdsLE hlo] with u hu
  exact congrFun ((dyadicDoobStep_eq_on_Ioc X F P n k hu.1 (hu.2.trans hhi)).trans
    (dyadicDoobStep_eq_on_Ioc X F P n k hlo hhi).symm) ω

variable {X F P}

theorem Supermartingale.dyadic_restriction (hX : Supermartingale X F P) (n : ℕ) :
    Supermartingale (fun k : ℕ ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ)))
      (dyadicDoobFiltration F n) P :=
  hX.reindex _ _

theorem Supermartingale.dyadicDoobStep_monotone (hX : Supermartingale X F P) (n : ℕ) :
    HasMonotonePaths (dyadicDoobStep X F P n) P := by
  filter_upwards [(hX.dyadic_restriction n).neg.monotone_predictablePart] with ω hω
  intro s t hst
  apply hω
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hst (by positivity))

theorem Supermartingale.dyadicDoobStep_nonneg (hX : Supermartingale X F P) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ dyadicDoobStep X F P n t ω := by
  filter_upwards [hX.dyadicDoobStep_monotone n] with ω hω t
  have h := hω (bot_le : (0 : ℝ≥0) ≤ t)
  change dyadicDoobStep X F P n 0 ω ≤ dyadicDoobStep X F P n t ω at h
  simpa only [dyadicDoobStep_zero, Pi.zero_apply] using h

section FiniteMeasure

variable [IsFiniteMeasure P]

/-- The decomposition is native and discrete; the martingale part is not
asserted to remain a martingale after ceiling extension to all real times. -/
theorem Supermartingale.dyadic_doob_decomposition_data (hX : Supermartingale X F P)
    (n : ℕ) :
    let A := dyadicDoobIncreasing X F P n
    let M := -martingalePart (-(fun k : ℕ ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ))))
      (dyadicDoobFiltration F n) P
    Martingale M (dyadicDoobFiltration F n) P ∧
      IsStronglyPredictable (dyadicDoobFiltration F n) A ∧ A 0 = 0 ∧ M 0 = X 0 ∧
      M - A = (fun k : ℕ ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ))) ∧ HasMonotonePaths A P ∧
      (∀ᵐ ω ∂P, ∀ k, 0 ≤ A k ω) ∧ (∀ k, Integrable (A k) P) ∧
      ∀ k, (∫ ω, A k ω ∂P) =
        (∫ ω, X 0 ω ∂P) - ∫ ω, X ((k : ℝ≥0) / (2 ^ n : ℕ)) ω ∂P := by
  simpa only [dyadicDoobIncreasing, Nat.cast_zero, zero_div] using
    (hX.dyadic_restriction n).doob_decomposition_data

theorem Supermartingale.dyadicDoobIncreasing_memLp_two_of_bound
    (hX : Supermartingale X F P) {K : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (n k : ℕ) :
    MemLp (dyadicDoobIncreasing X F P n k) 2 P := by
  have hL (t : ℝ≥0) : MemLp (X t) 2 P := MemLp.of_bound
    (hX.integrable t).aestronglyMeasurable K (by simpa only [Real.norm_eq_abs] using hb t)
  rw [dyadicDoobIncreasing_eq_sum]
  apply memLp_finsetSum'
  intro i _
  exact ((hL _).sub (hL _)).condExp (by norm_num)

theorem Supermartingale.dyadicDoobStep_memLp_two_of_bound
    (hX : Supermartingale X F P) {K : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (n : ℕ) (t : ℝ≥0) :
    MemLp (dyadicDoobStep X F P n t) 2 P :=
  hX.dyadicDoobIncreasing_memLp_two_of_bound hb n _

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure P]

theorem Supermartingale.integral_sq_dyadicDoobIncreasing_le_of_bound
    (hX : Supermartingale X F P) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (n k : ℕ) :
    (∫ ω, dyadicDoobIncreasing X F P n k ω ^ 2 ∂P) ≤ 8 * K ^ 2 :=
  (hX.dyadic_restriction n).integral_sq_doob_increasing_le_of_bound hK
    (fun k ↦ hb ((k : ℝ≥0) / (2 ^ n : ℕ))) k

theorem Supermartingale.integral_sq_dyadicDoobStep_le_of_bound
    (hX : Supermartingale X F P) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (n : ℕ) (t : ℝ≥0) :
    (∫ ω, dyadicDoobStep X F P n t ω ^ 2 ∂P) ≤ 8 * K ^ 2 :=
  hX.integral_sq_dyadicDoobIncreasing_le_of_bound hK hb n _

/-- For each fixed mesh there is an actual terminal random variable in `L²`.
The limit here is along the discrete time index, not along mesh refinements. -/
theorem Supermartingale.exists_memLp_two_dyadicDoobIncreasing_terminal_of_bound
    (hX : Supermartingale X F P) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (n : ℕ) :
    let A := dyadicDoobIncreasing X F P n
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧ (∫ ω, Z ω ^ 2 ∂P) ≤ 8 * K ^ 2 ∧
      (∀ᵐ ω ∂P, (∀ k, A k ω ≤ Z ω) ∧ Tendsto (fun k ↦ A k ω) atTop (𝓝 (Z ω))) ∧
      UniformIntegrable A 1 P ∧ Tendsto (fun k ↦ eLpNorm (A k - Z) 1 P) atTop (𝓝 0) :=
  (hX.dyadic_restriction n).exists_memLp_two_doob_increasing_limit_of_bound hK
    (fun k ↦ hb ((k : ℝ≥0) / (2 ^ n : ℕ)))

end ProbabilityMeasure

end MeasureTheory

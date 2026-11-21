/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicApproximation

/-! # Predictability of actual coarse Doob steps on finer dyadic grids

The process is the existing ceiling extension `dyadicDoobStep`, sampled on
the existing dyadic grid. The predecessor of its next coarse coefficient
lies no later than the current fine-grid time. This arithmetic fact, rather
than adaptedness at the next fine time, gives discrete predictability.

Every fixed-grid sampling tends to the same actual coarse terminal variable.
No new dyadic grid or compensator selector is introduced.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

/-- A coarse grid point is the corresponding integer-multiple fine grid point. -/
theorem dyadicDoob_grid_time_eq_refined {n m : ℕ} (hnm : n ≤ m) (j : ℕ) :
    (j : ℝ≥0) / (2 ^ n : ℕ) =
      ((j * 2 ^ (m - n) : ℕ) : ℝ≥0) / (2 ^ m : ℕ) := by
  have hp : 2 ^ m = 2 ^ n * 2 ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_of_le hnm]
  simp only [hp, Nat.cast_mul]
  exact (mul_div_mul_right (j : ℝ≥0) ((2 ^ n : ℕ) : ℝ≥0) (by positivity)).symm

/-- The predecessor of the coarse coefficient revealed at the next fine
time is already available at the current fine time. -/
theorem dyadicDoob_coarse_predecessor_le {n m k j : ℕ} (hnm : n ≤ m)
    (hj : Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) *
      (((k + 1 : ℕ) : ℝ≥0) / (2 ^ m : ℕ))) = j + 1) :
    (j : ℝ≥0) / (2 ^ n : ℕ) ≤ (k : ℝ≥0) / (2 ^ m : ℕ) := by
  have hpn : (0 : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) := by positivity
  have hpm : (0 : ℝ≥0) < ((2 ^ m : ℕ) : ℝ≥0) := by positivity
  have hlt : (j : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) *
      (((k + 1 : ℕ) : ℝ≥0) / (2 ^ m : ℕ)) := by
    apply Nat.lt_ceil.mp
    rw [hj]
    exact Nat.lt_succ_self j
  have hgrid : (j : ℝ≥0) / (2 ^ n : ℕ) <
      ((k + 1 : ℕ) : ℝ≥0) / (2 ^ m : ℕ) := by
    apply (div_lt_iff₀ hpn).mpr
    simpa only [mul_comm] using hlt
  rw [dyadicDoob_grid_time_eq_refined hnm j] at hgrid
  have hnat : j * 2 ^ (m - n) < k + 1 := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hpm).mp hgrid
  rw [dyadicDoob_grid_time_eq_refined hnm j]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hnat)) hpm.le

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)

/-- Native discrete predictability of the actual coarse ceiling extension
when viewed on a finer grid. No supermartingale hypothesis is needed. -/
theorem dyadicDoobStep_isStronglyPredictable_on_fine_grid {n m : ℕ} (hnm : n ≤ m) :
    IsStronglyPredictable (dyadicDoobFiltration F m)
      (fun k : ℕ ↦ dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ m : ℕ))) := by
  apply IsStronglyPredictable.of_measurable_add_one
  · simp only [Nat.cast_zero, zero_div, dyadicDoobStep_zero]
    exact stronglyMeasurable_zero
  · intro k
    change StronglyMeasurable[F ((k : ℝ≥0) / (2 ^ m : ℕ))]
      (dyadicDoobStep X F P n (((k + 1 : ℕ) : ℝ≥0) / (2 ^ m : ℕ)))
    cases hc : Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) *
        (((k + 1 : ℕ) : ℝ≥0) / (2 ^ m : ℕ))) with
    | zero =>
      simp only [dyadicDoobStep, hc, dyadicDoobIncreasing_zero]
      exact stronglyMeasurable_zero
    | succ j =>
      have hj := dyadicDoob_coarse_predecessor_le hnm hc
      simpa only [dyadicDoobStep, hc, Nat.succ_eq_add_one] using
        (dyadicDoobIncreasing_stronglyMeasurable_add_one X F P n j).mono (F.mono hj)

@[simp] theorem dyadicDoobStep_fine_grid_zero (n m : ℕ) :
    dyadicDoobStep X F P n (((0 : ℕ) : ℝ≥0) / (2 ^ m : ℕ)) = 0 := by
  simp only [Nat.cast_zero, zero_div, dyadicDoobStep_zero]

/-- The ceiling index along any fixed fine grid tends to infinity. Nesting
is only needed for predictability, not for this terminal-limit assertion. -/
theorem dyadicDoob_ceil_index_tendsto (n m : ℕ) :
    Tendsto (fun k : ℕ ↦ Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) *
      ((k : ℝ≥0) / (2 ^ m : ℕ)))) atTop atTop := by
  have hm : Monotone (fun k : ℕ ↦ Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) *
      ((k : ℝ≥0) / (2 ^ m : ℕ)))) := by
    intro i j hij
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)) (by positivity)
  apply hm.tendsto_atTop_atTop
  intro b
  refine ⟨b * 2 ^ m, ?_⟩
  have hpm : ((2 ^ m : ℕ) : ℝ≥0) ≠ 0 := by positivity
  have he : Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) *
      (((b * 2 ^ m : ℕ) : ℝ≥0) / (2 ^ m : ℕ))) = 2 ^ n * b := by
    rw [Nat.cast_mul, mul_div_cancel_right₀ _ hpm, ← Nat.cast_mul, Nat.ceil_natCast]
  rw [he]
  have hp : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by decide))
  simpa only [one_mul] using Nat.mul_le_mul_right b hp

/-- A supplied actual coarse terminal limit remains the terminal limit of
the same coarse step process sampled on any fixed dyadic grid. -/
theorem dyadicDoobStep_tendsto_on_fine_grid (n m : ℕ) {Z : Ω → ℝ}
    (hl : ∀ᵐ ω ∂P, Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω)
      atTop (𝓝 (Z ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ ↦
      dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ m : ℕ)) ω) atTop (𝓝 (Z ω)) :=
  hl.mono fun _ hω ↦ hω.comp (dyadicDoob_ceil_index_tendsto n m)

variable {X F P}

theorem Supermartingale.dyadicDoobStep_monotone_on_fine_grid
    (hX : Supermartingale X F P) (n m : ℕ) :
    HasMonotonePaths
      (fun k : ℕ ↦ dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ m : ℕ))) P := by
  filter_upwards [hX.dyadicDoobStep_monotone n] with ω hω
  intro i j hij
  exact hω (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity))

/-- The existing bounded-supermartingale terminal construction supplies one
and the same terminal variable for the coarse process and its fine sampling. -/
theorem Supermartingale.exists_memLp_two_dyadicDoob_terminal_on_fine_grid
    [IsProbabilityMeasure P] (hX : Supermartingale X F P) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (n m : ℕ) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧ (∫ ω, Z ω ^ 2 ∂P) ≤ 8 * K ^ 2 ∧
      (∀ᵐ ω ∂P, (∀ k, dyadicDoobIncreasing X F P n k ω ≤ Z ω) ∧
        Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (Z ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k : ℕ ↦
        dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ m : ℕ)) ω) atTop (𝓝 (Z ω))) := by
  obtain ⟨Z, hZ, he, hl, _, _⟩ :=
    hX.exists_memLp_two_dyadicDoobIncreasing_terminal_of_bound hK hb n
  exact ⟨Z, hZ, he, hl,
    dyadicDoobStep_tendsto_on_fine_grid X F P n m (hl.mono fun _ hω ↦ hω.2)⟩

end MeasureTheory

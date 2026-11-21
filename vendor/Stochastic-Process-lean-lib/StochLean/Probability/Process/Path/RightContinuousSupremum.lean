/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Supremum
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Right-continuous running suprema and real-valued probability bounds

These interfaces use the existing `denseRunningSupremum`, not a second running-supremum
construction. Right continuity recovers strict exceedance at every point of `[0,T]`, including
both endpoints. A finite upper bound is established before converting the extended supremum to
real values. Strict positive-threshold probabilities then give the native `TendstoInMeasure`
conclusion, using a smaller threshold to handle its non-strict norm events.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Right continuity detects every strict exceedance on the clipped countable dense grid.
No maximum-attainment assumption is needed, including at `T = 0`. -/
theorem exists_denseTimeUpTo_exceedance_of_rightContinuous {f : ℝ≥0 → ℝ}
    (hf : IsRightContinuousPath f) {T t : ℝ≥0} (ht : t ≤ T) {a : ℝ}
    (ha : a < f t) : ∃ n : ℕ, a < f (denseTimeUpTo T n) := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt ha) (le_of_denseTimeUpTo_le_of_rightContinuous hf ht hn)

/-- Strict nonnegative-level exceedance by the existing countable supremum is equivalent to
an actual exceedance somewhere on the entire closed time interval for a right-continuous path. -/
theorem lt_denseRunningSupremum_iff_exists_of_rightContinuous
    {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) :
    ENNReal.ofReal a < denseRunningSupremum X T ω ↔
      ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω := by
  constructor
  · simp only [denseRunningSupremum, lt_iSup_iff]
    rintro ⟨n, hn⟩
    exact ⟨denseTimeUpTo T n, min_le_left _ _,
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mp hn⟩
  · rintro ⟨t, ht, hat⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr hat).trans_le
      (ofReal_le_denseRunningSupremum_of_rightContinuous ht hX)

/-- The existing countable supremum equals the full extended supremum on the closed interval.
This equality does not assert that the supremum is attained. -/
theorem denseRunningSupremum_eq_iSup_of_rightContinuous {X : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {ω : Ω} (hX : IsRightContinuousPath (X · ω)) :
    denseRunningSupremum X T ω = ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal (X t ω) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact le_iSup_of_le (denseTimeUpTo T n)
      (le_iSup_of_le (min_le_left _ _) le_rfl)
  · exact iSup_le fun t ↦ iSup_le fun ht ↦
      ofReal_le_denseRunningSupremum_of_rightContinuous ht hX

/-- Pointwise order on the relevant time interval is preserved by the countable supremum. -/
theorem denseRunningSupremum_mono {X Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hXY : ∀ t, t ≤ T → X t ω ≤ Y t ω) :
    denseRunningSupremum X T ω ≤ denseRunningSupremum Y T ω := by
  exact iSup_mono fun n ↦ ENNReal.ofReal_le_ofReal
    (hXY (denseTimeUpTo T n) (min_le_left _ _))

/-- A real upper bound controls the positive-part running supremum. -/
theorem denseRunningSupremum_le_of_le {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω} {K : ℝ}
    (hK : ∀ t, t ≤ T → X t ω ≤ K) :
    denseRunningSupremum X T ω ≤ ENNReal.ofReal K := by
  exact iSup_le fun n ↦ ENNReal.ofReal_le_ofReal
    (hK (denseTimeUpTo T n) (min_le_left _ _))

/-- In particular, a process bounded above by one has extended running supremum at most one. -/
theorem denseRunningSupremum_le_one {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hX : ∀ t, t ≤ T → X t ω ≤ 1) : denseRunningSupremum X T ω ≤ 1 := by
  simpa only [ENNReal.ofReal_one] using denseRunningSupremum_le_of_le hX

/-- Finiteness follows from an actual upper bound before applying `ENNReal.toReal`. -/
theorem denseRunningSupremum_ne_top_of_le {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω} {K : ℝ}
    (hK : ∀ t, t ≤ T → X t ω ≤ K) : denseRunningSupremum X T ω ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (denseRunningSupremum_le_of_le hK)

/-- A nonnegative upper bound also bounds the genuine real value of the finite supremum. -/
theorem denseRunningSupremum_toReal_le {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω} {K : ℝ}
    (hK : 0 ≤ K) (hX : ∀ t, t ≤ T → X t ω ≤ K) :
    (denseRunningSupremum X T ω).toReal ≤ K := by
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (denseRunningSupremum_le_of_le hX)
  simpa only [ENNReal.toReal_ofReal hK] using hle

/-- Every value of a right-continuous path lies below its finite real running supremum.
The path itself need not be nonnegative. -/
theorem le_toReal_denseRunningSupremum_of_rightContinuous
    {X : ℝ≥0 → Ω → ℝ} {T t : ℝ≥0} {ω : Ω} (ht : t ≤ T)
    (hX : IsRightContinuousPath (X · ω)) (hfin : denseRunningSupremum X T ω ≠ ∞) :
    X t ω ≤ (denseRunningSupremum X T ω).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    (ofReal_le_denseRunningSupremum_of_rightContinuous ht hX)

/-- For finite running suprema, the strict real exceedance event has the same whole-interval
interpretation. The explicit non-top hypothesis prevents the `toReal` infinity fallback. -/
theorem lt_toReal_denseRunningSupremum_iff_exists_of_rightContinuous
    {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {a : ℝ} {ω : Ω} (ha : 0 ≤ a)
    (hX : IsRightContinuousPath (X · ω)) (hfin : denseRunningSupremum X T ω ≠ ∞) :
    a < (denseRunningSupremum X T ω).toReal ↔ ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω := by
  rw [← ENNReal.ofReal_lt_iff_lt_toReal ha hfin]
  exact lt_denseRunningSupremum_iff_exists_of_rightContinuous ha hX

/-- Coordinate measurability gives measurability of the real-valued countable supremum. -/
theorem measurable_toReal_denseRunningSupremum {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T : ℝ≥0) :
    Measurable (fun ω ↦ (denseRunningSupremum X T ω).toReal) :=
  (measurable_denseRunningSupremum hX T).ennreal_toReal

/-- Coordinatewise almost-sure upper bounds yield a common almost-sure bound for the countable
supremum, without taking an uncountable intersection of exceptional sets. -/
theorem ae_denseRunningSupremum_le_of_ae_le {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {K : ℝ} (hX : ∀ t, t ≤ T → ∀ᵐ ω ∂P, X t ω ≤ K) :
    ∀ᵐ ω ∂P, denseRunningSupremum X T ω ≤ ENNReal.ofReal K := by
  have hgrid : ∀ᵐ ω ∂P, ∀ n : ℕ, X (denseTimeUpTo T n) ω ≤ K := by
    rw [ae_all_iff]
    exact fun n ↦ hX (denseTimeUpTo T n) (min_le_left _ _)
  filter_upwards [hgrid] with ω hω
  exact iSup_le fun n ↦ ENNReal.ofReal_le_ofReal (hω n)

/-- Strict positive-threshold probabilities of finite running suprema imply convergence in
measure of their actual real values. The measure must be finite: otherwise `P.real` could hide
infinite mass. Right continuity is only needed to identify these with whole-time exceedances. -/
theorem tendstoInMeasure_toReal_denseRunningSupremum_of_measureReal_lt
    {ι : Type*} {P : Measure Ω} [IsFiniteMeasure P] {l : Filter ι}
    {X : ι → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hfin : ∀ i ω, denseRunningSupremum (X i) T ω ≠ ∞)
    (hprob : ∀ a : ℝ, 0 < a →
      Tendsto (fun i ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (X i) T ω})
        l (𝓝 0)) :
    TendstoInMeasure P (fun i ω ↦ (denseRunningSupremum (X i) T ω).toReal) l
      (fun _ ↦ (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hprob (ε / 2) (half_pos hε)) (fun _ ↦ measureReal_nonneg)
  intro i
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  have hnorm : ε ≤ (denseRunningSupremum (X i) T ω).toReal := by
    simpa only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hω
  exact (ENNReal.ofReal_lt_iff_lt_toReal (half_pos hε).le (hfin i ω)).mpr
    ((half_lt_self hε).trans_le hnorm)

/-- Almost-sure finiteness for each process is enough for the strict-threshold conversion.
The exceptional event may depend on the index; no common uncountable intersection or pointwise
bound on exceptional paths is required. -/
theorem tendstoInMeasure_toReal_denseRunningSupremum_of_ae_ne_top
    {ι : Type*} {P : Measure Ω} [IsFiniteMeasure P] {l : Filter ι}
    {X : ι → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hfin : ∀ i, ∀ᵐ ω ∂P, denseRunningSupremum (X i) T ω ≠ ∞)
    (hprob : ∀ a : ℝ, 0 < a →
      Tendsto (fun i ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (X i) T ω})
        l (𝓝 0)) :
    TendstoInMeasure P (fun i ω ↦ (denseRunningSupremum (X i) T ω).toReal) l
      (fun _ ↦ (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hprob (ε / 2) (half_pos hε)) (fun _ ↦ measureReal_nonneg)
  intro i
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hfin i] with ω hfinω
  intro hω
  change ε ≤ ‖(denseRunningSupremum (X i) T ω).toReal - 0‖ at hω
  have hnorm : ε ≤ (denseRunningSupremum (X i) T ω).toReal := by
    simpa only [sub_zero, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hω
  exact (ENNReal.ofReal_lt_iff_lt_toReal (half_pos hε).le hfinω).mpr
    ((half_lt_self hε).trans_le hnorm)

/-- The bounded-probability specialization used for uniform conditional jump probabilities.
An upper bound by one supplies the non-top proof; no arbitrary real fallback is used. -/
theorem tendstoInMeasure_toReal_denseRunningSupremum_of_le_one
    {ι : Type*} {P : Measure Ω} [IsFiniteMeasure P] {l : Filter ι}
    {X : ι → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hX : ∀ i t ω, t ≤ T → X i t ω ≤ 1)
    (hprob : ∀ a : ℝ, 0 < a →
      Tendsto (fun i ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (X i) T ω})
        l (𝓝 0)) :
    TendstoInMeasure P (fun i ω ↦ (denseRunningSupremum (X i) T ω).toReal) l
      (fun _ ↦ (0 : ℝ)) :=
  tendstoInMeasure_toReal_denseRunningSupremum_of_measureReal_lt
    (fun i ω ↦ denseRunningSupremum_ne_top_of_le (fun t ht ↦ hX i t ω ht)) hprob

end ProbabilityTheory

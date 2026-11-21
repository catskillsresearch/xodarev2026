/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Countable running suprema and pathwise bridges

Generic process-level objects, also used by Brownian path functionals and UCP.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A fixed countable dense grid, retracted to the deterministic interval `[0,T]`.  Retraction by
`min T` retains density in that interval and includes the terminal endpoint whenever a dense-grid
point lies above it. -/
noncomputable def denseTimeUpTo (T : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  min T (TopologicalSpace.denseSeq ℝ≥0 n)

/-- The positive-part running supremum along the canonical dense grid. -/
noncomputable def denseRunningSupremum (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (X (denseTimeUpTo T n) ω)

theorem measurable_denseRunningSupremum {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T : ℝ≥0) :
    Measurable (denseRunningSupremum X T) := by
  apply Measurable.iSup
  intro n
  exact ENNReal.measurable_ofReal.comp (hX (denseTimeUpTo T n))

/-- A strict exceedance of a continuous path before `T` is seen by the canonical dense grid. -/
theorem exists_denseTimeUpTo_exceedance {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {T t : ℝ≥0} (ht : t ≤ T) {a : ℝ} (ha : a < f t) :
    ∃ n : ℕ, a < f (denseTimeUpTo T n) := by
  let U : Set ℝ≥0 := f ⁻¹' Set.Ioi a
  have hUopen : IsOpen U := isOpen_Ioi.preimage hf
  have htU : t ∈ U := ha
  let r : ℝ≥0 → ℝ≥0 := fun s => min T s
  have hr : Continuous r := continuous_const.min continuous_id
  have hrt : r t = t := min_eq_right ht
  have hpre : r ⁻¹' U ∈ 𝓝 t := by
    exact hr.continuousAt (hUopen.mem_nhds (show r t ∈ U by simpa only [hrt] using htU))
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq ℝ≥0).mem_nhds hpre
  exact ⟨n, by simpa only [Set.mem_preimage, U, Set.mem_Ioi, r, denseTimeUpTo] using hn⟩

/-- For a continuous path, strict positive-level exceedance on the whole compact time interval is
equivalent to exceedance on the canonical countable dense grid. -/
theorem lt_denseRunningSupremum_iff_exists_of_continuous {X : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) {ω : Ω} (hcont : Continuous (X · ω)) :
    ENNReal.ofReal a < denseRunningSupremum X T ω ↔
      ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω := by
  constructor
  · simp only [denseRunningSupremum, lt_iSup_iff]
    rintro ⟨n, hn⟩
    exact ⟨denseTimeUpTo T n, min_le_left _ _,
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mp hn⟩
  · rintro ⟨t, ht, hXt⟩
    obtain ⟨n, hn⟩ := exists_denseTimeUpTo_exceedance hcont ht hXt
    rw [denseRunningSupremum, lt_iSup_iff]
    exact ⟨n, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr hn⟩

theorem measurableSet_denseRunningSupremum_gt {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T : ℝ≥0) (a : ℝ) :
    MeasurableSet {ω | ENNReal.ofReal a < denseRunningSupremum X T ω} :=
  measurableSet_lt measurable_const (measurable_denseRunningSupremum hX T)

/-- Rational times in the compact interval `[0,T]`. -/
abbrev RationalTimeUpTo (T : ℝ≥0) :=
  {q : ℚ // 0 ≤ q ∧ (q : ℝ) ≤ T}

/-- A bounded nonnegative rational time as an `NNReal`. -/
def RationalTimeUpTo.toNNReal {T : ℝ≥0} (q : RationalTimeUpTo T) : ℝ≥0 :=
  ⟨(q : ℝ), by exact_mod_cast q.property.1⟩

/-- The positive-part running supremum over rational times up to `T`.  `ENNReal` is used so that
the countable supremum is total; for a continuous real path on a compact interval it is finite. -/
noncomputable def rationalRunningSupremum (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ q : RationalTimeUpTo T, ENNReal.ofReal (X q.toNNReal ω)

/-- The rational running supremum is measurable as a countable supremum of coordinate maps. -/
theorem measurable_rationalRunningSupremum {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T : ℝ≥0) :
    Measurable (rationalRunningSupremum X T) := by
  apply Measurable.iSup
  intro q
  exact ENNReal.measurable_ofReal.comp (hX q.toNNReal)

/-- Strict exceedance of a positive level by the rational running supremum is exactly a
countable-coordinate event. -/
theorem lt_rationalRunningSupremum_iff {X : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ENNReal.ofReal a < rationalRunningSupremum X T ω ↔
      ∃ q : RationalTimeUpTo T, a < X q.toNNReal ω := by
  simp only [rationalRunningSupremum, lt_iSup_iff]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mp hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr hq⟩

/-- The strict rational-exceedance event is measurable. -/
theorem measurableSet_rationalRunningSupremum_gt {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T : ℝ≥0) (a : ℝ) :
    MeasurableSet {ω | ENNReal.ofReal a < rationalRunningSupremum X T ω} :=
  measurableSet_lt measurable_const (measurable_rationalRunningSupremum hX T)

/-- Right continuity suffices to recover bounds from the clipped dense grid,
including at the terminal endpoint. -/
theorem le_of_denseTimeUpTo_le_of_rightContinuous {E : Type*}
    [TopologicalSpace E] [Preorder E] [OrderClosedTopology E]
    {f : ℝ≥0 → E} (hf : IsRightContinuousPath f) {T t : ℝ≥0} (ht : t ≤ T)
    {a : E} (hbound : ∀ n, f (denseTimeUpTo T n) ≤ a) : f t ≤ a := by
  have hdense : Dense (Set.range (TopologicalSpace.denseSeq ℝ≥0)) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hdense.exists_seq_strictAnti_tendsto t
  have hv : Tendsto (fun n ↦ min T (u n)) atTop (𝓝 t) := by
    simpa only [min_eq_right ht] using
      ((show Tendsto (fun _ : ℕ ↦ T) atTop (𝓝 T) from tendsto_const_nhds).min hlim)
  have hwithin : Tendsto (fun n ↦ min T (u n)) atTop (nhdsWithin t (Set.Ici t)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hv, Eventually.of_forall fun n ↦ le_min ht (hu n).1.le⟩
  apply le_of_tendsto' ((hf t).tendsto.comp hwithin)
  intro n
  obtain ⟨k, hk⟩ := (hu n).2
  simpa only [denseTimeUpTo, hk, Function.comp_apply] using hbound k

/-- The countable running supremum dominates every point on a right-continuous path. -/
theorem ofReal_le_denseRunningSupremum_of_rightContinuous {X : ℝ≥0 → Ω → ℝ}
    {T t : ℝ≥0} (ht : t ≤ T) {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) :
    ENNReal.ofReal (X t ω) ≤ denseRunningSupremum X T ω := by
  apply le_of_denseTimeUpTo_le_of_rightContinuous
    (f := fun t ↦ ENNReal.ofReal (X t ω))
    (fun t ↦ ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hX t)) ht
  intro n
  exact le_iSup (fun n ↦ ENNReal.ofReal (X (denseTimeUpTo T n) ω)) n

end ProbabilityTheory

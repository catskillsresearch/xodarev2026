/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesEndpointSums

/-! # Finite steps depending on both cell endpoint values

Repeated endpoints are allowed. At positive times the unique nonempty cell
determines both values; the initial value is retained separately.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0} {E : Type*}

noncomputable def endpointPairStep (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) (t : ℝ≥0) : ℝ :=
  if t = 0 then Φ (x 0) (x 0) else
    ∑ i : Fin π.size, (Ioc (π.left i) (π.right i)).indicator
      (fun _ ↦ Φ (x (π.left i)) (x (π.right i))) t

@[simp] theorem endpointPairStep_zero (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) : π.endpointPairStep Φ x 0 = Φ (x 0) (x 0) := by
  simp only [endpointPairStep, ↓reduceIte]

theorem endpointPairStep_eq_of_mem_cell (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) :
    π.endpointPairStep Φ x t = Φ (x (π.left i)) (x (π.right i)) := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [endpointPairStep, if_neg ht, Finset.sum_eq_single i]
  · exact indicator_of_mem (s := Ioc (π.left i) (π.right i)) (a := t) hi _
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji (π.cell_unique hj hi)
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem endpointPairStep_eq_left_right (π : TimePartition T) (Φ : ℝ → ℝ → ℝ)
    (x : ℝ≥0 → ℝ) {t : ℝ≥0} (ht : t ∈ Ioc 0 T) :
    π.endpointPairStep Φ x t = Φ (π.leftStep x t) (π.taggedStep π.right x t) := by
  obtain ⟨i, hi⟩ := π.exists_cell ht
  rw [π.endpointPairStep_eq_of_mem_cell Φ x hi,
    π.leftStep_eq_of_mem_cell x hi, π.taggedStep_eq_of_mem_cell π.right x hi]

theorem measurable_endpointPairStep (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) : Measurable (π.endpointPairStep Φ x) := by
  classical
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc)

theorem norm_endpointPairStep_le (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) {C : ℝ}
    (hC : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, ‖Φ (x a) (x b)‖ ≤ C)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) : ‖π.endpointPairStep Φ x t‖ ≤ C := by
  by_cases ht0 : t = 0
  · subst t
    rw [endpointPairStep_zero]
    exact hC 0 ht 0 ht
  · obtain ⟨i, hi⟩ := π.exists_cell ⟨pos_iff_ne_zero.mpr ht0, ht.2⟩
    rw [π.endpointPairStep_eq_of_mem_cell Φ x hi]
    exact hC _ ⟨bot_le, π.point_le_horizon _⟩ _ ⟨bot_le, π.point_le_horizon _⟩

theorem tendsto_endpointPairStep_of_cadlag [MetricSpace E] {π : ℕ → TimePartition T}
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    {x : ℝ≥0 → E} (hx : IsCadlagPath x) {t : ℝ≥0} (ht : t ∈ Ioc 0 T)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).endpointPairStep Φ x t) atTop
      (𝓝 (Φ (Function.leftLim x t) (x t))) := by
  choose i hi using fun n ↦ (π n).exists_cell ht
  have hl : Tendsto (fun n ↦ (π n).left (i n)) atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).1⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (π n).dist_left_of_mem_cell_le_mesh (hi n)
  have hr : Tendsto (fun n ↦ (π n).right (i n)) atTop (𝓝[≥] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).2⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (π n).dist_tag_of_mem_cell_le_mesh (π n).right
      (fun j ↦ ⟨(π n).left_le_right j, le_rfl⟩) (hi n)
  have hxl := (tendsto_leftLim_of_tendsto (hx.2 t (ne_of_gt ht.1))).comp hl
  have hxr := (hx.1 t).tendsto.comp hr
  simpa only [fun n ↦ (π n).endpointPairStep_eq_of_mem_cell Φ x (hi n),
    Function.comp_def] using
    (hΦ.tendsto (Function.leftLim x t, x t)).comp (hxl.prodMk_nhds hxr)

end TimePartition

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem integrableOn_variationStieltjes_endpointPairStep {E : Type*} (π : TimePartition T)
    (Φ : E → E → ℝ) (f : ℝ≥0 → E) (t : ℝ≥0) :
    IntegrableOn (π.endpointPairStep Φ f) (Ioc 0 t)
      (totalVariationStieltjes x hx hr).measure :=
  integrableOn_variationStieltjes_finite_step π.left π.right
    (fun i ↦ Φ (f (π.left i)) (f (π.right i))) (Φ (f 0) (f 0)) t

theorem pathStieltjesIncrementIntegral_endpointPairStep_terminal {E : Type*} (π : TimePartition T)
    (Φ : E → E → ℝ) (f : ℝ≥0 → E) :
    pathStieltjesIncrementIntegral x hx hr (π.endpointPairStep Φ f) 0 T =
      ∑ i : Fin π.size, Φ (f (π.left i)) (f (π.right i)) * π.increment x i := by
  have h := pathStieltjesIntegral_finite_step (x := x) (hx := hx) (hr := hr)
    π.left π.right (fun i ↦ Φ (f (π.left i)) (f (π.right i))) π.left_le_right
      (Φ (f 0) (f 0)) T
  change pathStieltjesIntegral x hx hr (π.endpointPairStep Φ f) T = _ at h
  rw [pathStieltjesIntegral, TimePartition.endpointPairStep_zero] at h
  apply add_left_cancel (a := Φ (f 0) (f 0) * x 0)
  convert h using 1
  simp only [TimePartition.increment, TimePartition.left, TimePartition.right,
    min_eq_left (π.point_le_horizon _)]

end StochLean

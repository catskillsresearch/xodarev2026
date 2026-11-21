/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Topology.Algebra.InfiniteSum.LifetimeReindex
public import StochLean.Analysis.PathVariation.StieltjesCountableSupport
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Actual jump series along disjoint lifetime graphs

Finite partial sums are bounded by the original path's variation, not by an
assumed dominating series. Only positive-time jumps in `(0,T]` are included.
The real global-variation bound explicitly requires finite global variation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped NNReal ENNReal Topology

namespace StochLean

private theorem stieltjesJumpPart_le_increment (f : StieltjesFunction ℝ≥0)
    (T : ℝ≥0) : stieltjesJumpPart f T ≤ f T - f 0 := by
  have hn : 0 ≤ stieltjesContinuousPart f T := by
    rw [← stieltjesContinuousPart_zero f]
    exact (stieltjesContinuousPart f).mono bot_le
  linarith [stieltjesContinuousPart_add_jumpPart f T]

/-- The absolute jump mass on `(0,T]` is bounded by compact variation. -/
theorem tsum_abs_jumps_le_eVariationOn_Icc {y : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn y univ)
    (hr : ∀ t, ContinuousWithinAt y (Ici t) t) (T : ℝ≥0) :
    (∑' t : Ioc 0 T, |y t - leftLim y t|) ≤ (eVariationOn y (Icc 0 T)).toReal := by
  let p := positiveVariationStieltjes y hv hr
  let n := negativeVariationStieltjes y hv hr
  have hp := summable_stieltjes_jumps p T
  have hn := summable_stieltjes_jumps n T
  calc
    _ ≤ ∑' t : Ioc 0 T,
        ((p t - leftLim p t) + (n t - leftLim n t)) := by
      apply (summable_abs_jumps_of_locallyBoundedVariation hv hr T).tsum_le_tsum _ (hp.add hn)
      intro t
      rw [← variationStieltjes_jump_sub hv hr t.property.1]
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (p.mono.leftLim_le le_rfl)),
        abs_of_nonneg (sub_nonneg.mpr (n.mono.leftLim_le le_rfl))] using
          norm_sub_le (p t - leftLim p t) (n t - leftLim n t)
    _ = stieltjesJumpPart p T + stieltjesJumpPart n T := by
      rw [hp.tsum_add hn, ← stieltjesJumpPart_eq_tsum, ← stieltjesJumpPart_eq_tsum]
    _ ≤ (p T - p 0) + (n T - n 0) :=
      add_le_add (stieltjesJumpPart_le_increment p T) (stieltjesJumpPart_le_increment n T)
    _ = _ := by
      change (pathPositiveVariation y T - pathPositiveVariation y 0) +
        (pathNegativeVariation y T - pathNegativeVariation y 0) = _
      rw [pathPositiveVariation_zero, pathNegativeVariation_zero, sub_zero, sub_zero,
        pathPositiveVariation_add_negative, pathTotalVariation_eq]

/-- A genuinely bounded weight controls the actual absolute jump series. -/
theorem tsum_abs_weighted_jumps_le_mul_eVariationOn_Icc {y f : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn y univ)
    (hr : ∀ t, ContinuousWithinAt y (Ici t) t) (T : ℝ≥0)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ C) :
    (∑' t : Ioc 0 T, |f t * (y t - leftLim y t)|) ≤
      C * (eVariationOn y (Icc 0 T)).toReal := by
  have hs := summable_abs_jumps_of_locallyBoundedVariation hv hr T
  calc
    _ ≤ ∑' t : Ioc 0 T, C * |y t - leftLim y t| := by
      apply (summable_abs_weighted_jumps_of_locallyBoundedVariation hv hr T hb).tsum_le_tsum
        _ (hs.mul_left C)
      intro t
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb t t.property) (abs_nonneg _)
    _ = C * ∑' t : Ioc 0 T, |y t - leftLim y t| := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_abs_jumps_le_eVariationOn_Icc hv hr T) hC

/-- A cover of the integrator's positive jumps reindexes the weighted
series. Zero products need not be separately covered. -/
theorem tsum_weighted_jumps_eq_tsum_of_disjoint_finite_lifetimes
    {ι : Type*} {y f : ℝ≥0 → ℝ} {g : ι → ℝ} {τ : ι → WithTop ℝ≥0}
    (T : ℝ≥0)
    (hdisj : ∀ i j (t : ℝ≥0),
      τ i = (t : WithTop ℝ≥0) → τ j = (t : WithTop ℝ≥0) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : ℝ≥0), τ i = (t : WithTop ℝ≥0) →
      g i = (Ioc 0 T).indicator (fun u ↦ f u * (y u - leftLim y u)) t)
    (hcover : ∀ t : ℝ≥0, 0 < t → y t - leftLim y t ≠ 0 →
      ∃ i, τ i = (t : WithTop ℝ≥0)) :
    (∑' t : Ioc 0 T, f t * (y t - leftLim y t)) = ∑' i, g i := by
  classical
  rw [tsum_subtype (Ioc 0 T) (fun t ↦ f t * (y t - leftLim y t))]
  apply tsum_eq_tsum_of_disjoint_finite_lifetimes hdisj htop hcoe
  intro t ht
  have htmem : t ∈ Ioc 0 T := by
    by_contra hm
    exact ht (indicator_of_notMem hm _)
  have hj : y t - leftLim y t ≠ 0 := by
    intro hz
    apply ht
    rw [indicator_of_mem htmem, hz, mul_zero]
  exact hcover t htmem.1 hj

/-- Every finite lifetime-indexed partial sum is dominated by finite
global variation. No coverage hypothesis is needed for this bound. -/
theorem sum_abs_weighted_jumps_le_of_disjoint_finite_lifetimes
    {ι : Type*} {y f : ℝ≥0 → ℝ} {g : ι → ℝ} {τ : ι → WithTop ℝ≥0}
    (hv : LocallyBoundedVariationOn y univ)
    (hr : ∀ t, ContinuousWithinAt y (Ici t) t)
    (hfin : eVariationOn y univ ≠ ∞) (T : ℝ≥0)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ C)
    (hdisj : ∀ i j (t : ℝ≥0),
      τ i = (t : WithTop ℝ≥0) → τ j = (t : WithTop ℝ≥0) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : ℝ≥0), τ i = (t : WithTop ℝ≥0) →
      g i = (Ioc 0 T).indicator (fun u ↦ f u * (y u - leftLim y u)) t)
    (s : Finset ι) : (∑ i ∈ s, |g i|) ≤ C * (eVariationOn y univ).toReal := by
  classical
  have hs := summable_abs_weighted_jumps_of_locallyBoundedVariation hv hr T hb
  have he (t : ℝ≥0) :
      |(Ioc 0 T).indicator (fun u ↦ f u * (y u - leftLim y u)) t| =
      (Ioc 0 T).indicator (fun u ↦ |f u * (y u - leftLim y u)|) t := by
    by_cases ht : t ∈ Ioc 0 T <;> simp only [indicator_apply, ht, if_true, if_false, abs_zero]
  have hs' : Summable (fun t ↦
      |(Ioc 0 T).indicator (fun u ↦ f u * (y u - leftLim y u)) t|) := by
    simp_rw [he]
    exact summable_subtype_iff_indicator.mp hs
  have hle := sum_abs_le_tsum_abs_of_disjoint_finite_lifetimes hdisj htop hcoe hs' s
  simp_rw [he] at hle
  rw [← tsum_subtype] at hle
  exact (hle.trans (tsum_abs_weighted_jumps_le_mul_eVariationOn_Icc hv hr T hC hb)).trans
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hfin (eVariationOn.mono y (subset_univ _))) hC)

/-- A bounded cadlag first path gives the explicit `2 C` envelope for
arbitrary finite partial sums of the actual mixed jump series. -/
theorem abs_sum_mixed_jumps_le_of_disjoint_finite_lifetimes
    {ι : Type*} {x y : ℝ≥0 → ℝ} {g : ι → ℝ} {τ : ι → WithTop ℝ≥0}
    (hx : IsCadlagPath x) (hv : LocallyBoundedVariationOn y univ)
    (hr : ∀ t, ContinuousWithinAt y (Ici t) t)
    (hfin : eVariationOn y univ ≠ ∞) (T : ℝ≥0)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖x t‖ ≤ C)
    (hdisj : ∀ i j (t : ℝ≥0),
      τ i = (t : WithTop ℝ≥0) → τ j = (t : WithTop ℝ≥0) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : ℝ≥0), τ i = (t : WithTop ℝ≥0) → g i =
      (Ioc 0 T).indicator (fun u ↦ (x u - leftLim x u) * (y u - leftLim y u)) t)
    (s : Finset ι) : |∑ i ∈ s, g i| ≤ 2 * C * (eVariationOn y univ).toReal := by
  have hxb (t : ℝ≥0) (ht : t ∈ Ioc 0 T) : ‖x t - leftLim x t‖ ≤ 2 * C := by
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht.1⟩
    have hl : ‖leftLim x t‖ ≤ C :=
      le_of_tendsto (tendsto_leftLim_of_tendsto (hx.2 t ht.1.ne')).norm
        (Eventually.of_forall hb)
    exact (norm_sub_le _ _).trans ((add_le_add (hb t) hl).trans_eq (two_mul C).symm)
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_abs_weighted_jumps_le_of_disjoint_finite_lifetimes hv hr hfin T
      (by positivity : 0 ≤ 2 * C) hxb hdisj htop hcoe s)

end StochLean

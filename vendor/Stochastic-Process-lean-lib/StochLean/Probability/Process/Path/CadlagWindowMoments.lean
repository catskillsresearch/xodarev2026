/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagWindowOscillation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Fixed-cap second moments of short cadlag windows

On a measurable good event with jumps bounded by `b`, the positive excess of
the squared capped window envelope over `b²` tends to zero. A fixed cap gives
integrable domination without any moment assumption on a jump count. The
result bounds the asymptotic second moment, but does not presume convergence
of the envelope itself or control a cap that varies with the width.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A fixed real cap on the existing countable short-window envelope. On the
cadlag domain the extended envelope is finite, so `toReal` is its actual value. -/
noncomputable def cappedDenseWindowOscillation (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) (C : ℝ) (ω : Ω) : ℝ :=
  min C (denseWindowOscillation X T δ ω).toReal

theorem measurable_cappedDenseWindowOscillation {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T δ : ℝ≥0) (C : ℝ) :
    Measurable (cappedDenseWindowOscillation X T δ C) :=
  measurable_const.min (measurable_denseWindowOscillation hX T δ).ennreal_toReal

theorem cappedDenseWindowOscillation_nonneg (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) {C : ℝ} (hC : 0 ≤ C) (ω : Ω) :
    0 ≤ cappedDenseWindowOscillation X T δ C ω :=
  le_min hC ENNReal.toReal_nonneg

theorem cappedDenseWindowOscillation_le_cap (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) (C : ℝ) (ω : Ω) :
    cappedDenseWindowOscillation X T δ C ω ≤ C := min_le_left _ _

private theorem tendsto_sq_excess_of_eventually_le {ι : Type*} {l : Filter ι}
    {d : ι → ℝ} {b : ℝ} (hb : 0 ≤ b) (hd : ∀ i, 0 ≤ d i)
    (hbound : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, d i ≤ b + η) :
    Tendsto (fun i ↦ max ((d i) ^ 2 - b ^ 2) 0) l (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun i ↦ ha.trans_le (le_max_right _ _)
  · intro a ha
    let η : ℝ := min 1 (a / (4 * (b + 1)))
    have hden : 0 < 4 * (b + 1) := by positivity
    have hη : 0 < η := lt_min zero_lt_one (div_pos ha hden)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηa : η * (4 * (b + 1)) ≤ a :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    filter_upwards [hbound η hη] with i hi
    have hs : (d i) ^ 2 ≤ (b + η) ^ 2 :=
      (sq_le_sq₀ (hd i) (add_nonneg hb hη.le)).mpr hi
    have hηsq : η ^ 2 ≤ η := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hη1 hη.le
    have hsmall : (d i) ^ 2 - b ^ 2 < a := by
      nlinarith only [hs, hηsq, hηa, ha, hb, hη.le]
    exact max_lt hsmall ha

theorem IsCadlagPath.tendsto_cappedDenseWindowOscillation_sq_excess
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hj : ∀ t, 0 < t → t ≤ T → ‖jumpProcess X t ω‖ ≤ b)
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ≥0} (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i ↦ max ((cappedDenseWindowOscillation X T (δ i) C ω) ^ 2 - b ^ 2) 0)
      l (𝓝 0) := by
  apply tendsto_sq_excess_of_eventually_le hb
    (fun i ↦ cappedDenseWindowOscillation_nonneg X T (δ i) hC ω)
  intro η hη
  filter_upwards [hX.eventually_toReal_denseWindowOscillation_le_of_jumpProcess_bound T hb hη hj hδ]
    with i hi
  exact (min_le_right _ _).trans hi

theorem tendsto_integral_cappedDenseWindowOscillation_sq_excess_indicator
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (hmX : ∀ t, Measurable (X t)) (hX : HasCadlagPaths X P)
    (T : ℝ≥0) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    {A : Set Ω} (hA : MeasurableSet A)
    (hj : ∀ᵐ ω ∂P, ω ∈ A → ∀ t, 0 < t → t ≤ T → ‖jumpProcess X t ω‖ ≤ b)
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω,
      A.indicator (fun ω ↦ max ((cappedDenseWindowOscillation X T (δ n) C ω) ^ 2 - b ^ 2) 0) ω ∂P)
      atTop (𝓝 0) := by
  let d := fun n ↦ cappedDenseWindowOscillation X T (δ n) C
  have hdm (n : ℕ) : Measurable (d n) := measurable_cappedDenseWindowOscillation hmX T (δ n) C
  have hdb (n : ℕ) (ω : Ω) : (d n ω) ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (cappedDenseWindowOscillation_nonneg X T (δ n) hC ω) hC).mpr
      (cappedDenseWindowOscillation_le_cap X T (δ n) C ω)
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ A.indicator (fun ω ↦ max ((d n ω) ^ 2 - b ^ 2) 0) ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hX, hj] with ω hω hjω
    by_cases hωA : ω ∈ A
    · simpa only [indicator_of_mem hωA] using
        hω.tendsto_cappedDenseWindowOscillation_sq_excess T hC hb (hjω hωA) hδ
    · simpa only [indicator_of_notMem hωA] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hbound (n : ℕ) : ∀ᵐ ω ∂P,
      ‖A.indicator (fun ω ↦ max ((d n ω) ^ 2 - b ^ 2) 0) ω‖ ≤ C ^ 2 := by
    filter_upwards with ω
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le ((sub_le_self _ (sq_nonneg b)).trans (hdb n ω)) (sq_nonneg C)
    · rw [indicator_of_notMem hωA, norm_zero]
      exact sq_nonneg C
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ C ^ 2)
    (fun n ↦ ((((hdm n).pow_const 2).sub measurable_const).max measurable_const).indicator hA
      |>.aestronglyMeasurable)
    (integrable_const (C ^ 2)) hbound hlim
  simpa only [integral_zero, Pi.sub_apply, d] using hint

theorem eventually_integral_sq_cappedDenseWindowOscillation_le
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (hmX : ∀ t, Measurable (X t)) (hX : HasCadlagPaths X P)
    (T : ℝ≥0) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    {A : Set Ω} (hA : MeasurableSet A)
    (hj : ∀ᵐ ω ∂P, ω ∈ A → ∀ t, 0 < t → t ≤ T → ‖jumpProcess X t ω‖ ≤ b)
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (∫ ω, (cappedDenseWindowOscillation X T (δ n) C ω) ^ 2 ∂P) ≤
      b ^ 2 * P.real A + C ^ 2 * P.real Aᶜ + ε := by
  let d := fun n ↦ cappedDenseWindowOscillation X T (δ n) C
  let e := fun n ↦ A.indicator (fun ω ↦ max ((d n ω) ^ 2 - b ^ 2) 0)
  let q : Ω → ℝ := A.indicator (fun _ ↦ b ^ 2) + Aᶜ.indicator (fun _ ↦ C ^ 2)
  have hdm (n : ℕ) : Measurable (d n) := measurable_cappedDenseWindowOscillation hmX T (δ n) C
  have hdb (n : ℕ) (ω : Ω) : (d n ω) ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (cappedDenseWindowOscillation_nonneg X T (δ n) hC ω) hC).mpr
      (cappedDenseWindowOscillation_le_cap X T (δ n) C ω)
  have hdi (n : ℕ) : Integrable (fun ω ↦ (d n ω) ^ 2) P :=
    (integrable_const (C ^ 2)).mono' ((hdm n).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hdb n ω)
  have hei (n : ℕ) : Integrable (e n) P := by
    have hem : Measurable (e n) :=
      ((((hdm n).pow_const 2).sub measurable_const).max measurable_const).indicator hA
    apply (integrable_const (C ^ 2)).mono' hem.aestronglyMeasurable
    filter_upwards with ω
    by_cases hωA : ω ∈ A
    · rw [show e n ω = max ((d n ω) ^ 2 - b ^ 2) 0 from indicator_of_mem hωA _,
        Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le ((sub_le_self _ (sq_nonneg b)).trans (hdb n ω)) (sq_nonneg C)
    · rw [show e n ω = 0 from indicator_of_notMem hωA _, norm_zero]
      exact sq_nonneg C
  have hqi : Integrable q P :=
    ((integrable_const (b ^ 2)).indicator hA).add
      ((integrable_const (C ^ 2)).indicator hA.compl)
  have hq : (∫ ω, q ω ∂P) = b ^ 2 * P.real A + C ^ 2 * P.real Aᶜ := by
    change (∫ ω, A.indicator (fun _ ↦ b ^ 2) ω + Aᶜ.indicator (fun _ ↦ C ^ 2) ω ∂P) = _
    rw [integral_add ((integrable_const _).indicator hA)
      ((integrable_const _).indicator hA.compl), integral_indicator hA, integral_indicator hA.compl]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    ring
  have hle (n : ℕ) : (∫ ω, (d n ω) ^ 2 ∂P) ≤
      b ^ 2 * P.real A + C ^ 2 * P.real Aᶜ + ∫ ω, e n ω ∂P := by
    rw [← hq, ← integral_add hqi (hei n)]
    apply integral_mono (hdi n) (hqi.add (hei n))
    intro ω
    by_cases hωA : ω ∈ A
    · have he : (d n ω) ^ 2 - b ^ 2 ≤ max ((d n ω) ^ 2 - b ^ 2) 0 := le_max_left _ _
      simp only [q, e, Pi.add_apply, indicator_of_mem hωA,
        indicator_of_notMem (show ω ∉ Aᶜ from notMem_compl_iff.mpr hωA), add_zero]
      linarith only [he]
    · simpa only [q, e, Pi.add_apply, indicator_of_notMem hωA,
        indicator_of_mem (show ω ∈ Aᶜ from hωA), zero_add, add_zero] using hdb n ω
  have hlim := tendsto_integral_cappedDenseWindowOscillation_sq_excess_indicator
    hmX hX T hC hb hA hj hδ
  filter_upwards [hlim.eventually_lt_const hε] with n hn
  exact (hle n).trans (add_le_add le_rfl hn.le)

end ProbabilityTheory

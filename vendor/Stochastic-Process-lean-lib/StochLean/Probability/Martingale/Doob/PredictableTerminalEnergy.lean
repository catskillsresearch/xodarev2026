/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableEnergy
public import StochLean.ForMathlib.MeasureTheory.FatouNonnegative

/-! # Terminal second moments from bounded conditional remaining variation

Protter III.10, Lemma 1: an increasing predictable discrete process starting at
zero, with uniformly bounded conditional remaining mean, has terminal second
moment at most twice the square of that bound. No coordinate or terminal L2
premise is used. Fixed-level truncations preserve the original filtration and
predictability. A diagonal sequence and native Fatou remove both truncations.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℕ mΩ} {C : ℕ → Ω → ℝ} {Z : Ω → ℝ}

/-- The source conditional-tail hypothesis is an L1 hypothesis. The L2
terminal property and the second-moment estimate are derived conclusions. -/
theorem IsStronglyPredictable.memLp_two_terminal_of_condExp_tail_bound
    (hp : IsStronglyPredictable F C) (hm : HasMonotonePaths C P)
    (h0 : C 0 =ᵐ[P] 0) (hZ : Integrable Z P)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun k ↦ C k ω) atTop (𝓝 (Z ω)))
    {N : ℝ} (hN : 0 ≤ N) (hb : ∀ k, P[Z - C k | F k] ≤ᵐ[P] (fun _ ↦ N)) :
    MemLp Z 2 P ∧ (∫ ω, Z ω ^ 2 ∂P) ≤ 2 * N ^ 2 := by
  have hpath : ∀ᵐ ω ∂P, (∀ k, 0 ≤ C k ω) ∧ (∀ k, C k ω ≤ Z ω) := by
    filter_upwards [hm, h0, hl] with ω hmω h0ω hlω
    constructor
    · intro k
      have he := hmω (Nat.zero_le k)
      simpa only [h0ω, Pi.zero_apply] using he
    · exact fun k ↦ hmω.ge_of_tendsto hlω k
  have hiC (k : ℕ) : Integrable (C k) P := by
    apply hZ.mono' ((hp.stronglyAdapted k).mono (F.le k)).aestronglyMeasurable
    filter_upwards [hpath] with ω hω
    rw [Real.norm_of_nonneg (hω.1 k)]
    exact hω.2 k
  let D (R : ℝ) : ℕ → Ω → ℝ := fun k ω ↦ min (C k ω) R
  have hpD (R : ℝ) : IsStronglyPredictable F (D R) := by
    apply IsStronglyPredictable.of_measurable_add_one
    · exact ((hp.stronglyAdapted 0).measurable.min measurable_const).stronglyMeasurable
    · intro k
      exact ((hp.measurable_add_one k).measurable.min measurable_const).stronglyMeasurable
  have hmD (R : ℝ) : HasMonotonePaths (D R) P :=
    hm.mono fun _ hω _ _ hij ↦ min_le_min (hω hij) le_rfl
  have h0D (R : ℝ) (hR : 0 ≤ R) : D R 0 =ᵐ[P] 0 := by
    filter_upwards [h0] with ω hω
    change min (C 0 ω) R = 0
    simpa only [hω, Pi.zero_apply] using min_eq_left hR
  have hLD (R : ℝ) (hR : 0 ≤ R) (k : ℕ) : MemLp (D R k) 2 P := by
    apply MemLp.of_bound (((hpD R).stronglyAdapted k).mono (F.le k)).aestronglyMeasurable R
    filter_upwards [hpath] with ω hω
    change ‖min (C k ω) R‖ ≤ R
    rw [Real.norm_of_nonneg (le_min (hω.1 k) hR)]
    exact min_le_right _ _
  have hbound (R : ℝ) (hR : 0 ≤ R) (n k : ℕ) :
      P[D R n - D R k | F k] ≤ᵐ[P] (fun _ ↦ N) := by
    have hle : D R n - D R k ≤ᵐ[P] Z - C k := by
      filter_upwards [hpath] with ω hω
      change min (C n ω) R - min (C k ω) R ≤ Z ω - C k ω
      by_cases hk : C k ω ≤ R
      · rw [min_eq_left hk]
        exact sub_le_sub_right ((min_le_left _ _).trans (hω.2 n)) _
      · rw [min_eq_right (le_of_not_ge hk)]
        exact (sub_nonpos.mpr (min_le_right _ _)).trans (sub_nonneg.mpr (hω.2 k))
    exact (condExp_mono (((hLD R hR n).integrable (by norm_num)).sub
      ((hLD R hR k).integrable (by norm_num))) (hZ.sub (hiC k)) hle).trans (hb k)
  have hE (n : ℕ) : (∫ ω, D (n : ℝ) n ω ^ 2 ∂P) ≤ 2 * N ^ 2 :=
    (hpD n).integral_sq_le_of_condExp_tail_bound (hmD n) (h0D n (Nat.cast_nonneg n))
      (hLD n (Nat.cast_nonneg n)) hN n (fun k _ ↦ hbound n (Nat.cast_nonneg n) n k)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ D (n : ℝ) n ω ^ 2) atTop
      (𝓝 (Z ω ^ 2)) := by
    filter_upwards [hl, hpath] with ω hlω hω
    have he : (fun n : ℕ ↦ D (n : ℝ) n ω) =ᶠ[atTop] (fun n ↦ C n ω) := by
      filter_upwards [eventually_ge_atTop (⌈Z ω⌉₊)] with n hn
      apply min_eq_left
      exact (hω.2 n).trans ((Nat.le_ceil (Z ω)).trans (Nat.cast_le.mpr hn))
    exact (hlω.congr' he.symm).pow 2
  obtain ⟨hiSq, hSq⟩ := integrable_and_integral_le_of_nonneg_ae_tendsto
    (fun n ↦ (hLD n (Nat.cast_nonneg n) n).integrable_sq)
    (fun n ↦ Eventually.of_forall fun ω ↦ sq_nonneg (D n n ω)) hlim
    (by positivity : 0 ≤ 2 * N ^ 2) hE
  exact ⟨(memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mpr hiSq, hSq⟩

end MeasureTheory

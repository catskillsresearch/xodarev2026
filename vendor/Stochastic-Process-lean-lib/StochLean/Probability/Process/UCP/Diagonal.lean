/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Algebra

/-! # Simultaneous UCP diagonals on growing horizons

One index is chosen for each pair of convergent rows. Both selected errors vanish
in UCP; the construction does not require a uniform convergence rate across rows.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem tendstoUCP_zero_of_diagonal_deviation_bound
    {D : ℕ → ℝ≥0 → Ω → ℝ} {a : ℕ → ℝ} {b : ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hd : ∀ n : ℕ, P {ω | ∃ t ≤ (n : ℝ≥0), a n < ‖D n t ω‖} ≤ b n) :
    TendstoUCP P D atTop 0 := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  simp only [Pi.zero_apply, sub_zero]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (ha.eventually_lt_const hε)
  obtain ⟨NP, hNP⟩ := ENNReal.tendsto_atTop_zero.mp hb η hη
  refine ⟨max NT (max NE NP), fun n hn ↦ ?_⟩
  have hTn : T ≤ (n : ℝ≥0) := hNT.trans (by
    exact_mod_cast (le_max_left NT (max NE NP)).trans hn)
  have hEn := hNE n ((le_max_left NE NP).trans ((le_max_right NT (max NE NP)).trans hn))
  have hPn := hNP n ((le_max_right NE NP).trans ((le_max_right NT (max NE NP)).trans hn))
  apply le_trans ?_ ((hd n).trans hPn)
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  exact ⟨t, ht.trans hTn, hEn.trans hω⟩

theorem exists_diagonal_tendstoUCP_sub_zero
    {A B : ℕ → ℕ → ℝ≥0 → Ω → ℝ} {X Y : ℕ → ℝ≥0 → Ω → ℝ}
    (hA : ∀ n, TendstoUCP P (A n) atTop (X n))
    (hB : ∀ n, TendstoUCP P (B n) atTop (Y n)) :
    ∃ k : ℕ → ℕ, TendstoUCP P (fun n ↦ A n (k n) - X n) atTop 0 ∧
      TendstoUCP P (fun n ↦ B n (k n) - Y n) atTop 0 := by
  let a : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ha : ∀ n, 0 < a n := fun n ↦ by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hblim : Tendsto (fun n ↦ ENNReal.ofReal (a n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp halim
  have hAt : ∀ n : ℕ, ∃ K, ∀ k ≥ K,
      P {ω | ∃ t ≤ (n : ℝ≥0), a n < ‖A n k t ω - X n t ω‖} ≤ ENNReal.ofReal (a n) := by
    intro n
    exact ENNReal.tendsto_atTop_zero.mp
      (tendstoUCP_iff_measure_exists_norm_lt.mp (hA n) n (a n) (ha n))
      (ENNReal.ofReal (a n)) (ENNReal.ofReal_pos.mpr (ha n))
  have hBt : ∀ n : ℕ, ∃ K, ∀ k ≥ K,
      P {ω | ∃ t ≤ (n : ℝ≥0), a n < ‖B n k t ω - Y n t ω‖} ≤ ENNReal.ofReal (a n) := by
    intro n
    exact ENNReal.tendsto_atTop_zero.mp
      (tendstoUCP_iff_measure_exists_norm_lt.mp (hB n) n (a n) (ha n))
      (ENNReal.ofReal (a n)) (ENNReal.ofReal_pos.mpr (ha n))
  choose KA hKA using hAt
  choose KB hKB using hBt
  refine ⟨fun n ↦ max (KA n) (KB n), ?_, ?_⟩
  · exact tendstoUCP_zero_of_diagonal_deviation_bound halim hblim
      (fun n ↦ hKA n _ (le_max_left _ _))
  · exact tendstoUCP_zero_of_diagonal_deviation_bound halim hblim
      (fun n ↦ hKB n _ (le_max_right _ _))

end ProbabilityTheory

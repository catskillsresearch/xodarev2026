/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Reverse one-sided martingale control

The time index is Mathlib's order dual of the naturals, with its existing
filtration and supermartingale owners. Increasing ordinary natural indices
therefore correspond to decreasing filtration times. Nonnegative conditional
residuals are measured by differences of expectations, not assumed small.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕᵒᵈ mΩ} {X : ℕᵒᵈ → Ω → ℝ}

theorem Supermartingale.reverse_expectation_monotone (hX : Supermartingale X F P) :
    Monotone (fun n : ℕ ↦ ∫ ω, X (OrderDual.toDual n) ω ∂P) := by
  intro i j hij
  have h := integral_mono_ae integrable_condExp (hX.integrable (OrderDual.toDual j))
    (hX.condExp_ae_le (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))
  rwa [integral_condExp (F.le (OrderDual.toDual j))] at h

theorem Supermartingale.eLpNorm_reverse_condExp_sub_eq (hX : Supermartingale X F P)
    {i j : ℕ} (hij : i ≤ j) :
    eLpNorm (X (OrderDual.toDual j) - P[X (OrderDual.toDual i) | F (OrderDual.toDual j)])
      1 P = ENNReal.ofReal ((∫ ω, X (OrderDual.toDual j) ω ∂P) -
        ∫ ω, X (OrderDual.toDual i) ω ∂P) := by
  have hi : Integrable
      (X (OrderDual.toDual j) - P[X (OrderDual.toDual i) | F (OrderDual.toDual j)]) P :=
    (hX.integrable _).sub integrable_condExp
  have hn : ∀ᵐ ω ∂P, 0 ≤ (X (OrderDual.toDual j) -
      P[X (OrderDual.toDual i) | F (OrderDual.toDual j)]) ω := by
    filter_upwards [hX.condExp_ae_le
      (show OrderDual.toDual j ≤ OrderDual.toDual i from hij)] with ω hω
    exact sub_nonneg.mpr hω
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  have he : (fun ω ↦ ‖(X (OrderDual.toDual j) -
      P[X (OrderDual.toDual i) | F (OrderDual.toDual j)]) ω‖) =ᵐ[P]
      X (OrderDual.toDual j) - P[X (OrderDual.toDual i) | F (OrderDual.toDual j)] :=
    hn.mono fun _ hω ↦ Real.norm_of_nonneg hω
  rw [integral_congr_ae he]
  simp only [Pi.sub_apply]
  rw [integral_sub (hX.integrable _) integrable_condExp,
    integral_condExp (F.le (OrderDual.toDual j))]

theorem Supermartingale.eLpNorm_reverse_le_of_expectation_bounded
    (hX : Supermartingale X F P) {C : ℝ} (hC : ∀ n, (∫ ω, X n ω ∂P) ≤ C)
    (n : ℕᵒᵈ) :
    eLpNorm (X n) 1 P ≤ ENNReal.ofReal (C - ∫ ω, X (OrderDual.toDual 0) ω ∂P) +
      eLpNorm (X (OrderDual.toDual 0)) 1 P := by
  let Z := P[X (OrderDual.toDual 0) | F n]
  have hZ : Integrable Z P := integrable_condExp
  calc
    _ ≤ eLpNorm (X n - Z) 1 P + eLpNorm Z 1 P := by
      simpa only [sub_add_cancel] using
        eLpNorm_add_le ((hX.integrable n).sub hZ).aestronglyMeasurable
          hZ.aestronglyMeasurable (le_refl (1 : ℝ≥0∞))
    _ = ENNReal.ofReal ((∫ ω, X n ω ∂P) - ∫ ω, X (OrderDual.toDual 0) ω ∂P) +
        eLpNorm Z 1 P := by
      exact congrArg (fun r : ℝ≥0∞ ↦ r + eLpNorm Z 1 P)
        (hX.eLpNorm_reverse_condExp_sub_eq (Nat.zero_le (OrderDual.ofDual n)))
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal (sub_le_sub_right (hC n) _))
      (eLpNorm_condExp_le_eLpNorm _ (le_refl (1 : ℝ≥0∞)))

/-- A reverse supermartingale with expectations bounded above is uniformly
integrable. Small conditional residuals control the tail; the finite prefix
and all conditional expectations of one integrable coordinate are UI. -/
theorem Supermartingale.uniformIntegrable_of_reverse_expectation_bounded
    (hX : Supermartingale X F P) {C : ℝ} (hC : ∀ n, (∫ ω, X n ω ∂P) ≤ C) :
    UniformIntegrable X 1 P := by
  refine ⟨fun n ↦ (hX.integrable n).aestronglyMeasurable, ?_, ?_⟩
  · intro ε hε
    let m (n : ℕ) := ∫ ω, X (OrderDual.toDual n) ω ∂P
    have hm : BddAbove (Set.range m) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hC _
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (⨆ n, m n) - ε / 2 < m N := by
      by_contra! h
      have hle : (⨆ n, m n) ≤ (⨆ n, m n) - ε / 2 := ciSup_le h
      linarith
    have hfinite : UnifIntegrable (fun n : Fin (N + 1) ↦ X (OrderDual.toDual n.val)) 1 P :=
      unifIntegrable_finite le_rfl ENNReal.one_ne_top
        (fun n ↦ memLp_one_iff_integrable.mpr (hX.integrable _))
    obtain ⟨δ₀, hδ₀, hsmall₀⟩ := hfinite hε
    obtain ⟨δ₁, hδ₁, hsmall₁⟩ :=
      (hX.integrable (OrderDual.toDual N)).uniformIntegrable_condExp F.le
        |>.unifIntegrable (half_pos hε)
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
    intro n s hs hPs
    by_cases hn : OrderDual.ofDual n ≤ N
    · exact hsmall₀ ⟨OrderDual.ofDual n, Nat.lt_succ_of_le hn⟩ s hs
        (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    · have hNn : N ≤ OrderDual.ofDual n := (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      let Z := P[X (OrderDual.toDual N) | F n]
      have hZ : Integrable Z P := integrable_condExp
      have hd : Integrable (X n - Z) P := (hX.integrable n).sub hZ
      have hdiff : eLpNorm (X n - Z) 1 P ≤ ENNReal.ofReal (ε / 2) := by
        apply (hX.eLpNorm_reverse_condExp_sub_eq hNn).trans_le
        apply ENNReal.ofReal_le_ofReal
        have hmn := le_ciSup hm (OrderDual.ofDual n)
        change (∫ ω, X n ω ∂P) - (∫ ω, X (OrderDual.toDual N) ω ∂P) ≤ ε / 2
        dsimp only [m] at hmn hN
        change (∫ ω, X n ω ∂P) ≤ ⨆ k : ℕ, ∫ ω, X (OrderDual.toDual k) ω ∂P at hmn
        linarith
      have he : s.indicator (X n) = s.indicator Z + s.indicator (X n - Z) := by
        funext ω
        by_cases hω : ω ∈ s <;> simp [hω]
      rw [he]
      calc
        _ ≤ eLpNorm (s.indicator Z) 1 P + eLpNorm (s.indicator (X n - Z)) 1 P :=
          eLpNorm_add_le (hZ.indicator hs).aestronglyMeasurable
            (hd.indicator hs).aestronglyMeasurable le_rfl
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (hsmall₁ n s hs
            (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
            ((eLpNorm_indicator_le _).trans hdiff)
        _ = _ := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
          congr 1
          ring
  · let B := ENNReal.ofReal (C - ∫ ω, X (OrderDual.toDual 0) ω ∂P) +
      eLpNorm (X (OrderDual.toDual 0)) 1 P
    have hB : B ≠ ∞ := (ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, (memLp_one_iff_integrable.mpr (hX.integrable _)).eLpNorm_lt_top⟩).ne
    refine ⟨B.toNNReal, fun n ↦ ?_⟩
    rw [ENNReal.coe_toNNReal hB]
    exact hX.eLpNorm_reverse_le_of_expectation_bounded hC n

/-- The dual assertion for reverse submartingales retains the direction of
the expectation bound: it must be a lower bound, not an upper bound. -/
theorem Submartingale.uniformIntegrable_of_reverse_expectation_bounded_below
    (hX : Submartingale X F P) {C : ℝ} (hC : ∀ n, C ≤ ∫ ω, X n ω ∂P) :
    UniformIntegrable X 1 P := by
  have hn : ∀ n, (∫ ω, (-X) n ω ∂P) ≤ -C := by
    intro n
    simpa only [Pi.neg_apply, integral_neg] using neg_le_neg (hC n)
  obtain ⟨_, hu, B, hb⟩ := hX.neg.uniformIntegrable_of_reverse_expectation_bounded hn
  refine ⟨fun n ↦ (hX.integrable n).aestronglyMeasurable, ?_, B, fun n ↦ ?_⟩
  · simpa only [neg_neg] using hu.neg
  · simpa only [Pi.neg_apply, eLpNorm_neg] using hb n

end MeasureTheory

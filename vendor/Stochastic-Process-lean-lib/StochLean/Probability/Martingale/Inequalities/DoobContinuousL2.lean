/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobFiniteTime
public import StochLean.Probability.Process.Path.Supremum
public import StochLean.Probability.Moments.L2
public import Mathlib.MeasureTheory.Order.Lattice

/-! # An actual dense-grid L2 maximal bound for continuous-time martingales

The supremum is the existing extended nonnegative owner, not a real-valued
fallback at infinity. Finite maxima, sorted-time Doob estimates and monotone
convergence prove the bound before any finiteness assertion is made.
-/

@[expose] public section

open Filter Set Finset ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E} {T : ℝ≥0}

theorem Martingale.lintegral_denseRunningSupremum_norm_sq_le (hX : Martingale X F P)
    (hT : MemLp (X T) 2 P) :
    (∫⁻ ω, denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω ∂P) ≤
      4 * ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ 2 ∂P) := by
  classical
  let s (n : ℕ) := (range (n + 1)).image (denseTimeUpTo T)
  have hs (n : ℕ) : (s n).Nonempty := nonempty_range_add_one.image _
  let g (n : ℕ) (ω : Ω) := (s n).sup' (hs n) (fun t ↦ ‖X t ω‖)
  have hgm (n : ℕ) : Measurable (g n) := by
    convert!
      (Finset.measurable_sup' (hs n) (fun t _ ↦
        ((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl)) using 1
    ext ω
    simp only [g, Finset.sup'_apply]
  have hgn (n : ℕ) (ω : Ω) : 0 ≤ g n ω := by
    obtain ⟨t, ht⟩ := hs n
    exact (norm_nonneg _).trans (le_sup' (fun t ↦ ‖X t ω‖) ht)
  have hbound (n : ℕ) : eLpNorm (g n) 2 P ≤ 2 * eLpNorm (X T) 2 P := by
    have h := hX.eLpNorm_norm_finset_sup_le (by norm_num : (1 : ℝ) < 2) (s n) (hs n)
      (by
        intro t ht
        obtain ⟨k, _, rfl⟩ := mem_image.mp ht
        exact min_le_left _ _)
    norm_num at h
    exact h
  have hgp (n : ℕ) : MemLp (g n) 2 P :=
    ⟨(hgm n).aestronglyMeasurable, (hbound n).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hT.eLpNorm_lt_top)⟩
  have hint (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (g n ω ^ 2) ∂P) ≤
      4 * ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ 2 ∂P) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hgp n).integrable_sq
      (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    rw [← sq_eLpNorm_two_eq_ofReal_integral_sq (hgp n).integrable_sq,
      ← sq_eLpNorm_two_eq_ofReal_integral_sq hT.norm.integrable_sq, eLpNorm_norm]
    have h := pow_le_pow_left' (hbound n) 2
    norm_num [mul_pow] at h
    exact h
  have hmono : Monotone (fun n ω ↦ ENNReal.ofReal (g n ω ^ 2)) := by
    intro n m hnm ω
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (hgn n ω) (hgn m ω)).mpr
    apply sup'_le
    intro t ht
    exact le_sup' (fun t ↦ ‖X t ω‖)
      (image_subset_image (range_mono (Nat.add_le_add_right hnm 1)) ht)
  have heq (ω : Ω) : (⨆ n, ENNReal.ofReal (g n ω ^ 2)) =
      denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω := by
    apply le_antisymm
    · apply iSup_le
      intro n
      obtain ⟨t, ht, he⟩ := (s n).exists_mem_eq_sup' (hs n) (fun t ↦ ‖X t ω‖)
      obtain ⟨k, _, rfl⟩ := mem_image.mp ht
      change g n ω = ‖X (denseTimeUpTo T k) ω‖ at he
      rw [he]
      exact le_iSup (fun j ↦ ENNReal.ofReal (‖X (denseTimeUpTo T j) ω‖ ^ 2)) k
    · apply iSup_le
      intro k
      apply le_trans _ (le_iSup (fun n ↦ ENNReal.ofReal (g n ω ^ 2)) k)
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (norm_nonneg _) (hgn k ω)).mpr
      exact le_sup' (fun t ↦ ‖X t ω‖) (mem_image.mpr ⟨k, by simp, rfl⟩)
  calc
    _ = ∫⁻ ω, ⨆ n, ENNReal.ofReal (g n ω ^ 2) ∂P := lintegral_congr fun ω ↦ (heq ω).symm
    _ = ⨆ n, ∫⁻ ω, ENNReal.ofReal (g n ω ^ 2) ∂P :=
      lintegral_iSup (fun n ↦ ENNReal.measurable_ofReal.comp ((hgm n).pow_const 2)) hmono
    _ ≤ _ := iSup_le hint

/-- Finiteness is proved for the extended supremum before taking its real value. -/
theorem Martingale.ae_denseRunningSupremum_norm_sq_lt_top (hX : Martingale X F P)
    (hT : MemLp (X T) 2 P) :
    ∀ᵐ ω ∂P, denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω < ∞ := by
  apply ae_lt_top
    (measurable_denseRunningSupremum (fun t ↦
      (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2) T)
  exact ((hX.lintegral_denseRunningSupremum_norm_sq_le hT).trans_lt
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)).ne

theorem Martingale.integrable_toReal_denseRunningSupremum_norm_sq (hX : Martingale X F P)
    (hT : MemLp (X T) 2 P) :
    Integrable (fun ω ↦ (denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω).toReal) P := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_denseRunningSupremum (fun t ↦
      (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2) T).aemeasurable
  exact ((hX.lintegral_denseRunningSupremum_norm_sq_le hT).trans_lt
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)).ne

theorem Martingale.memLp_sqrt_denseRunningSupremum_norm_sq (hX : Martingale X F P)
    (hT : MemLp (X T) 2 P) :
    MemLp (fun ω ↦ Real.sqrt
      (denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω).toReal) 2 P := by
  have hm := (measurable_denseRunningSupremum (fun t ↦
    (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2) T).ennreal_toReal
  apply (memLp_two_iff_integrable_sq hm.sqrt.aestronglyMeasurable).mpr
  simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using
    hX.integrable_toReal_denseRunningSupremum_norm_sq hT

theorem Martingale.integral_toReal_denseRunningSupremum_norm_sq_le (hX : Martingale X F P)
    (hT : MemLp (X T) 2 P) :
    (∫ ω, (denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω).toReal ∂P) ≤
      4 * ∫ ω, ‖X T ω‖ ^ 2 ∂P := by
  rw [integral_toReal
    (measurable_denseRunningSupremum (fun t ↦
      (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2) T).aemeasurable
    (hX.ae_denseRunningSupremum_norm_sq_lt_top hT)]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_lt_top (by norm_num : (4 : ℝ≥0∞) < ∞) ENNReal.ofReal_lt_top).ne
    (hX.lintegral_denseRunningSupremum_norm_sq_le hT)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)] using h

/-- One event supports the maximal bound at every time, including the terminal time.
No uncountable intersection of coordinate almost-everywhere assertions is used. -/
theorem Martingale.ae_norm_le_sqrt_denseRunningSupremum_norm_sq (hX : Martingale X F P)
    (hpath : HasRightContinuousPaths X P) (hT : MemLp (X T) 2 P) :
    ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ Real.sqrt
      (denseRunningSupremum (fun s ω ↦ ‖X s ω‖ ^ 2) T ω).toReal := by
  filter_upwards [hX.ae_denseRunningSupremum_norm_sq_lt_top hT, hpath] with ω hfin hcont
  intro t ht
  apply Real.le_sqrt_of_sq_le
  exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp
    (ofReal_le_denseRunningSupremum_of_rightContinuous ht (fun s ↦ (hcont s).norm.pow 2))

/-- Continuous-time Doob L2 control in a form usable for dominated convergence.
The witness is explicitly the square root of the finite dense-grid square supremum. -/
theorem Martingale.exists_memLp_two_maximalEnvelope (hX : Martingale X F P)
    (hpath : HasRightContinuousPaths X P) (hT : MemLp (X T) 2 P) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 4 * ∫ ω, ‖X T ω‖ ^ 2 ∂P := by
  refine ⟨fun ω ↦ Real.sqrt
    (denseRunningSupremum (fun t ω ↦ ‖X t ω‖ ^ 2) T ω).toReal, ?_,
    fun _ ↦ Real.sqrt_nonneg _, hX.memLp_sqrt_denseRunningSupremum_norm_sq hT,
    hX.ae_norm_le_sqrt_denseRunningSupremum_norm_sq hpath hT, ?_⟩
  · exact (measurable_denseRunningSupremum (fun t ↦
      (((hX.stronglyAdapted t).norm.measurable).mono (F.le t) le_rfl).pow_const 2)
        T).ennreal_toReal.sqrt
  · simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using
      hX.integral_toReal_denseRunningSupremum_norm_sq_le hT

end MeasureTheory

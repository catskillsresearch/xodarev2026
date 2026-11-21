/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableEnergy
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Terminal energy for differences of predictable increasing processes

Monotonicity, the zero initial value and an actual square-integrable terminal
limit give coordinate square integrability and convergence in L2. A finite
telescoping inequality, conditional-expectation pullout for predictable
increments, and dominated convergence then give the difference energy bound.
No terminal energy bound or L2-convergence conclusion is an input. This is a
generic estimate, not a construction of the dyadic Doob approximants.
-/

@[expose] public section

open ProbabilityTheory Filter Finset
open scoped ENNReal Topology

namespace MeasureTheory

private theorem twice_mul_sub_sq_le_remaining_sum (x : ℕ → ℝ) (z : ℝ)
    (n : ℕ) (h0 : x 0 = 0) :
    2 * (z * x n) - (x n) ^ 2 ≤
      2 * ∑ k ∈ range n, (z - x k) * (x (k + 1) - x k) := by
  have he : (∑ k ∈ range n, ((z - x k) ^ 2 - (z - x (k + 1)) ^ 2)) =
      z ^ 2 - (z - x n) ^ 2 := by
    rw [sum_range_sub', h0]
    ring
  have hl : (∑ k ∈ range n, ((z - x k) ^ 2 - (z - x (k + 1)) ^ 2)) ≤
      2 * ∑ k ∈ range n, (z - x k) * (x (k + 1) - x k) := by
    rw [mul_sum]
    exact sum_le_sum fun k _ ↦ by nlinarith [sq_nonneg (x (k + 1) - x k)]
  rw [he] at hl
  nlinarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {A B : ℕ → Ω → ℝ} {U V W : Ω → ℝ}

omit [IsFiniteMeasure P] in
private theorem monotone_nonneg_le_terminal (hm : HasMonotonePaths A P)
    (h0 : A 0 =ᵐ[P] 0)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (U ω))) :
    ∀ᵐ ω ∂P, (∀ n, 0 ≤ A n ω) ∧ (∀ n, A n ω ≤ U ω) := by
  filter_upwards [hm, h0, hl] with ω hmω h0ω hlω
  constructor
  · intro n
    simpa only [h0ω, Pi.zero_apply] using hmω (Nat.zero_le n)
  · exact fun n ↦ hmω.ge_of_tendsto hlω n

/-- Monotone predictable processes starting at zero converge in L2 to their
actual L2 terminal limits. The coordinate L2 hypotheses and upper bounds are
derived from monotonicity and the supplied almost-sure limit. -/
theorem IsStronglyPredictable.memLp_two_and_tendsto_of_monotone_terminal
    (hp : IsStronglyPredictable F A) (hm : HasMonotonePaths A P)
    (h0 : A 0 =ᵐ[P] 0) (hU : MemLp U 2 P)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (U ω))) :
    (∀ n, MemLp (A n) 2 P) ∧
      Tendsto (fun n ↦ eLpNorm (A n - U) 2 P) atTop (𝓝 0) := by
  have hpath := monotone_nonneg_le_terminal hm h0 hl
  have hmeas (n : ℕ) : AEStronglyMeasurable (A n) P :=
    ((hp.stronglyAdapted n).mono (F.le n)).aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ ω ∂P, ‖A n ω‖ ≤ ‖U ω‖ := by
    filter_upwards [hpath] with ω hω
    rw [Real.norm_of_nonneg (hω.1 n)]
    exact (hω.2 n).trans (le_abs_self _)
  have hui : UniformIntegrable A 2 P :=
    (uniformIntegrable_const (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hU).mono_norm
      hmeas hdom
  exact ⟨fun n ↦ hU.mono (hmeas n) (hdom n),
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hmeas hU hui.2.1 hl⟩

/-- A conditional remaining-difference bound controls the terminal difference
energy. The dominating terminal variable `W` is square integrable and
nonnegative, and the increasing terminal variables are actual path limits.
No energy or convergence assertion is assumed. -/
theorem IsStronglyPredictable.integral_sq_sub_terminal_le_of_condExp_tail_norm_bound
    (hpA : IsStronglyPredictable F A) (hpB : IsStronglyPredictable F B)
    (hmA : HasMonotonePaths A P) (hmB : HasMonotonePaths B P)
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0)
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) (hW : MemLp W 2 P)
    (hWn : 0 ≤ᵐ[P] W)
    (hlA : ∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (U ω)))
    (hlB : ∀ᵐ ω ∂P, Tendsto (fun n ↦ B n ω) atTop (𝓝 (V ω)))
    (hb : ∀ k, ∀ᵐ ω ∂P,
      ‖P[(U - A k) - (V - B k) | F k] ω‖ ≤ P[W | F k] ω) :
    (∫ ω, (U ω - V ω) ^ 2 ∂P) ≤ 2 * ∫ ω, W ω * (U ω + V ω) ∂P := by
  obtain ⟨hLA, _⟩ := hpA.memLp_two_and_tendsto_of_monotone_terminal hmA hA0 hU hlA
  obtain ⟨hLB, _⟩ := hpB.memLp_two_and_tendsto_of_monotone_terminal hmB hB0 hV hlB
  have hpa := monotone_nonneg_le_terminal hmA hA0 hlA
  have hpb := monotone_nonneg_le_terminal hmB hB0 hlB
  let C : ℕ → Ω → ℝ := A - B
  let S : ℕ → Ω → ℝ := A + B
  let z : Ω → ℝ := U - V
  have hLz : MemLp z 2 P := hU.sub hV
  have hLC (n : ℕ) : MemLp (C n) 2 P := (hLA n).sub (hLB n)
  have hLS (n : ℕ) : MemLp (S n) 2 P := (hLA n).add (hLB n)
  have hiC (n : ℕ) : Integrable (C n) P := (hLC n).integrable (by norm_num)
  have hiz : Integrable z P := hLz.integrable (by norm_num)
  have hiW : Integrable W P := hW.integrable (by norm_num)
  have hprod (k : ℕ) : Integrable
      (fun ω ↦ (z ω - C k ω) * (C (k + 1) ω - C k ω)) P :=
    (hLz.sub (hLC k)).integrable_mul ((hLC (k + 1)).sub (hLC k))
  have hprodW (k : ℕ) : Integrable
      (fun ω ↦ W ω * (S (k + 1) ω - S k ω)) P :=
    hW.integrable_mul ((hLS (k + 1)).sub (hLS k))
  have hterm (k : ℕ) :
      (∫ ω, (z ω - C k ω) * (C (k + 1) ω - C k ω) ∂P) ≤
        ∫ ω, W ω * (S (k + 1) ω - S k ω) ∂P := by
    have hsmC : StronglyMeasurable[F k] (C (k + 1) - C k) :=
      ((hpA.measurable_add_one k).sub (hpB.measurable_add_one k)).sub
        ((hpA.stronglyAdapted k).sub (hpB.stronglyAdapted k))
    have hsmS : StronglyMeasurable[F k] (S (k + 1) - S k) :=
      ((hpA.measurable_add_one k).add (hpB.measurable_add_one k)).sub
        ((hpA.stronglyAdapted k).add (hpB.stronglyAdapted k))
    have hpull := condExp_mul_of_stronglyMeasurable_right hsmC (hprod k) (hiz.sub (hiC k))
    have hpullW := condExp_mul_of_stronglyMeasurable_right hsmS (hprodW k) hiW
    have hiCE : Integrable
        (fun ω ↦ P[z - C k | F k] ω * (C (k + 1) ω - C k ω)) P :=
      integrable_condExp.congr hpull
    have hiCEW : Integrable
        (fun ω ↦ P[W | F k] ω * (S (k + 1) ω - S k ω)) P :=
      integrable_condExp.congr hpullW
    have he : z - C k = (U - A k) - (V - B k) := by
      funext ω
      change (U ω - V ω) - (A k ω - B k ω) = (U ω - A k ω) - (V ω - B k ω)
      ring
    have hbk : ∀ᵐ ω ∂P, ‖P[z - C k | F k] ω‖ ≤ P[W | F k] ω := by
      rw [he]
      exact hb k
    calc
      _ = ∫ ω, P[z - C k | F k] ω * (C (k + 1) ω - C k ω) ∂P := by
        rw [← integral_condExp (F.le k)]
        exact integral_congr_ae hpull
      _ ≤ ∫ ω, P[W | F k] ω * (S (k + 1) ω - S k ω) ∂P := by
        apply integral_mono_ae hiCE hiCEW
        filter_upwards [hbk, hmA, hmB, condExp_nonneg (m := F k) hWn]
          with ω hk ha hm hw
        have hda : 0 ≤ A (k + 1) ω - A k ω := sub_nonneg.mpr (ha k.le_succ)
        have hdb : 0 ≤ B (k + 1) ω - B k ω := sub_nonneg.mpr (hm k.le_succ)
        have hd : ‖C (k + 1) ω - C k ω‖ ≤ S (k + 1) ω - S k ω := by
          have hec : C (k + 1) ω - C k ω =
              (A (k + 1) ω - A k ω) - (B (k + 1) ω - B k ω) := by
            dsimp [C]
            ring
          rw [hec]
          have hn := norm_sub_le (A (k + 1) ω - A k ω) (B (k + 1) ω - B k ω)
          rw [Real.norm_of_nonneg hda, Real.norm_of_nonneg hdb] at hn
          exact hn.trans_eq (by dsimp [S]; ring)
        have hp : P[z - C k | F k] ω * (C (k + 1) ω - C k ω) ≤
            ‖P[z - C k | F k] ω‖ * ‖C (k + 1) ω - C k ω‖ := by
          rw [← norm_mul]
          exact le_abs_self _
        exact hp.trans (mul_le_mul hk hd (norm_nonneg _) hw)
      _ = _ := by
        calc
          _ = ∫ ω, P[(fun v ↦ W v * (S (k + 1) v - S k v)) | F k] ω ∂P :=
            (integral_congr_ae hpullW).symm
          _ = _ := integral_condExp (F.le k)
  have hiEnergy (n : ℕ) : Integrable
      (fun ω ↦ 2 * (z ω * C n ω) - (C n ω) ^ 2) P :=
    ((hLz.integrable_mul (hLC n)).const_mul 2).sub (hLC n).integrable_sq
  have hfinite (n : ℕ) :
      (∫ ω, 2 * (z ω * C n ω) - (C n ω) ^ 2 ∂P) ≤
        2 * ∫ ω, W ω * (U ω + V ω) ∂P := by
    have hpoint : ∀ᵐ ω ∂P, 2 * (z ω * C n ω) - (C n ω) ^ 2 ≤
        2 * ∑ k ∈ range n, (z ω - C k ω) * (C (k + 1) ω - C k ω) := by
      filter_upwards [hA0, hB0] with ω ha hb
      apply twice_mul_sub_sq_le_remaining_sum (C · ω) (z ω) n
      change A 0 ω - B 0 ω = 0
      simp only [ha, hb, Pi.zero_apply, sub_self]
    calc
      _ ≤ ∫ ω, 2 * ∑ k ∈ range n, (z ω - C k ω) * (C (k + 1) ω - C k ω) ∂P :=
        integral_mono_ae (hiEnergy n)
          ((integrable_finsetSum _ (fun k _ ↦ hprod k)).const_mul 2) hpoint
      _ = 2 * ∑ k ∈ range n,
          ∫ ω, (z ω - C k ω) * (C (k + 1) ω - C k ω) ∂P := by
        rw [integral_const_mul, integral_finsetSum _ (fun k _ ↦ hprod k)]
      _ ≤ 2 * ∑ k ∈ range n, ∫ ω, W ω * (S (k + 1) ω - S k ω) ∂P :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun k _ ↦ hterm k) (by norm_num)
      _ = 2 * ∫ ω, W ω * S n ω ∂P := by
        rw [← integral_finsetSum _ (fun k _ ↦ hprodW k)]
        congr 1
        apply integral_congr_ae
        filter_upwards [hA0, hB0] with ω ha hb
        rw [← mul_sum, sum_range_sub (fun k ↦ S k ω) n]
        change W ω * ((A n ω + B n ω) - (A 0 ω + B 0 ω)) = W ω * (A n ω + B n ω)
        simp only [ha, hb, Pi.zero_apply, zero_add, sub_zero]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply integral_mono_ae (hW.integrable_mul (hLS n)) (hW.integrable_mul (hU.add hV))
        filter_upwards [hWn, hpa, hpb] with ω hw ha hb
        exact mul_le_mul_of_nonneg_left (add_le_add (ha.2 n) (hb.2 n)) hw
  have hlimit : Tendsto (fun n ↦ ∫ ω, 2 * (z ω * C n ω) - (C n ω) ^ 2 ∂P)
      atTop (𝓝 (∫ ω, (z ω) ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω ↦ 3 * (U ω + V ω) ^ 2)
      (fun n ↦ (hiEnergy n).aestronglyMeasurable) ((hU.add hV).integrable_sq.const_mul 3)
    · intro n
      filter_upwards [hpa, hpb] with ω ha hb
      have hu : 0 ≤ U ω := (ha.1 0).trans (ha.2 0)
      have hv : 0 ≤ V ω := (hb.1 0).trans (hb.2 0)
      have hs : 0 ≤ U ω + V ω := add_nonneg hu hv
      have hzn : ‖z ω‖ ≤ U ω + V ω := by
        have hn := norm_sub_le (U ω) (V ω)
        simpa only [z, Pi.sub_apply, Real.norm_of_nonneg hu, Real.norm_of_nonneg hv] using hn
      have hcn : ‖C n ω‖ ≤ U ω + V ω := by
        have hn := norm_sub_le (A n ω) (B n ω)
        rw [Real.norm_of_nonneg (ha.1 n), Real.norm_of_nonneg (hb.1 n)] at hn
        exact hn.trans (add_le_add (ha.2 n) (hb.2 n))
      calc
        _ ≤ ‖2 * (z ω * C n ω)‖ + ‖(C n ω) ^ 2‖ := norm_sub_le _ _
        _ = 2 * (‖z ω‖ * ‖C n ω‖) + ‖C n ω‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow]
          norm_num
        _ ≤ 3 * (U ω + V ω) ^ 2 := by
          have hm := mul_le_mul hzn hcn (norm_nonneg _) hs
          have hsq := (sq_le_sq₀ (norm_nonneg _) hs).mpr hcn
          nlinarith
    · filter_upwards [hlA, hlB] with ω ha hb
      have hc : Tendsto (fun n ↦ C n ω) atTop (𝓝 (z ω)) := ha.sub hb
      have he : Tendsto (fun n ↦ 2 * (z ω * C n ω) - (C n ω) ^ 2) atTop
          (𝓝 (2 * (z ω * z ω) - (z ω) ^ 2)) :=
        (tendsto_const_nhds.mul (tendsto_const_nhds.mul hc)).sub (hc.pow 2)
      have hvalue : 2 * (z ω * z ω) - (z ω) ^ 2 = (z ω) ^ 2 := by ring
      simpa only [hvalue] using he
  exact le_of_tendsto' hlimit hfinite

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Convergence.LocalVitali
public import StochLean.Probability.Moments.L2

/-! # Terminal energy estimates imply actual L2 Cauchy convergence

Native Hilbert-space Cauchy--Schwarz bounds the supplied terminal energy
estimate. Uniform second moments and vanishing error second moments then
give a Cauchy sequence in the native `Lp` space. The existing completeness
interface constructs an actual L2 limiting random variable.

This criterion does not assert that any particular approximation satisfies
the energy premise. Nonnegativity of the error variables is unnecessary
once that premise has been established. The ambient measure may be arbitrary.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology InnerProductSpace

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {U W : ℕ → Ω → ℝ} {C : ℝ}

private theorem norm_toLp_two_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow,
    sq_eLpNorm_two_eq_ofReal_integral_sq hf.integrable_sq,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]

private theorem integral_mul_eq_inner_toLp {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, f ω * g ω ∂P) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  rw [Real.inner_apply, hfω, hgω]

/-- Quantitative native L2 distance bound obtained from the actual energy
premise by Hilbert-space Cauchy--Schwarz. The constant `C + 1` avoids any
nonzero-energy or square-root denominator side condition. -/
theorem norm_toLp_sub_sq_le_of_terminal_energy
    (hU : ∀ n, MemLp (U n) 2 P) (hW : ∀ n, MemLp (W n) 2 P)
    (hbound : ∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ C)
    {n m : ℕ}
    (he : (∫ ω, (U n ω - U m ω) ^ 2 ∂P) ≤
      2 * ∫ ω, (W n ω + W m ω) * (U n ω + U m ω) ∂P) :
    ‖(hU n).toLp (U n) - (hU m).toLp (U m)‖ ^ 2 ≤
      4 * (C + 1) * (‖(hW n).toLp (W n)‖ + ‖(hW m).toLp (W m)‖) := by
  have hC : 0 ≤ C := (integral_nonneg fun ω ↦ sq_nonneg (U 0 ω)).trans (hbound 0)
  have hu (k : ℕ) : ‖(hU k).toLp (U k)‖ ≤ C + 1 := by
    have hs := (norm_toLp_two_sq (hU k)).trans_le (hbound k)
    nlinarith [sq_nonneg (‖(hU k).toLp (U k)‖ - 1)]
  have henergy : ‖(hU n).toLp (U n) - (hU m).toLp (U m)‖ ^ 2 ≤
      2 * inner ℝ ((hW n).toLp (W n) + (hW m).toLp (W m))
        ((hU n).toLp (U n) + (hU m).toLp (U m)) := by
    rw [← MemLp.toLp_sub (hU n) (hU m), norm_toLp_two_sq]
    have hprod := integral_mul_eq_inner_toLp ((hW n).add (hW m)) ((hU n).add (hU m))
    rw [MemLp.toLp_add (hW n) (hW m), MemLp.toLp_add (hU n) (hU m)] at hprod
    exact he.trans_eq (congrArg (fun x : ℝ ↦ 2 * x) hprod)
  have hsumU := (norm_add_le ((hU n).toLp (U n)) ((hU m).toLp (U m))).trans
    (add_le_add (hu n) (hu m))
  calc
    _ ≤ 2 * inner ℝ ((hW n).toLp (W n) + (hW m).toLp (W m))
        ((hU n).toLp (U n) + (hU m).toLp (U m)) := henergy
    _ ≤ 2 * (‖(hW n).toLp (W n) + (hW m).toLp (W m)‖ *
        ‖(hU n).toLp (U n) + (hU m).toLp (U m)‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by norm_num)
    _ ≤ 2 * ((‖(hW n).toLp (W n)‖ + ‖(hW m).toLp (W m)‖) * ((C + 1) + (C + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul (norm_add_le _ _) hsumU (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- Ordered-pair terminal energy estimates and vanishing error second moments
give a genuine Cauchy sequence of the original random variables in native L2. -/
theorem cauchySeq_toLp_two_of_terminal_energy
    (hU : ∀ n, MemLp (U n) 2 P) (hW : ∀ n, MemLp (W n) 2 P)
    (hbound : ∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ C)
    (hsmall : Tendsto (fun n ↦ ∫ ω, W n ω ^ 2 ∂P) atTop (𝓝 0))
    (he : ∀ n m, n ≤ m → (∫ ω, (U n ω - U m ω) ^ 2 ∂P) ≤
      2 * ∫ ω, (W n ω + W m ω) * (U n ω + U m ω) ∂P) :
    CauchySeq (fun n ↦ (hU n).toLp (U n)) := by
  have hnormW : Tendsto (fun n ↦ ‖(hW n).toLp (W n)‖) atTop (𝓝 0) := by
    have heq (n : ℕ) : Real.sqrt (∫ ω, W n ω ^ 2 ∂P) = ‖(hW n).toLp (W n)‖ := by
      rw [← norm_toLp_two_sq (hW n), Real.sqrt_sq (norm_nonneg _)]
    simpa only [Function.comp_def, heq, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsmall
  have hpair (n m : ℕ) : ‖(hU n).toLp (U n) - (hU m).toLp (U m)‖ ^ 2 ≤
      4 * (C + 1) * (‖(hW n).toLp (W n)‖ + ‖(hW m).toLp (W m)‖) := by
    rcases le_total n m with hnm | hmn
    · exact norm_toLp_sub_sq_le_of_terminal_energy hU hW hbound (he n m hnm)
    · simpa only [norm_sub_rev, add_comm] using
        norm_toLp_sub_sq_le_of_terminal_energy hU hW hbound (he m n hmn)
  have hscaled : Tendsto (fun n ↦ 8 * (C + 1) * ‖(hW n).toLp (W n)‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hnormW.const_mul (8 * (C + 1))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hscaled.eventually (gt_mem_nhds (sq_pos_of_pos hε)))
  refine ⟨N, fun n hn m hm ↦ ?_⟩
  rw [dist_eq_norm]
  have hp := hpair n m
  have hn' := hN n hn
  have hm' := hN m hm
  nlinarith [norm_nonneg ((hU n).toLp (U n) - (hU m).toLp (U m))]

/-- L2 completeness constructs an actual limiting random variable. This
uses the existing canonical `toLp` completeness interface, not a new selector. -/
theorem exists_memLp_two_limit_of_terminal_energy
    (hU : ∀ n, MemLp (U n) 2 P) (hW : ∀ n, MemLp (W n) 2 P)
    (hbound : ∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ C)
    (hsmall : Tendsto (fun n ↦ ∫ ω, W n ω ^ 2 ∂P) atTop (𝓝 0))
    (he : ∀ n m, n ≤ m → (∫ ω, (U n ω - U m ω) ^ 2 ∂P) ≤
      2 * ∫ ω, (W n ω + W m ω) * (U n ω + U m ω) ∂P) :
    ∃ A : Ω → ℝ, MemLp A 2 P ∧
      Tendsto (fun n ↦ eLpNorm (U n - A) 2 P) atTop (𝓝 0) :=
  (exists_memLp_tendsto_eLpNorm_iff_cauchySeq_toLp hU).mpr
    (cauchySeq_toLp_two_of_terminal_energy hU hW hbound hsmall he)

end MeasureTheory

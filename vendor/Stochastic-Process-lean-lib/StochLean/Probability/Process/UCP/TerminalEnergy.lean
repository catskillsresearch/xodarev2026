/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Cauchy
public import StochLean.Probability.Moments.L2

/-! # From terminal L2 maximal estimates to native UCP-Cauchy convergence

Native L2 Cauchy convergence makes the terminal difference energies uniformly
small on pairs of late indices. Vanishing error energies and the elementary
square-of-a-sum bound handle the second term of the supplied maximal estimate.
This proves the existing `CauchyUCP` predicate for the actual processes.

No measurability or regularity assumption on the processes is hidden in the
argument: the strict-deviation events use the ambient outer measure. Finite
ambient measure justifies conversion from real outer probabilities, with an
explicit separate case for an infinite target probability tolerance.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {U W : ℕ → Ω → ℝ} {Y : ℕ → ℝ≥0 → Ω → ℝ}

private theorem integral_sq_sub_eq_dist_toLp_sq {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, (f ω - g ω) ^ 2 ∂P) = dist (hf.toLp f) (hg.toLp g) ^ 2 := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, Lp.norm_toLp, ← ENNReal.toReal_pow,
    sq_eLpNorm_two_eq_ofReal_integral_sq (hf.sub hg).integrable_sq,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]
  rfl

private theorem integral_sq_add_le_twice {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, (f ω + g ω) ^ 2 ∂P) ≤
      2 * ((∫ ω, f ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂P) := by
  calc
    _ ≤ ∫ ω, 2 * (f ω ^ 2 + g ω ^ 2) ∂P := by
      apply integral_mono_ae (hf.add hg).integrable_sq
        ((hf.integrable_sq.add hg.integrable_sq).const_mul 2)
      apply Eventually.of_forall
      intro ω
      change (f ω + g ω) ^ 2 ≤ 2 * (f ω ^ 2 + g ω ^ 2)
      nlinarith [sq_nonneg (f ω - g ω)]
    _ = _ := by
      rw [integral_const_mul, integral_add hf.integrable_sq hg.integrable_sq]

/-- A genuine maximal inequality and native terminal L2 Cauchy convergence
imply UCP-Cauchy convergence. The maximal estimate is the mathematical premise
to be instantiated; no UCP or process-regularity conclusion is assumed. -/
theorem cauchyUCP_of_terminal_L2_maximal [IsFiniteMeasure P]
    (hU : ∀ n, MemLp (U n) 2 P) (hW : ∀ n, MemLp (W n) 2 P)
    (hc : CauchySeq (fun n ↦ (hU n).toLp (U n)))
    (hw : Tendsto (fun n ↦ ∫ ω, W n ω ^ 2 ∂P) atTop (𝓝 0))
    (hmax : ∀ T : ℝ≥0, ∀ a : ℝ, 0 < a → ∀ n m : ℕ,
      P.real {ω | ∃ t ≤ T, a < ‖Y n t ω - Y m t ω‖} ≤
        8 * ((∫ ω, (U n ω - U m ω) ^ 2 ∂P) +
          ∫ ω, (W n ω + W m ω) ^ 2 ∂P) / a ^ 2) :
    CauchyUCP P Y := by
  intro T a ha η hη
  by_cases htop : η = ∞
  · subst η
    exact ⟨0, fun _ _ _ _ ↦ le_top⟩
  have hηreal : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  let ρ : ℝ := η.toReal * a ^ 2 / 64
  have hρ : 0 < ρ := div_pos (mul_pos hηreal (sq_pos_of_pos ha)) (by norm_num)
  have hρeq : 64 * ρ = η.toReal * a ^ 2 := by
    dsimp [ρ]
    ring
  obtain ⟨NU, hNU⟩ := Metric.cauchySeq_iff.mp hc (Real.sqrt ρ) (Real.sqrt_pos.mpr hρ)
  obtain ⟨NW, hNW⟩ := eventually_atTop.mp (hw.eventually (gt_mem_nhds hρ))
  refine ⟨max NU NW, fun n m hn hm ↦ ?_⟩
  have hdist := hNU n ((le_max_left _ _).trans hn) m ((le_max_left _ _).trans hm)
  have hdiff : (∫ ω, (U n ω - U m ω) ^ 2 ∂P) ≤ ρ := by
    rw [integral_sq_sub_eq_dist_toLp_sq (hU n) (hU m)]
    have hsqrt := Real.sq_sqrt hρ.le
    have hd0 : 0 ≤ dist ((hU n).toLp (U n)) ((hU m).toLp (U m)) := dist_nonneg
    nlinarith
  have hwn := hNW n ((le_max_right _ _).trans hn)
  have hwm := hNW m ((le_max_right _ _).trans hm)
  have hsum : (∫ ω, (W n ω + W m ω) ^ 2 ∂P) ≤ 4 * ρ := by
    have h := integral_sq_add_le_twice (hW n) (hW m)
    linarith
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) htop).mp
  change P.real {ω | ∃ t ≤ T, a < ‖Y n t ω - Y m t ω‖} ≤ η.toReal
  apply (hmax T a ha n m).trans
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith

end ProbabilityTheory

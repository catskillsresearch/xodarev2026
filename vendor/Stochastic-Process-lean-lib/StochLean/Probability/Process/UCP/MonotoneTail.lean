/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Cauchy
public import StochLean.Probability.Process.Path.Monotone
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # UCP-Cauchy convergence from monotone differences and mean tails

An increasing zero-initial difference attains its largest absolute value on
a compact interval at its right endpoint. Markov's inequality therefore
turns vanishing mean tails into the native UCP-Cauchy property. All path
comparisons take place on common full-measure events; the deviation events
are evaluated by outer measure and need not be measurable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → ℝ≥0 → Ω → ℝ} {e : ℕ → ℝ}

/-- Mean control of ordered increasing differences gives a compact maximal
bound, without requiring the compact deviation event to be measurable. -/
theorem measureReal_ucp_deviation_le_of_monotone_sub
    {n m : ℕ} (hm : HasMonotonePaths (A m - A n) P)
    (hn0 : A n 0 =ᵐ[P] 0) (hm0 : A m 0 =ᵐ[P] 0)
    (T : ℝ≥0) (hi : Integrable ((A m - A n) T) P) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ t ≤ T, a < ‖A m t ω - A n t ω‖} ≤
      (∫ ω, (A m - A n) T ω ∂P) / a := by
  have hn : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ (A m - A n) t ω := by
    filter_upwards [hm, hn0, hm0] with ω hmω hnω hm0ω t
    have h := hmω (show (0 : ℝ≥0) ≤ t from bot_le)
    change A m 0 ω - A n 0 ω ≤ (A m - A n) t ω at h
    simpa only [hnω, hm0ω, sub_self] using h
  have hset : P {ω | ∃ t ≤ T, a < ‖A m t ω - A n t ω‖} ≤
      P {ω | a ≤ (A m - A n) T ω} := by
    apply measure_mono_ae
    filter_upwards [hm, hn] with ω hmω hnω
    rintro ⟨t, ht, hgt⟩
    have hnorm : ‖A m t ω - A n t ω‖ = (A m - A n) t ω :=
      Real.norm_of_nonneg (hnω t)
    rw [hnorm] at hgt
    exact hgt.le.trans (hmω ht)
  have hreal := ENNReal.toReal_mono (measure_ne_top P _) hset
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (hn.mono fun _ hω ↦ hω T) hi a
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ P.real {ω | a ≤ (A m - A n) T ω} * a :=
      mul_le_mul_of_nonneg_right hreal ha.le
    _ ≤ _ := by simpa only [mul_comm] using hmarkov

/-- Ordered increasing differences, zero initial values and a vanishing
expectation tail imply UCP-Cauchy convergence. No terminal process or limit
random variable is supplied. -/
theorem cauchyUCP_of_monotone_sub_integral_tail
    (hm : ∀ n m : ℕ, n ≤ m → HasMonotonePaths (A m - A n) P)
    (h0 : ∀ n, A n 0 =ᵐ[P] 0) (hi : ∀ n t, Integrable (A n t) P)
    (htail : Tendsto e atTop (𝓝 0))
    (he : ∀ n m : ℕ, n ≤ m → ∀ t : ℝ≥0,
      (∫ ω, (A m - A n) t ω ∂P) ≤ e n) : CauchyUCP P A := by
  intro T a ha η hη
  by_cases htop : η = ∞
  · subst η
    exact ⟨0, fun _ _ _ _ ↦ le_top⟩
  have hηreal : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (mul_pos hηreal ha)))
  have hmax (n m : ℕ) (hnm : n ≤ m) :
      P.real {ω | ∃ t ≤ T, a < ‖A m t ω - A n t ω‖} ≤ e n / a :=
    (measureReal_ucp_deviation_le_of_monotone_sub (hm n m hnm) (h0 n) (h0 m)
      T ((hi m T).sub (hi n T)) ha).trans
      (div_le_div_of_nonneg_right (he n m hnm T) ha.le)
  refine ⟨N, fun m n hmN hnN ↦ ?_⟩
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) htop).mp
  change P.real {ω | ∃ t ≤ T, a < ‖A m t ω - A n t ω‖} ≤ η.toReal
  rcases le_total n m with hnm | hmn
  · exact (hmax n m hnm).trans ((div_le_iff₀ ha).mpr (hN n hnN).le)
  · have hswap : P.real {ω | ∃ t ≤ T, a < ‖A m t ω - A n t ω‖} ≤ e m / a := by
      simpa only [norm_sub_rev] using hmax m n hmn
    exact hswap.trans ((div_le_iff₀ ha).mpr (hN m hmN).le)

end ProbabilityTheory

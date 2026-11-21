/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Measure.RNDensityVanishing
public import StochLean.ForMathlib.MeasureTheory.Measure.RightWindowDerivative

/-! # Vanishing under actual right-window bounds

A nonnegative rate eventually dominated by every member of a countable
family of actual right-window rates tends to zero at almost every real
time, provided the finite absolutely continuous measures have infimum
total mass zero.

The proof uses one common event for the countably many native RN window
derivatives and the vanishing infimum of their ENNReal densities. At a
fixed time and tolerance, a genuinely small finite RN density supplies
the required window bound. No monotonicity of chosen RN representatives,
measurability of the dominated rate, or target rate limit is assumed.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory.Measure

/-- Actual right-window domination by finite absolutely continuous measures
with vanishing infimum mass forces a nonnegative rate to vanish almost
everywhere in time. -/
theorem ae_tendsto_zero_of_eventually_le_measureReal_Ico_div
    (μ : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (μ n)]
    (hAC : ∀ n, μ n ≪ volume) (hzero : (⨅ n, μ n univ) = 0)
    (r : ℝ → ℝ → ℝ)
    (hnonneg : ∀ t, ∀ᶠ h in 𝓝[>] 0, 0 ≤ r t h)
    (hbound : ∀ n t, ∀ᶠ h in 𝓝[>] 0,
      r t h ≤ (μ n).real (Ico t (t + h)) / h) :
    ∀ᵐ t ∂volume, Tendsto (r t) (𝓝[>] 0) (𝓝 0) := by
  have hwindow : ∀ᵐ t ∂volume, ∀ n,
      Tendsto (fun h : ℝ ↦ (μ n).real (Ico t (t + h)) / h)
        (𝓝[>] 0) (𝓝 (((μ n).rnDeriv volume t).toReal)) :=
    ae_all_iff.mpr fun n ↦ (μ n).ae_tendsto_measureReal_Ico_div (hAC n)
  filter_upwards [hwindow,
    ae_iInf_rnDeriv_eq_zero_of_iInf_mass_eq_zero μ volume hzero] with t ht hz
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hnonneg t] with h hh
    exact ha.trans_le hh
  · intro ε hε
    have hsmall : (⨅ n, (μ n).rnDeriv volume t) < ENNReal.ofReal ε := by
      rw [hz]
      exact ENNReal.ofReal_pos.mpr hε
    obtain ⟨n, hn⟩ := iInf_lt_iff.mp hsmall
    have hreal : ((μ n).rnDeriv volume t).toReal < ε :=
      ENNReal.toReal_lt_of_lt_ofReal hn
    filter_upwards [hbound n t, (ht n).eventually_lt_const hreal] with h hb hl
    exact hb.trans_lt hl

end MeasureTheory.Measure

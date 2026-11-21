/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.L2
public import StochLean.Probability.Process.Path.Stopping

/-! # Square-integrable martingales are source semimartingales

The good-integrator property is proved from the elementary L2 estimate and Markov's
inequality, not assumed as part of a martingale definition or inferred from a decomposition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

/-- A quantitative square-integral bound supplies the source continuity criterion. -/
theorem isGoodIntegrator_of_elementaryIntegral_l2_estimate (K : ℝ)
    (hbound : ∀ C : ℝ≥0, ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      (∀ t ω, ‖H t ω‖ ≤ C) →
        Integrable (fun ω ↦ (hH.elementaryIntegral X ω) ^ 2) P ∧
          (∫ ω, (hH.elementaryIntegral X ω) ^ 2 ∂P) ≤ (C : ℝ) ^ 2 * K) :
    IsGoodIntegrator X F P := by
  apply isGoodIntegrator_iff_continuousAtZero.mpr
  intro ε hε η hη
  have hlim : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ 2 * K / ε ^ 2)) atTop (𝓝 0) := by
    have hr := ((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const K).div_const (ε ^ 2)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div,
      ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hη).exists
  let C : ℝ≥0 := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  refine ⟨(C : ℝ), (show 0 < (1 / ((n : ℝ) + 1)) from one_div_pos.mpr (by positivity)),
    fun H hH hb ↦ ?_⟩
  obtain ⟨hi, he⟩ := hbound C H hH hb
  calc
    _ ≤ ENNReal.ofReal ((∫ ω, (hH.elementaryIntegral X ω) ^ 2 ∂P) / ε ^ 2) :=
      measure_norm_ge_le_integral_sq_div hi hε
    _ ≤ ENNReal.ofReal ((C : ℝ) ^ 2 * K / ε ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right he (sq_nonneg _))
    _ ≤ η := hn.le

variable [SigmaFiniteFiltration P F]

theorem _root_.MeasureTheory.Martingale.isGoodIntegrator_min_const_of_memLp
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) :
    IsGoodIntegrator (fun t ↦ X (min t T)) F P := by
  apply isGoodIntegrator_of_elementaryIntegral_l2_estimate (∫ ω, (X T ω) ^ 2 ∂P)
  intro C H hH hb
  exact ⟨(hH.memLp_elementaryIntegral_min_const hX hF hr T hXT C hb).integrable_sq,
    hH.integral_sq_elementaryIntegral_min_const_le hX hF hr T hXT C hb⟩

theorem _root_.MeasureTheory.Martingale.isTotalSemimartingale_min_const_of_memLp
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) :
    IsTotalSemimartingale (fun t ↦ X (min t T)) F P :=
  ⟨(hX.min_const T).stronglyAdapted.adapted, hc.mono (fun _ h ↦ h.min_const T),
    hX.isGoodIntegrator_min_const_of_memLp hF hc.hasRightContinuousPaths T hXT⟩

/-- Finite-time L2 integrability suffices; no uniform half-line L2 bound is imposed. -/
theorem _root_.MeasureTheory.Martingale.isSemimartingale_of_memLp
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hlp : ∀ T, MemLp (X T) 2 P) : IsSemimartingale X F P := by
  intro T
  change IsTotalSemimartingale (stoppedProcess X (FiniteStoppingTime.const F T).withTop) F P
  rw [FiniteStoppingTime.stoppedProcess_eq]
  exact hX.isTotalSemimartingale_min_const_of_memLp hF hc T (hlp T)

end ProbabilityTheory

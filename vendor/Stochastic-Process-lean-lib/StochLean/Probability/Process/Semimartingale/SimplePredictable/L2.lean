/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Sampling
public import StochLean.Probability.Martingale.DiscreteIntegral.InitialL2
public import StochLean.Probability.Moments.L2

/-! # The source elementary-integral L2 estimate

For a martingale stopped at a finite deterministic horizon `T`, a uniform process bound `C`
on a simple predictable integrand gives `E[(H · X^T)^2] ≤ C^2 E[X_T^2]`. The source initial
term is retained, random endpoints are not bounded deterministically, and coefficients on
empty intervals are normalized before applying the discrete martingale estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

theorem memLp_integral_min_const_of_coefficients (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hinit : ∀ ω, ‖H.initial ω‖ ≤ C) (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) :
    MemLp (H.integral (fun t ↦ X (min t T))) 2 P := by
  let M := H.partition.sampledProcess (fun t ↦ X (min t T))
  have hlp : ∀ n, MemLp (M n) 2 P :=
    H.partition.memLp_sampledProcess_min_const hX hF hr T (by norm_num) hXT
  have htop : MemLp H.initial ∞ P := memLp_top_of_bound
    (H.measurable_initial.mono (F.le 0) le_rfl).aestronglyMeasurable C (ae_of_all _ hinit)
  have hZlp : MemLp (fun ω ↦ H.initial ω * X 0 ω) 2 P := by
    simpa only [M, StoppingTimePartition.sampledProcess_zero, zero_min] using (hlp 0).mul' htop
  rw [H.integral_eq_initial_add_discreteStochasticIntegral]
  simp only [zero_min]
  exact hZlp.add
    (memLp_discreteStochasticIntegral hlp H.stronglyPredictable_discreteCoefficient
      (fun n ↦ ⟨C, ae_of_all _ (H.norm_discreteCoefficient_le C.coe_nonneg hb n)⟩) H.partition.size)

theorem integral_sq_integral_min_const_le_of_coefficients (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hinit : ∀ ω, ‖H.initial ω‖ ≤ C) (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) :
    ∫ ω, (H.integral (fun t ↦ X (min t T)) ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (X T ω) ^ 2 ∂P := by
  let M := H.partition.sampledProcess (fun t ↦ X (min t T))
  have hM : Martingale M H.partition.sampledFiltration P :=
    H.partition.martingale_sampledProcess_min_const hX hF hr T
  have hlp : ∀ n, MemLp (M n) 2 P :=
    H.partition.memLp_sampledProcess_min_const hX hF hr T (by norm_num) hXT
  let Z : Ω → ℝ := fun ω ↦ H.initial ω * M 0 ω
  have hZ : StronglyMeasurable[H.partition.sampledFiltration 0] Z :=
    (H.measurable_initial.mono (H.partition.zero_le_sampledFiltration 0) le_rfl).stronglyMeasurable.mul
      (hM.stronglyMeasurable 0)
  have htop : MemLp H.initial ∞ P := memLp_top_of_bound
    (H.measurable_initial.mono (F.le 0) le_rfl).aestronglyMeasurable C (ae_of_all _ hinit)
  have hZlp : MemLp Z 2 P := (hlp 0).mul' htop
  have hZb : ∀ᵐ ω ∂P, (Z ω) ^ 2 ≤ (C : ℝ) ^ 2 * (M 0 ω) ^ 2 := by
    apply ae_of_all
    intro ω
    dsimp only [Z]
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (H.initial ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hinit ω) 2
  have hi := hM.integral_sq_initial_add_discreteStochasticIntegral_le hlp
    H.stronglyPredictable_discreteCoefficient C
    (fun n ↦ ae_of_all _ (H.norm_discreteCoefficient_le C.coe_nonneg hb n)) hZ hZlp hZb
    H.partition.size
  have hterminal : (∫ ω, (M H.partition.size ω) ^ 2 ∂P) ≤ ∫ ω, (X T ω) ^ 2 ∂P := by
    apply integral_sq_le_of_eLpNorm_two_le (hlp _) hXT
    exact hX.eLpNorm_finiteStoppingTime_min_le hF hr (H.partition.pointNat H.partition.size)
      T (by norm_num)
  have hrewrite : H.integral (fun t ↦ X (min t T)) = fun ω ↦ Z ω +
      discreteStochasticIntegral H.discreteCoefficient M H.partition.size ω := by
    rw [H.integral_eq_initial_add_discreteStochasticIntegral]
    simp only [Z, M, StoppingTimePartition.sampledProcess_zero, zero_min]
  rw [hrewrite]
  exact hi.trans (mul_le_mul_of_nonneg_left hterminal (sq_nonneg _))

theorem memLp_integral_min_const (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) :
    MemLp (H.integral (fun t ↦ X (min t T))) 2 P := by
  rw [← H.integral_removeEmptyIntervals]
  exact H.removeEmptyIntervals.memLp_integral_min_const_of_coefficients hX hF hr T hXT C
    (fun ω ↦ by
      change ‖H.initial ω‖ ≤ (C : ℝ)
      simpa only [toProcess_zero] using hb 0 ω)
    (H.norm_coefficient_removeEmptyIntervals_le C.coe_nonneg hb)

theorem integral_sq_integral_min_const_le (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) :
    ∫ ω, (H.integral (fun t ↦ X (min t T)) ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (X T ω) ^ 2 ∂P := by
  rw [← H.integral_removeEmptyIntervals]
  exact H.removeEmptyIntervals.integral_sq_integral_min_const_le_of_coefficients hX hF hr T hXT C
    (fun ω ↦ by
      change ‖H.initial ω‖ ≤ (C : ℝ)
      simpa only [toProcess_zero] using hb 0 ω)
    (H.norm_coefficient_removeEmptyIntervals_le C.coe_nonneg hb)

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem memLp_elementaryIntegral_min_const (hH : IsSimplePredictable H F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    MemLp (hH.elementaryIntegral (fun t ↦ X (min t T))) 2 P :=
  hH.choose.memLp_integral_min_const hX hF hr T hXT C (by simpa only [hH.choose_spec] using hb)

theorem integral_sq_elementaryIntegral_min_const_le (hH : IsSimplePredictable H F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    ∫ ω, (hH.elementaryIntegral (fun t ↦ X (min t T)) ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (X T ω) ^ 2 ∂P :=
  hH.choose.integral_sq_integral_min_const_le hX hF hr T hXT C
    (by simpa only [hH.choose_spec] using hb)

theorem eLpNorm_elementaryIntegral_min_const_le (hH : IsSimplePredictable H F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    eLpNorm (hH.elementaryIntegral (fun t ↦ X (min t T))) 2 P ≤ C * eLpNorm (X T) 2 P :=
  eLpNorm_two_le_mul_of_integral_sq_le
    (hH.memLp_elementaryIntegral_min_const hX hF hr T hXT C hb) hXT C
    (hH.integral_sq_elementaryIntegral_min_const_le hX hF hr T hXT C hb)

end IsSimplePredictable
end ProbabilityTheory

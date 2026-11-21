/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale
public import StochLean.Probability.Process.Stopping.Finite
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Martingales are locally uniformly integrable

Protter I.6 Example 1 and Klenke 21.69(i). Stopping at deterministic time T
closes the martingale with the terminal variable X_T. Thus it is UI even when
the original martingale is not UI over the whole half-line. No continuous-time
optional sampling or integrability of an unbounded stopping value is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.MeasureTheory.Martingale.condExp_terminal_ae_eq_min
    [SigmaFiniteFiltration P F] (hX : Martingale X F P) (T t : ℝ≥0) :
    P[X T | F t] =ᵐ[P] X (min t T) := by
  by_cases ht : t ≤ T
  · simpa only [min_eq_left ht] using hX.condExp_ae_eq ht
  · have hTt : T ≤ t := le_of_not_ge ht
    rw [min_eq_right hTt, condExp_of_stronglyMeasurable (F.le t)
      ((hX.stronglyAdapted T).mono (F.mono hTt)) (hX.integrable T)]

theorem _root_.MeasureTheory.Martingale.min_const [SigmaFiniteFiltration P F]
    (hX : Martingale X F P) (T : ℝ≥0) :
    Martingale (fun t ↦ X (min t T)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted _).mono (F.mono (min_le_left t T)), ?_⟩
  intro s t hst
  change P[X (min t T) | F s] =ᵐ[P] X (min s T)
  by_cases hs : s ≤ T
  · simpa only [min_eq_left hs] using hX.condExp_ae_eq (le_min hst hs)
  · have hTs : T ≤ s := le_of_not_ge hs
    have hTt := hTs.trans hst
    rw [min_eq_right hTs, min_eq_right hTt,
      condExp_of_stronglyMeasurable (F.le s)
        ((hX.stronglyAdapted T).mono (F.mono hTs)) (hX.integrable T)]

theorem _root_.MeasureTheory.Martingale.isUIMartingale_min_const
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P) (T : ℝ≥0) :
    IsUIMartingale (fun t ↦ X (min t T)) F P :=
  ⟨hX.min_const T, ((hX.integrable T).uniformIntegrable_condExp F.le).ae_eq
    (fun t ↦ hX.condExp_terminal_ae_eq_min T t)⟩

theorem _root_.MeasureTheory.Martingale.isReducingStoppingTime_const
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P) (T : ℝ≥0) :
    IsReducingStoppingTime X F P (fun _ ↦ (T : WithTop ℝ≥0)) := by
  refine ⟨isStoppingTime_const F T, ?_⟩
  change IsUIMartingale (stoppedProcess X (FiniteStoppingTime.const F T).withTop) F P
  rw [FiniteStoppingTime.stoppedProcess_eq]
  exact hX.isUIMartingale_min_const T

/-- The natural deterministic sequence supplies an actual source-localizing witness. -/
theorem _root_.MeasureTheory.Martingale.isKlenkeLocalizingSequence_nat
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P) :
    IsKlenkeLocalizingSequence X F P (fun n _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) := by
  refine ⟨⟨fun n ↦ isStoppingTime_const F n, ?_⟩, ?_, fun n ↦
    (hX.isReducingStoppingTime_const n).2⟩
  · exact ae_of_all _ fun _ ↦ WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
  · intro n m hnm ω
    exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm)

theorem _root_.MeasureTheory.Martingale.isLocalMartingale
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P)
    (hcad : HasCadlagPaths X P) : IsLocalMartingale X F P :=
  hX.isKlenkeLocalizingSequence_nat.isLocalMartingale hX.stronglyAdapted.adapted hcad

theorem _root_.MeasureTheory.Martingale.isContinuousLocalMartingale
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P)
    (hcont : HasContinuousPaths X P) : IsContinuousLocalMartingale X F P :=
  ⟨hX.isLocalMartingale hcont.hasCadlagPaths, hcont⟩

end ProbabilityTheory

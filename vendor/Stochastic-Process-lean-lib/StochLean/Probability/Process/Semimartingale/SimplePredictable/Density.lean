/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.ZeroPathApproximation
public import StochLean.Probability.Process.Stopping.LocalizingTail
public import StochLean.Probability.Process.UCP.DeviationEvents
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Source simple predictable density in the caglad UCP class

Protter II.10 with the first interval restored. Actual oscillation times of the
right-limit process and finite capped coefficients give the approximants. Their
number of cells is chosen from the proved vanishing exit probabilities. The source
allows unbounded finite coefficients, so no preliminary global coefficient bound
is imposed. No density assumption or general stochastic-integral selector is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}

/-- Actual source approximants are UCP dense and retain every zero input path.
The pathwise property does not require a measurable or full-probability zero event. -/
theorem exists_simplePredictable_tendstoUCP_preserves_zero_paths
    (ha : Adapted F H) (hF : F.IsUsual P)
    (hc : HasCagladPaths H P) :
    ∃ S : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, IsSimplePredictable (S n) F) ∧
      (∀ n ω, (∀ t, H t ω = 0) → ∀ t, S n t ω = 0) ∧ TendstoUCP P S atTop H := by
  classical
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hplim : Tendsto (fun k ↦ ENNReal.ofReal (ε k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hεlim
  have hτ (k n : ℕ) : IsStoppingTime F (oscillationTimes (rightLimitProcess H) (ε k) n) :=
    isStoppingTime_oscillationTimes (ha.rightLimitProcess_of_usual hF hc) hF
      hc.hasCadlagPaths_rightLimitProcess.hasRightContinuousPaths (ε k) n
  have hex (k : ℕ) : ∃ n : ℕ,
      P {ω | oscillationTimes (rightLimitProcess H) (ε k) n ω ≤ (k : WithTop ℝ≥0)} ≤
        ENNReal.ofReal (ε k) := by
    have hlim := tendsto_measure_le_of_ae_tendsto_top
      (fun n ↦ (hτ k n).measurable.mono (hτ k n).measurableSpace_le le_rfl)
      (ae_tendsto_top_oscillationTimes hc.hasCadlagPaths_rightLimitProcess (hε k)) (k : ℝ≥0)
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hlim
      (ENNReal.ofReal (ε k)) (ENNReal.ofReal_pos.mpr (hε k))
    exact ⟨N, hN N le_rfl⟩
  choose N hN using hex
  let R (k : ℕ) := CagladApproximation.representation H ha hF hc (ε k) (hε k).le (N k) k
  refine ⟨fun k ↦ (R k).toProcess, fun k ↦ ⟨R k, rfl⟩, ?_, ?_⟩
  · intro k ω hzero t
    exact CagladApproximation.toProcess_eq_zero_of_zero_path H ha hF hc
      (ε k) (hε k).le (N k) k hzero t
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T δ hδ
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hεlim.eventually_lt_const hδ)
  obtain ⟨NP, hNP⟩ := ENNReal.tendsto_atTop_zero.mp hplim η hη
  refine ⟨max NT (max NE NP), fun k hk ↦ ?_⟩
  have hTk : T ≤ (k : ℝ≥0) := hNT.trans (by
    exact_mod_cast (le_max_left NT (max NE NP)).trans hk)
  have hkε : ε k < δ := hNE k ((le_max_left NE NP).trans ((le_max_right NT (max NE NP)).trans hk))
  have hkp : ENNReal.ofReal (ε k) ≤ η :=
    hNP k ((le_max_right NE NP).trans ((le_max_right NT (max NE NP)).trans hk))
  apply le_trans ?_ ((hN k).trans hkp)
  apply measure_mono_ae
  filter_upwards [hc] with ω hω
  rintro ⟨t, ht, hbad⟩
  by_contra hn
  have hτk : (k : WithTop ℝ≥0) < oscillationTimes (rightLimitProcess H) (ε k) (N k) ω :=
    lt_of_not_ge hn
  have hbound := CagladApproximation.norm_toProcess_sub_le H ha hF hc
    (ε k) (hε k).le (N k) k hω (ht.trans hTk)
    ((WithTop.coe_le_coe.mpr (ht.trans hTk)).trans hτk.le)
  exact (not_lt_of_ge hbound) (hkε.trans hbad)

/-- The full simple source class is UCP dense in adapted processes
with common-event caglad paths. -/
theorem exists_simplePredictable_tendstoUCP (ha : Adapted F H) (hF : F.IsUsual P)
    (hc : HasCagladPaths H P) :
    ∃ S : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, IsSimplePredictable (S n) F) ∧ TendstoUCP P S atTop H := by
  obtain ⟨S, hS, _, hu⟩ := exists_simplePredictable_tendstoUCP_preserves_zero_paths ha hF hc
  exact ⟨S, hS, hu⟩

end ProbabilityTheory

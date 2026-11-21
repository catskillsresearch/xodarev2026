/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.DeviationEvents
public import StochLean.Probability.Process.Partition
public import Mathlib.MeasureTheory.Integral.Indicator

/-! # UCP exhaustion by finite stopping endpoints

On each compact interval, stopping eventually changes nothing on almost every
path. Measurable endpoint events bound the possibly nonmeasurable deviation
events, so no regularity or measurability assumption on the process is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

theorem tendstoUCP_min_of_ae_tendsto_atTop {τ : ℕ → Ω → ℝ≥0}
    (hm : ∀ n (T : ℝ≥0), MeasurableSet {ω | τ n ω < T})
    (hτ : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop atTop) (X : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun n t ω ↦ X (min (τ n ω) t) ω) atTop X := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  have hbad : Tendsto (fun n ↦ P {ω | τ n ω < T}) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := P) (As := fun n ↦ {ω | τ n ω < T}) atTop (A := ∅)
      MeasurableSet.empty (fun n ↦ hm n T) (hτ.mono fun ω hω ↦ ?_)
    · simpa only [measure_empty] using h
    · filter_upwards [hω.eventually (eventually_ge_atTop T)] with n hn
      exact iff_of_false (not_lt_of_ge hn) (Set.notMem_empty ω)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  by_contra hn
  have htn : t ≤ τ n ω := ht.trans (le_of_not_gt hn)
  rw [min_eq_right htn, sub_self, norm_zero] at hω
  exact (not_lt_of_ge hε.le) hω

theorem StoppingTimePartition.IsTendingToIdentity.tendstoUCP_min_terminal
    {F : Filtration ℝ≥0 mΩ} {π : ℕ → StoppingTimePartition F}
    (hπ : StoppingTimePartition.IsTendingToIdentity π P) (X : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun n t ω ↦ X (min ((π n).terminal ω) t) ω) atTop X := by
  apply tendstoUCP_min_of_ae_tendsto_atTop _ (hπ.mono fun _ hω ↦ hω.1) X
  intro n T
  have h := ((π n).terminal.isStoppingTime.measurableSet_lt T)
  exact (F.le T) _ (by simpa only [WithTop.coe_lt_coe] using h)

end ProbabilityTheory

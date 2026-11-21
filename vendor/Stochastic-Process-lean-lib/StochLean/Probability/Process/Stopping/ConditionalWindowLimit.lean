/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalWindowUniform
public import StochLean.Probability.Process.Path.RightContinuousSupremum

/-! # Small-window convergence for arbitrary widths tending to zero

Width comparison extends the ordered-sequence estimate to the full right
neighborhood of zero. The statements apply to any right-continuous coordinate
versions, not just a preselected monotone realization.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
  {R : ℝ≥0 → ℝ≥0 → Ω → ℝ}

theorem conditional_window_supremum_measure_mono (hτ : IsStoppingTime F τ)
    (hrR : ∀ δ, HasRightContinuousPaths (R δ) P)
    (heR : ∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) (ν : ℝ≥0) (a : ℝ) :
    Monotone (fun δ ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R δ) ν ω}) := by
  intro δ ε hδε
  have horder := cadlag_conditional_window_ae_le hτ hδε (hrR δ) (hrR ε) (heR δ) (heR ε)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [horder] with ω hω hmem
  exact hmem.trans_le (denseRunningSupremum_mono (fun t _ ↦ hω t))

theorem IsTotallyInaccessibleStoppingTime.tendsto_conditional_window_supremum
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hrR : ∀ δ, HasRightContinuousPaths (R δ) P)
    (heR : ∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) (ν : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R δ) ν ω})
      (𝓝 0) (𝓝 0) := by
  let d : ℕ → ℝ≥0 := fun n ↦ 1 / ((n : ℝ≥0) + 1)
  have hdmono : Antitone d := by
    intro n m hnm
    exact one_div_le_one_div_of_le (by positivity) (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq := hτ.tendsto_conditional_window_supremum_seq hF hdmono hd
    (fun n ↦ hrR (d n)) (fun n ↦ heR (d n)) ν ha
  have hmono := conditional_window_supremum_measure_mono hτ.1 hrR heR ν a
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    exact Eventually.of_forall fun _ ↦ hb.trans_le measureReal_nonneg
  · intro b hb
    obtain ⟨N, hN⟩ := (hseq.eventually_lt_const hb).exists
    have hpos : (0 : ℝ≥0) < d N := by dsimp [d]; positivity
    filter_upwards [Iio_mem_nhds hpos] with δ hδ
    exact (hmono (show δ ≤ d N from le_of_lt hδ)).trans_lt hN

theorem IsTotallyInaccessibleStoppingTime.ae_conditional_window_supremum_ne_top
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hrR : ∀ δ, HasRightContinuousPaths (R δ) P)
    (heR : ∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) (ν δ : ℝ≥0) :
    ∀ᵐ ω ∂P, denseRunningSupremum (R δ) ν ω ≠ ∞ := by
  obtain ⟨Q, _, hcQ, heQ, hbQ⟩ := hτ.1.exists_cadlag_conditional_window hF δ
  have hind := cadlag_conditional_window_unique (hrR δ) hcQ.hasRightContinuousPaths (heR δ) heQ
  filter_upwards [hind, hbQ] with ω hω hb
  apply denseRunningSupremum_ne_top_of_le (K := 1)
  intro t _
  rw [hω t]
  exact (hb t).2.1

theorem IsTotallyInaccessibleStoppingTime.tendstoInMeasure_conditional_window_supremum
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hrR : ∀ δ, HasRightContinuousPaths (R δ) P)
    (heR : ∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) (ν : ℝ≥0) :
    TendstoInMeasure P (fun δ ω ↦ (denseRunningSupremum (R δ) ν ω).toReal) (𝓝 0)
      (fun _ ↦ (0 : ℝ)) :=
  tendstoInMeasure_toReal_denseRunningSupremum_of_ae_ne_top
    (hτ.ae_conditional_window_supremum_ne_top hF hrR heR ν)
    (fun _ ha ↦ hτ.tendsto_conditional_window_supremum hF hrR heR ν ha)

end ProbabilityTheory

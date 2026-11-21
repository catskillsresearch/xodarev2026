/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Finite
public import StochLean.Probability.Process.Path.RightContinuousSupremum
public import Mathlib.MeasureTheory.Integral.Indicator

/-! # Sampling from the left under actual small-window tail bounds

For genuinely finite stopping times approaching a finite target from
below, the actual sampling difference tends to zero in measure if the
post-stopping small-window suprema have a vanishing uniform tail bound.
This is an intermediate quantitative sampling criterion, not an assertion
of such a bound for an arbitrary process or filtration.

For a fixed window, the event that the random time lag exceeds its width
has measure tending to zero. On the complementary event, right continuity
allows the existing dense running supremum to control the actual sampled
increment, including the window endpoint. The union bound then permits
first choosing a sufficiently small window and then a sufficiently late
sampling index. No independence of a random lag, moment condition, bounded
stopping time, monotonicity of the approximating sequence, or value at an
infinite time is used. No coordinate measurability of the process is needed:
both the hypothesis and convergence-in-measure conclusion use outer measures
for arbitrary events. All event measures remain extended real values.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-- A genuine uniform post-stopping window estimate makes finite sampling
differences converge in measure when the sampling times approach their
finite target and lie below it almost surely at each index. The bound is an
intermediate analytic input; applications must derive it from their actual
process laws. -/
theorem tendstoInMeasure_sub_sample_of_small_window_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F)
    (σ : ℕ → FiniteStoppingTime F) (hle : ∀ n, ∀ᵐ ω ∂P, σ n ω ≤ τ ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)))
    (b : ℝ → ℕ → ℝ≥0∞)
    (hb : ∀ ε : ℝ, 0 < ε → Tendsto (b ε) atTop (𝓝 0))
    (hwin : ∀ ε : ℝ, 0 < ε → ∀ n k : ℕ,
      P {ω | ENNReal.ofReal ε < denseRunningSupremum
        (fun u ω ↦ ‖X (σ n ω + u) ω - X (σ n ω) ω‖)
        (1 / ((k : ℝ≥0) + 1)) ω} ≤ b ε k) :
    TendstoInMeasure P (fun n ω ↦ X (τ ω) ω - X (σ n ω) ω) atTop
      (fun _ ↦ (0 : ℝ)) := by
  let δ : ℕ → ℝ≥0 := fun k ↦ 1 / ((k : ℝ≥0) + 1)
  have hδpos (k : ℕ) : 0 < δ k := by dsimp only [δ]; positivity
  have hmτ : Measurable τ :=
    (τ.isStoppingTime.measurable.untopD 0).mono τ.measurableSpace_le le_rfl
  have hmσ (n : ℕ) : Measurable (σ n) :=
    ((σ n).isStoppingTime.measurable.untopD 0).mono (σ n).measurableSpace_le le_rfl
  let E : ℕ → ℕ → Set Ω := fun n k ↦ {ω | δ k < τ ω - σ n ω}
  have hmE (n k : ℕ) : MeasurableSet (E n k) :=
    measurableSet_lt measurable_const (hmτ.sub (hmσ n))
  have hgap (k : ℕ) : Tendsto (fun n ↦ P (E n k)) atTop (𝓝 0) := by
    have he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n k ↔ ω ∈ (∅ : Set Ω) := by
      filter_upwards [hlim] with ω hω
      have hdiff : Tendsto (fun n ↦ τ ω - σ n ω) atTop (𝓝 0) := by
        simpa only [tsub_self] using
          (tendsto_const_nhds.sub hω :
            Tendsto (fun n : ℕ ↦ τ ω - σ n ω) atTop (𝓝 (τ ω - τ ω)))
      filter_upwards [hdiff.eventually_lt_const (hδpos k)] with n hn
      exact iff_of_false (not_lt_of_ge hn.le) (notMem_empty ω)
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        (μ := P) (As := fun n ↦ E n k) atTop (A := ∅)
        MeasurableSet.empty (fun n ↦ hmE n k) he
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  simp only [sub_zero]
  let W : ℕ → ℕ → Set Ω := fun n k ↦
    {ω | ENNReal.ofReal (ε / 2) < denseRunningSupremum
      (fun u ω ↦ ‖X (σ n ω + u) ω - X (σ n ω) ω‖) (δ k) ω}
  have hbound (n k : ℕ) :
      P {ω | ε ≤ ‖X (τ ω) ω - X (σ n ω) ω‖} ≤ P (E n k) + b (ε / 2) k := by
    have hsub : ∀ᵐ ω ∂P, ε ≤ ‖X (τ ω) ω - X (σ n ω) ω‖ →
        ω ∈ E n k ∪ W n k := by
      filter_upwards [hr, hle n] with ω hω hστ hnorm
      by_cases he : ω ∈ E n k
      · exact Or.inl he
      · apply Or.inr
        have hsmall : τ ω - σ n ω ≤ δ k := le_of_not_gt he
        have hshift : IsRightContinuousPath
            (fun u ↦ ‖X (σ n ω + u) ω - X (σ n ω) ω‖) := by
          intro u
          have hadd : ContinuousWithinAt (fun v : ℝ≥0 ↦ σ n ω + v) (Ici u) u :=
            (continuous_const.add continuous_id).continuousWithinAt
          exact (((hω (σ n ω + u)).comp hadd
            (fun v hv ↦ show σ n ω + u ≤ σ n ω + v from
              add_le_add_right (show u ≤ v from hv) _)).sub
            continuousWithinAt_const).norm
        have hsup := ofReal_le_denseRunningSupremum_of_rightContinuous
          (X := fun u v ↦ ‖X (σ n v + u) v - X (σ n v) v‖) hsmall hshift
        have ht : σ n ω + (τ ω - σ n ω) = τ ω := add_tsub_cancel_of_le hστ
        rw [ht] at hsup
        exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (half_pos hε).le).mpr
          ((half_lt_self hε).trans_le hnorm)).trans_le hsup
    calc
      P {ω | ε ≤ ‖X (τ ω) ω - X (σ n ω) ω‖} ≤ P (E n k ∪ W n k) :=
        measure_mono_ae hsub
      _ ≤ P (E n k) + P (W n k) := measure_union_le _ _
      _ ≤ P (E n k) + b (ε / 2) k :=
        add_le_add_right (hwin (ε / 2) (half_pos hε) n k) _
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  have hηhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨k, hk⟩ := ENNReal.tendsto_atTop_zero.mp (hb (ε / 2) (half_pos hε))
    (η / 2) hηhalf
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp (hgap k) (η / 2) hηhalf
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    P {ω | ε ≤ ‖X (τ ω) ω - X (σ n ω) ω‖} ≤ P (E n k) + b (ε / 2) k := hbound n k
    _ ≤ η / 2 + η / 2 := add_le_add (hN n hn) (hk k le_rfl)
    _ = η := ENNReal.add_halves η

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoringWindow
public import StochLean.Probability.Process.Counting.CensoringWedgeRate
public import StochLean.Probability.Process.Counting.LifetimeRealWindow

/-! # The actual crude censored-window rate almost everywhere

The crude window retains paths censored strictly before their arrival inside
the window. Its exact decomposition is the true arrival-cause window plus
this triangular error. The latter has zero rate almost everywhere, while
the actual finite cause law has its native RN right-window derivative.

Absolute continuity is assumed only for the original real arrival-coordinate
law. It implies absolute continuity of the true cause law and rules out the
infinite lifetime atom before converting finite lifetime windows to real
windows. No independence, regularity of the censoring law, pointwise density
continuity, or desired rate limit is an input.

The displayed real quotient is totalized even at zero joint survival. Only
at strictly positive joint survival does it represent a conditional rate.
The assertion is almost everywhere in nonnegative time, not at every time;
in particular it does not identify crude and cause-window rates pointwise
at an arbitrary censoring atom.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- The true crude arrival window divided by joint survival and window width
has almost everywhere the cause-law RN density divided by the same survival.
Zero-survival quotients are only real totalized expressions, not conditional
probabilities. -/
theorem ae_tendsto_censored_crude_window_rate
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {T U : Ω → WithTop ℝ≥0} (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    let κreal : Measure ℝ :=
      (P.restrict {ω | T ω ≤ U ω}).map (fun ω ↦ ((T ω).untopA : ℝ))
    let S : ℝ → ℝ := fun t ↦
      P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
        (t.toNNReal : WithTop ℝ≥0) ≤ U ω}
    ∀ᵐ t : ℝ ∂volume, 0 ≤ t →
      Tendsto (fun h : ℝ ↦
        (P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
          T ω < ((t + h).toNNReal : WithTop ℝ≥0) ∧
          (t.toNNReal : WithTop ℝ≥0) ≤ U ω} / S t) / h)
        (𝓝[>] 0) (𝓝 ((κreal.rnDeriv volume t).toReal / S t)) := by
  intro κreal S
  let ψ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ρ : Measure (WithTop ℝ≥0) := (P.restrict {ω | T ω ≤ U ω}).map T
  have hψ : Measurable ψ :=
    NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hφ : Measurable (fun ω ↦ ((T ω).untopA : ℝ)) := hψ.comp hT
  have hκle : κreal ≤ P.map (fun ω ↦ ((T ω).untopA : ℝ)) :=
    Measure.map_mono Measure.restrict_le_self hφ
  have hκAC : κreal ≪ volume :=
    (Measure.absolutelyContinuous_of_le hκle).trans hAC
  have hmap : ρ.map ψ = κreal := by
    change ((P.restrict {ω | T ω ≤ U ω}).map T).map ψ =
      (P.restrict {ω | T ω ≤ U ω}).map (fun ω ↦ ((T ω).untopA : ℝ))
    rw [Measure.map_map hψ hT]
    rfl
  have hρAC : ρ.map ψ ≪ volume := by
    rw [hmap]
    exact hκAC
  have htop : ρ {⊤} = 0 :=
    measure_top_eq_zero_of_absolutelyContinuous_map_untopA ρ hρAC
  have hwindow (t u : ℝ≥0) :
      κreal (Ico (t : ℝ) (u : ℝ)) =
        ρ (Ico (t : WithTop ℝ≥0) (u : WithTop ℝ≥0)) := by
    have hw := map_untopA_real_Ico ρ htop t u
    change (ρ.map ψ) (Ico (t : ℝ) (u : ℝ)) = _ at hw
    rw [hmap] at hw
    exact hw
  have hderiv := κreal.ae_tendsto_measureReal_Ico_div hκAC
  have hwedge := ae_tendsto_censored_wedge_rate_zero hT hU hAC
  filter_upwards [hderiv, hwedge] with t hd hw ht
  have hsum : Tendsto (fun h : ℝ ↦
      ((κreal.real (Ico t (t + h)) / h +
        P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧
          T ω < ((t + h).toNNReal : WithTop ℝ≥0)} / h) / S t))
      (𝓝[>] 0) (𝓝 ((κreal.rnDeriv volume t).toReal / S t)) := by
    simpa only [add_zero] using (hd.add (hw ht)).div_const (S t)
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hcause :
      ρ.real (Ico (t.toNNReal : WithTop ℝ≥0)
        ((t + h).toNNReal : WithTop ℝ≥0)) = κreal.real (Ico t (t + h)) := by
    change (ρ _).toReal = (κreal _).toReal
    rw [← hwindow t.toNNReal (t + h).toNNReal]
    rw [Real.coe_toNNReal t ht, Real.coe_toNNReal (t + h) (add_nonneg ht hh.le)]
  have heq :
      P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
        T ω < ((t + h).toNNReal : WithTop ℝ≥0) ∧
        (t.toNNReal : WithTop ℝ≥0) ≤ U ω} =
      κreal.real (Ico t (t + h)) +
        P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧
          T ω < ((t + h).toNNReal : WithTop ℝ≥0)} := by
    change (P _).toReal = _
    rw [censored_crude_window_measure_eq hT hU t.toNNReal (t + h).toNNReal,
      ENNReal.toReal_add (measure_ne_top ρ _) (measure_ne_top P _)]
    change ρ.real _ + P.real _ = _
    rw [hcause]
  change (_ / h + _ / h) / S t = (_ / S t) / h
  rw [heq]
  ring

end ProbabilityTheory

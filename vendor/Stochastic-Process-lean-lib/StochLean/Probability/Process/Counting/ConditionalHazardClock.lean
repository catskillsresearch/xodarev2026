/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.KernelHazardClock
public import StochLean.Probability.Process.Counting.ConditionalLifetimeHazard

/-! # History clocks for actual conditional-lifetime hazards

The native conditional distribution of the original lifetime given the
original history has the genuine history/lifetime pushforward as its
composition product. The existing joint-law clock results therefore pull
back to the original probability space without an injectivity assumption.

Measurable history clocks bounded by their calendar index give a globally
uniformly integrable family of actual compensated counts. For two ordered
bounded history clocks, the actual increment has zero integral on a history
event intersected with survival at the earlier clock. The latter transport
uses an integrable joint indicator and the measurable-pushforward integral
identity, not an injective change of variables or optional sampling.

There is no filtration assumption or assertion that history is initially
known. Neither the original space nor the history space is required to be
standard Borel. Only the lifetime target has the native structure needed by
`condDistrib`. Zero and infinite lifetimes retain their original meanings;
no additional kernel, hazard, clock or process selector is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem standardBorel_conditionalHazardClock : StandardBorelSpace (WithTop ℝ≥0) :=
  inferInstanceAs (StandardBorelSpace ℝ≥0∞)

attribute [local instance] standardBorel_conditionalHazardClock

variable {Ω K : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Ω → K} {τ : Ω → WithTop ℝ≥0}

/-- Calendar-bounded measurable history clocks preserve global uniform
integrability of the actual conditional-lifetime compensated count. -/
theorem uniformIntegrable_singleJump_sub_hazard_condDistrib_clock
    (hH : Measurable H) (hτ : Measurable τ)
    {q : ℝ≥0 → K → ℝ≥0} (hq : ∀ t, Measurable (q t))
    (hqt : ∀ t h, q t h ≤ t) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let κ := condDistrib τ H P
    UniformIntegrable (fun (t : ℝ≥0) ω ↦
      (if τ ω ≤ (q t (H ω) : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal)
        τ (q t (H ω)) ω) 1 P := by
  let κ := condDistrib τ H P
  have hMP : MeasurePreserving (fun ω ↦ (H ω, τ ω)) P ((P.map H) ⊗ₘ κ) :=
    ⟨hH.prodMk hτ, (compProd_map_condDistrib hτ.aemeasurable).symm⟩
  have hu := uniformIntegrable_singleJump_sub_hazard_compProd_clock (P.map H) κ
    (fun t ↦ (hq t).comp measurable_fst) (fun t p ↦ hqt t p.1)
  have hp := hu.comp_measurePreserving hMP le_rfl (by simp)
  simpa only [κ, Function.comp_def, stoppedProcess, id_eq] using hp

/-- On an actual history event and earlier-clock survival, the original
conditional-lifetime compensated increment has zero integral. No martingale
certificate or filtration property is assumed on the original space. -/
theorem setIntegral_singleJump_sub_hazard_condDistrib_clock_sub
    (hH : Measurable H) (hτ : Measurable τ)
    {a b : K → ℝ≥0} (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ h, a h ≤ b h) {T : ℝ≥0} (hbT : ∀ h, b h ≤ T)
    {B : Set K} (hB : MeasurableSet B) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let κ := condDistrib τ H P
    (∫ ω in {ω | H ω ∈ B ∧ (a (H ω) : WithTop ℝ≥0) < τ ω},
      ((if τ ω ≤ (b (H ω) : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal)
          τ (b (H ω)) ω) -
      ((if τ ω ≤ (a (H ω) : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal)
          τ (a (H ω)) ω) ∂P) = 0 := by
  classical
  let κ := condDistrib τ H P
  let φ : Ω → K × WithTop ℝ≥0 := fun ω ↦ (H ω, τ ω)
  let M : (K → ℝ≥0) → K × WithTop ℝ≥0 → ℝ := fun q p ↦
    (if p.2 ≤ (q p.1 : WithTop ℝ≥0) then 1 else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id (q p.1) p.2
  let S : Set (K × WithTop ℝ≥0) :=
    {p | p.1 ∈ B ∧ (a p.1 : WithTop ℝ≥0) < p.2}
  have hMP : MeasurePreserving φ P ((P.map H) ⊗ₘ κ) :=
    ⟨hH.prodMk hτ, (compProd_map_condDistrib hτ.aemeasurable).symm⟩
  have hi (q : K → ℝ≥0) (hq : Measurable q) (hqT : ∀ h, q h ≤ T) :
      Integrable (M q) ((P.map H) ⊗ₘ κ) := by
    have hmC : Measurable (fun p : K × WithTop ℝ≥0 ↦
        if p.2 ≤ (q p.1 : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd
        (WithTop.continuous_coe.measurable.comp (hq.comp measurable_fst)))
        measurable_const measurable_const
    have hiC : Integrable (fun p : K × WithTop ℝ≥0 ↦
        if p.2 ≤ (q p.1 : WithTop ℝ≥0) then (1 : ℝ) else 0) ((P.map H) ⊗ₘ κ) := by
      apply (integrable_const (1 : ℝ)).mono' hmC.aestronglyMeasurable
      exact ae_of_all _ fun p ↦ by split_ifs <;> norm_num
    exact hiC.sub (integrable_stopped_eCumulativeHazard_kernel_clock (P.map H) κ
      (hq.comp measurable_fst) (fun p ↦ hqT p.1))
  have hS : MeasurableSet S := (measurable_fst hB).inter
    (measurableSet_lt (WithTop.continuous_coe.measurable.comp (ha.comp measurable_fst))
      measurable_snd)
  have hiD := (hi b hb hbT).sub (hi a ha (fun h ↦ (hab h).trans (hbT h)))
  change Integrable (fun p ↦ M b p - M a p) ((P.map H) ⊗ₘ κ) at hiD
  have hmI : AEStronglyMeasurable (S.indicator (fun p ↦ M b p - M a p)) (P.map φ) := by
    rw [hMP.map_eq]
    exact (hiD.indicator hS).aestronglyMeasurable
  change (∫ ω in φ ⁻¹' S, M b (φ ω) - M a (φ ω) ∂P) = 0
  calc
    (∫ ω in φ ⁻¹' S, M b (φ ω) - M a (φ ω) ∂P) =
        ∫ p in S, M b p - M a p ∂((P.map H) ⊗ₘ κ) := by
      rw [← integral_indicator (hMP.measurable hS), ← integral_indicator hS]
      have he : (φ ⁻¹' S).indicator (fun ω ↦ M b (φ ω) - M a (φ ω)) =
          (S.indicator (fun p ↦ M b p - M a p)) ∘ φ := by
        funext ω
        rfl
      rw [he, ← hMP.map_eq]
      exact (integral_map hMP.measurable.aemeasurable hmI).symm
    _ = 0 := setIntegral_singleJump_sub_hazard_compProd_clock_sub (P.map H) κ
      ha hb hab hbT hB

end ProbabilityTheory

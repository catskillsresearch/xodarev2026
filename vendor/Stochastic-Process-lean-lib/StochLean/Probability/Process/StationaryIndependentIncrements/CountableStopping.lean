/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIncrements
public import StochLean.Probability.Process.Stopping.ConditionalCountableSampling
public import Mathlib.Probability.ConditionalExpectation

import Mathlib.MeasureTheory.Function.Piecewise

/-! # Stationary independent increments after countable finite stopping times

For the original filtration, independence from its deterministic past and
stationarity give constant conditional expectations of bounded measurable
increment tests. Countable pasting proves integrability of the actual test
after a genuinely finite stopping time. The existing countable conditional
sampling theorem then identifies its expectation given the stopped field.

No random-time increment law, conditional-expectation certificate, path
regularity, or replacement filtration is assumed. The stopping time takes
values in `NNReal`, so there is no finite fallback for infinity. The reference
increment retains `X u - X 0`, without an initial-value normalization.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A bounded measurable test of the actual post-stopping increment has
its stationary unconditional mean given the original stopped field. Only
countably many genuinely finite stopping values are needed, not cadlag paths. -/
theorem HasStationaryIncrements.condExp_increment_after_countable
    (hs : HasStationaryIncrements X P) (hXm : ∀ s, Measurable (X s))
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (τ : FiniteStoppingTime F) (hτcount : (range τ).Countable)
    (u : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ x, |f x| ≤ C) :
    P[(fun ω ↦ f (X (τ ω + u) ω - X (τ ω) ω)) | τ.measurableSpace] =ᵐ[P]
      fun _ ↦ ∫ ω, f (X u ω - X 0 ω) ∂P := by
  classical
  let V (s : ℝ≥0) (ω : Ω) := f (X (s + u) ω - X s ω)
  let c := ∫ ω, f (X u ω - X 0 ω) ∂P
  have hmV (s : ℝ≥0) : Measurable (V s) := hf.comp ((hXm (s + u)).sub (hXm s))
  have hiV (s : ℝ≥0) : Integrable (V s) P := by
    apply (integrable_const C).mono' (hmV s).aestronglyMeasurable
    exact Eventually.of_forall fun ω ↦ hb (X (s + u) ω - X s ω)
  have hdet (s : ℝ≥0) : P[V s | F s] =ᵐ[P] fun _ ↦ c := by
    have hCE : P[V s | F s] =ᵐ[P] fun _ ↦ ∫ ω, V s ω ∂P :=
      condExp_indep_eq ((hXm (s + u)).sub (hXm s)).comap_le (F.le s)
        (hf.comp (comap_measurable (fun ω ↦ X (s + u) ω - X s ω))).stronglyMeasurable
        (hi s (s + u) (le_add_right le_rfl)).symm
    have he : (∫ ω, V s ω ∂P) = c := (hs s u |>.comp hf).integral_eq
    exact hCE.trans (Eventually.of_forall fun _ ↦ he)
  let R := range τ
  let slices : R → Set Ω := fun r ↦ {ω | τ ω = r.1}
  let part : IndexedPartition slices :=
    { eq_of_mem := fun {_ r q} hr hq ↦ Subtype.ext (hr.symm.trans hq)
      some := fun r ↦ Classical.choose r.property
      some_mem := fun r ↦ Classical.choose_spec r.property
      index := fun ω ↦ ⟨τ ω, ⟨ω, rfl⟩⟩
      mem_index := fun _ ↦ rfl }
  let : Countable R := hτcount.to_subtype
  have hslice (r : R) : MeasurableSet (slices r) := by
    apply τ.measurableSpace_le
    simpa only [slices, WithTop.coe_inj] using τ.isStoppingTime.measurableSet_eq' r.1
  have hmZ : Measurable (fun ω ↦ V (τ ω) ω) := by
    have hpw : Measurable (part.piecewise fun r ↦ V r.1) :=
      part.measurable_piecewise hslice fun r ↦ hmV r.1
    have he : part.piecewise (fun r ↦ V r.1) = (fun ω ↦ V (τ ω) ω) := by
      funext ω
      simp only [IndexedPartition.piecewise_apply, part]
    exact he ▸ hpw
  have hiZ : Integrable (fun ω ↦ V (τ ω) ω) P := by
    apply (integrable_const C).mono' hmZ.aestronglyMeasurable
    exact Eventually.of_forall fun ω ↦ hb (X (τ ω + u) ω - X (τ ω) ω)
  exact (τ.sample_condExp_of_countable_range hτcount hiV hiZ
    (Y := fun _ _ ↦ c) (fun s ↦ (hdet s).symm)).symm

end ProbabilityTheory

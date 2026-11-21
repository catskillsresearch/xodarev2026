/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrements.FiniteFutureLaw
public import StochLean.Probability.Process.IndependentIncrements.Filtration
public import StochLean.Probability.Process.IndependentIncrements.FiniteFutureFiltration
public import StochLean.Probability.Process.Stopping.ConditionalFiniteSampling
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Actual finite future laws after finite stopping times

Past-independent increments give independence of the entire finite future
vector, not only its individual coordinates. Actual stationarity and the
existing dominated right-continuous sampling theorem identify bounded
continuous test expectations in the original stopped field.

The original sampled vector is proved AE measurable by upper dyadic stopping
grids and common-event right continuity. Equality of its true image measure
with the reference image measure then follows from bounded continuous tests.
No random-time law, sample-measurability certificate, usual augmentation,
left limits, or initial normalization is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
private theorem aemeasurable_finite_future_after {I : Type*} [Finite I]
    (hXm : ∀ s, Measurable (X s)) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (u : I → ℝ≥0) :
    AEMeasurable (fun ω i ↦ X (τ ω + u i) ω - X (τ ω) ω) P := by
  let := Fintype.ofFinite I
  let σ (n : ℕ) : FiniteStoppingTime F :=
    ⟨fun ω ↦ dyadicRightGrid n (τ ω), stoppingTime_dyadicRightGridFinite τ.isStoppingTime n⟩
  let V (s : ℝ≥0) (ω : Ω) (i : I) := X (s + u i) ω - X s ω
  have hmV (s : ℝ≥0) : Measurable (V s) :=
    measurable_pi_iff.mpr fun i ↦ (hXm (s + u i)).sub (hXm s)
  have hcount (n : ℕ) : (range (σ n)).Countable := by
    apply (countable_range_dyadicRightGrid n).mono
    rintro y ⟨ω, rfl⟩
    exact ⟨τ ω, rfl⟩
  have hmZ (n : ℕ) : Measurable (fun ω ↦ V (σ n ω) ω) := by
    let R := range (σ n)
    let : Countable R := (hcount n).to_subtype
    have hmσ : Measurable (σ n) :=
      ((σ n).isStoppingTime.measurable.untopD 0).mono (σ n).measurableSpace_le le_rfl
    have hmR : Measurable (fun ω ↦ (⟨σ n ω, mem_range_self ω⟩ : R)) :=
      hmσ.subtype_mk
    have hmEval : Measurable (fun p : Ω × R ↦ V p.2.val p.1) :=
      measurable_from_prod_countable_left fun r ↦ hmV r.val
    exact hmEval.comp (measurable_id.prodMk hmR)
  apply aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hmZ n).aemeasurable)
  filter_upwards [hr] with ω hω
  apply tendsto_pi_nhds.mpr
  intro i
  have htime : Tendsto (fun n ↦ σ n ω) atTop (𝓝[Ici (τ ω)] (τ ω)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_dyadicRightGrid (τ ω),
      Eventually.of_forall fun n ↦ le_dyadicRightGrid n (τ ω)⟩
  have hshiftTime : ContinuousWithinAt (fun s : ℝ≥0 ↦ s + u i) (Ici (τ ω)) (τ ω) :=
    continuousWithinAt_id.add continuousWithinAt_const
  have hshift : ContinuousWithinAt (fun s ↦ X (s + u i) ω) (Ici (τ ω)) (τ ω) :=
    (hω (τ ω + u i)).comp (f := fun s : ℝ≥0 ↦ s + u i) (x := τ ω) hshiftTime (by
      intro s hs
      change τ ω + u i ≤ s + u i
      exact _root_.add_le_add hs le_rfl)
  exact (hshift.sub (hω (τ ω))).tendsto.comp htime

/-- Every bounded continuous test of the whole finite future-increment
vector has its stationary mean given the original stopped field. -/
theorem HasStationaryIncrements.condExp_finite_future_after {I : Type*} [Finite I]
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F)
    (u : I → ℝ≥0) (f : (I → ℝ) →ᵇ ℝ) :
    P[(fun ω ↦ f (fun i ↦ X (τ ω + u i) ω - X (τ ω) ω)) | τ.measurableSpace] =ᵐ[P]
      fun _ ↦ ∫ ω, f (fun i ↦ X (u i) ω - X 0 ω) ∂P := by
  let := Fintype.ofFinite I
  let D (s : ℝ≥0) (ω : Ω) (i : I) := X (s + u i) ω - X s ω
  let V (s : ℝ≥0) (ω : Ω) := f (D s ω)
  have hmD (s : ℝ≥0) : Measurable (D s) :=
    measurable_pi_iff.mpr fun _ ↦ ha.measurable.sub ha.measurable
  have hmV (s : ℝ≥0) : Measurable (V s) := f.continuous.measurable.comp (hmD s)
  have hrV : HasRightContinuousPaths V P := by
    filter_upwards [hr] with ω hω s
    apply f.continuous.continuousAt.comp_continuousWithinAt
    apply continuousWithinAt_pi.mpr
    intro i
    have hshiftTime : ContinuousWithinAt (fun v : ℝ≥0 ↦ v + u i) (Ici s) s :=
      continuousWithinAt_id.add continuousWithinAt_const
    have hshift : ContinuousWithinAt (fun v ↦ X (v + u i) ω) (Ici s) s :=
      (hω (s + u i)).comp (f := fun v : ℝ≥0 ↦ v + u i) (x := s) hshiftTime (by
        intro v hv
        change s + u i ≤ v + u i
        exact _root_.add_le_add hv le_rfl)
    exact hshift.sub (hω s)
  have hSII : HasStationaryIndependentIncrements X P :=
    ⟨hs, ha.hasIndepIncrements_of_indep_comap hi⟩
  apply τ.sample_condExp_const_of_dominated_rightContinuous hmV hrV
    (integrable_const ‖f‖) (ae_of_all _ fun _ _ ↦ f.norm_coe_le_norm _) _
  intro s
  have hCE : P[V s | F s] =ᵐ[P] fun _ ↦ ∫ ω, V s ω ∂P :=
    condExp_indep_eq (hmD s).comap_le (F.le s)
      (f.continuous.measurable.comp (comap_measurable (D s))).stronglyMeasurable
      (indep_finite_future_of_indep_increment ha hi s u).symm
  have he : (∫ ω, V s ω ∂P) = ∫ ω, f (fun i ↦ X (u i) ω - X 0 ω) ∂P :=
    ((hSII.identDistrib_finite_future s u).comp f.continuous.measurable).integral_eq
  exact hCE.trans (Eventually.of_forall fun _ ↦ he)

/-- The actual finite future-increment vector after any genuinely finite
stopping time has the reference vector's law, with arbitrary initial value. -/
theorem HasStationaryIncrements.identDistrib_finite_future_after {I : Type*} [Finite I]
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F) (u : I → ℝ≥0) :
    IdentDistrib (fun ω i ↦ X (τ ω + u i) ω - X (τ ω) ω)
      (fun ω i ↦ X (u i) ω - X 0 ω) P P := by
  let := Fintype.ofFinite I
  let Y (ω : Ω) (i : I) := X (τ ω + u i) ω - X (τ ω) ω
  let Z (ω : Ω) (i : I) := X (u i) ω - X 0 ω
  have hmY : AEMeasurable Y P :=
    aemeasurable_finite_future_after (fun _ ↦ ha.measurable) hr τ u
  have hmZ : Measurable Z :=
    measurable_pi_iff.mpr fun _ ↦ ha.measurable.sub ha.measurable
  refine ⟨hmY, hmZ.aemeasurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hmY f.continuous.aestronglyMeasurable,
    integral_map hmZ.aemeasurable f.continuous.aestronglyMeasurable]
  have hCE := hs.condExp_finite_future_after ha hi hr τ u f
  calc
    (∫ ω, f (Y ω) ∂P) =
        ∫ ω, P[(fun ω ↦ f (Y ω)) | τ.measurableSpace] ω ∂P :=
      (integral_condExp τ.measurableSpace_le).symm
    _ = ∫ ω, f (Z ω) ∂P := by
      simpa only [integral_const, probReal_univ, one_smul] using integral_congr_ae hCE

end ProbabilityTheory

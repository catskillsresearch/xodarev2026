/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable
public import StochLean.Probability.Process.Path.Cadlag
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Zero-sequential continuity of the elementary integral on the Protter source class. -/
def IsGoodIntegrator (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  ∀ H : ℕ → ℝ≥0 → Ω → ℝ, ∀ hH : ∀ n, IsSimplePredictable (H n) F,
    TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2) (fun _ ↦ 0) atTop →
      TendstoInMeasure P (fun n ↦ (hH n).elementaryIntegral X) atTop 0

/-- Neighborhood formulation of source continuity at zero, with uniform input
neighborhoods and probability output neighborhoods. -/
def ElementaryIntegralContinuousAtZero (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      (∀ t ω, ‖H t ω‖ ≤ δ) → P {ω | ε ≤ ‖hH.elementaryIntegral X ω‖} ≤ η

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- R06: sequential continuity and the source neighborhood criterion are equivalent. -/
theorem isGoodIntegrator_iff_continuousAtZero :
    IsGoodIntegrator X F P ↔ ElementaryIntegralContinuousAtZero X F P := by
  classical
  constructor
  · intro hX ε hε η hη
    by_contra h
    push Not at h
    have hchoice : ∀ n : ℕ, ∃ H : ℝ≥0 → Ω → ℝ, ∃ hH : IsSimplePredictable H F,
        (∀ t ω, ‖H t ω‖ ≤ 1 / ((n : ℝ) + 1)) ∧
          η < P {ω | ε ≤ ‖hH.elementaryIntegral X ω‖} := by
      intro n
      exact h (1 / ((n : ℝ) + 1)) (by positivity)
    choose H hH hb hm using hchoice
    have hu : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2)
        (fun _ ↦ 0) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro δ hδ
      have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [hlim.eventually_lt_const hδ] with n hn
      intro z
      simpa only [dist_zero_left] using (hb n z.1 z.2).trans_lt hn
    have hlim := (tendstoInMeasure_iff_norm.mp (hX H hH hu)) ε hε
    simp only [Pi.zero_apply, sub_zero] at hlim
    have hle : η ≤ 0 := ge_of_tendsto' hlim fun n ↦ (hm n).le
    exact (not_le_of_gt hη) hle
  · intro hX H hH hu
    apply tendstoInMeasure_iff_norm.mpr
    intro ε hε
    simp only [Pi.zero_apply, sub_zero]
    apply ENNReal.tendsto_atTop_zero.mpr
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hX ε hε η hη
    obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu δ hδ)
    refine ⟨N, fun n hn ↦ hbound (H n) (hH n) ?_⟩
    intro t ω
    have h := hN n hn (t, ω)
    simpa only [dist_zero_left] using h.le

/-- Protter total semimartingale: adapted, cadlag, and a good integrator. -/
def IsTotalSemimartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧ IsGoodIntegrator X F P

/-- Protter ordinary semimartingale: every deterministic finite stopping is total. -/
def IsSemimartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  ∀ t : ℝ≥0, IsTotalSemimartingale (stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0))) F P

/-- Elementary integration against the zero process vanishes on its legal input domain. -/
theorem IsSimplePredictable.elementaryIntegral_zero_integrator
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) :
    hH.elementaryIntegral (0 : ℝ≥0 → Ω → ℝ) = 0 := by
  funext ω
  simp [IsSimplePredictable.elementaryIntegral, SimplePredictableRep.integral]

theorem isGoodIntegrator_zero (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsGoodIntegrator (0 : ℝ≥0 → Ω → ℝ) F P := by
  intro H hH _
  simp only [IsSimplePredictable.elementaryIntegral_zero_integrator]
  intro ε hε
  simp [not_le_of_gt hε]

/-- Every semimartingale is adapted, by examining the deterministic stopping at that same time. -/
theorem IsSemimartingale.adapted (hX : IsSemimartingale X F P) : Adapted F X := by
  intro t
  have ht := (hX t).1 t
  have heq : stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0)) t = X t :=
    funext fun _ ↦ stoppedProcess_eq_of_le le_rfl
  rwa [heq] at ht

/-- Countably many deterministic stoppings give one common event of cadlag paths. -/
theorem IsSemimartingale.hasCadlagPaths (hX : IsSemimartingale X F P) : HasCadlagPaths X P := by
  have hreg : ∀ᵐ ω ∂P, ∀ n : ℕ,
      IsCadlagPath (fun t ↦ stoppedProcess X (fun _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) t ω) :=
    ae_all_iff.mpr fun n ↦ (hX n).2.1
  filter_upwards [hreg] with ω hω
  have heq : ∀ t : ℝ≥0, ∃ n : ℕ,
      (fun s ↦ stoppedProcess X (fun _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) s ω) =ᶠ[𝓝 t]
        fun s ↦ X s ω := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt t
    refine ⟨n, ?_⟩
    filter_upwards [Iio_mem_nhds hn] with s hs
    exact stoppedProcess_eq_of_le (WithTop.coe_le_coe.mpr hs.le)
  constructor
  · intro t
    obtain ⟨n, hn⟩ := heq t
    exact ((hω n).1 t).congr_of_eventuallyEq
      (hn.symm.filter_mono nhdsWithin_le_nhds) hn.self_of_nhds.symm
  · intro t ht
    obtain ⟨n, hn⟩ := heq t
    obtain ⟨a, ha⟩ := (hω n).2 t ht
    exact ⟨a, ha.congr' (hn.filter_mono nhdsWithin_le_nhds)⟩

/-- A finite random constant is a good integrator; no L1 assumption is needed. -/
theorem isGoodIntegrator_const_initial [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : Measurable Z) : IsGoodIntegrator (fun _ : ℝ≥0 ↦ Z) F P := by
  intro H hH hu
  simp only [IsSimplePredictable.elementaryIntegral_const_initial]
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (((hH n).measurable_initial.mono (F.le 0) le_rfl).mul hZ).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    simpa only [zero_mul, Pi.zero_apply] using (hu.tendsto_at (0, ω)).mul_const (Z ω)

theorem isTotalSemimartingale_const_initial [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : Measurable[F 0] Z) : IsTotalSemimartingale (fun _ : ℝ≥0 ↦ Z) F P := by
  refine ⟨fun t ↦ hZ.mono (F.mono bot_le) le_rfl, ?_,
    isGoodIntegrator_const_initial (hZ.mono (F.le 0) le_rfl)⟩
  apply ae_of_all
  intro ω
  exact ⟨fun _ ↦ continuousWithinAt_const, fun _ _ ↦ ⟨Z ω, tendsto_const_nhds⟩⟩

theorem isSemimartingale_const_initial [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : Measurable[F 0] Z) : IsSemimartingale (fun _ : ℝ≥0 ↦ Z) F P := by
  intro t
  simpa only [stoppedProcess_const] using isTotalSemimartingale_const_initial hZ

end ProbabilityTheory

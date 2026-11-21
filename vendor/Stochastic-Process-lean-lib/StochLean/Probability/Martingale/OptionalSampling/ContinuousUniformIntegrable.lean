/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Martingale.Convergence.ContinuousClosure

/-!
# Uniform integrability under continuous-time stopping

Every bounded stopping value of a closed martingale is a conditional
expectation of its closing variable. Their union over all finite bounds is
therefore UI. Taking AE limits gives the same result for arbitrary families
of AE-finite stopping times. In particular Protter I.18 follows without
assigning an artificial terminal value on the event that a stopping time is
infinite: all coordinates of a stopped process are evaluated at finite times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem uniformIntegrable_bounded_stoppedValue {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i))
    (hb : ∀ i, ∃ T : ℝ≥0, ∀ ω, τ i ω ≤ T) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  obtain ⟨Z, hi, hc⟩ := hX.exists_integrable_closing hu
  apply (hi.uniformIntegrable_condExp (fun i ↦ (hτ i).measurableSpace_le)).ae_eq
  intro i
  obtain ⟨T, hT⟩ := hb i
  exact ((hX.stoppedValue_ae_eq_condExp_of_bounded hprog hr (hτ i) hT).trans
    ((condExp_congr_ae (hc T)).trans (condExp_condExp_of_le
      ((hτ i).measurableSpace_le_of_le_const hT) (F.le T)))).symm

theorem uniformIntegrable_bounded_stoppedValue_of_usual {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i))
    (hb : ∀ i, ∃ T : ℝ≥0, ∀ ω, τ i ω ≤ T) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  exact ((hX.congr hprog.stronglyAdapted heq.ae_eq).uniformIntegrable_bounded_stoppedValue
    (hu.ae_eq heq.ae_eq) hprog (ae_of_all _ hreg) hτ hb).ae_eq
      (fun i ↦ (heq.stoppedValue (τ i)).symm)

omit [IsFiniteMeasure P] in
/-- On the finite event truncation is eventually exact; no continuity at infinity is used. -/
theorem ae_tendsto_stoppedValue_truncate {τ : Ω → WithTop ℝ≥0}
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ stoppedValue X (fun ω ↦ min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω)
      atTop (𝓝 (stoppedValue X τ ω)) := by
  filter_upwards [hfinite] with ω hω
  lift τ ω to ℝ≥0 using hω with t ht
  obtain ⟨N, hN⟩ := exists_nat_ge t
  refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
  intro n hn
  have htn : (t : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
  simp only [stoppedValue, ← ht, min_eq_left htn]

theorem uniformIntegrable_stoppedValue_of_ae_finite_continuous {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i))
    (hfinite : ∀ i, ∀ᵐ ω ∂P, τ i ω ≠ ⊤) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  let ρ : ι × ℕ → Ω → WithTop ℝ≥0 := fun z ω ↦ min (τ z.1 ω) (z.2 : ℝ≥0)
  have hρ := hX.uniformIntegrable_bounded_stoppedValue hu hprog hr
    (fun z : ι × ℕ ↦ (hτ z.1).min_const (z.2 : ℝ≥0))
    (fun z ↦ ⟨(z.2 : ℝ≥0), fun _ ↦ min_le_right _ _⟩)
  let L := {g : Ω → ℝ | ∃ e : ℕ → ι × ℕ,
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (ρ (e n)) ω) atTop (𝓝 (g ω))}
  have hL : UniformIntegrable (fun g : L ↦ g.1) 1 P :=
    hρ.uniformIntegrable_of_ae_tendsto atTop
  let e : ι → L := fun i ↦ ⟨stoppedValue X (τ i), fun n ↦ (i, n),
    ae_tendsto_stoppedValue_truncate (hfinite i)⟩
  exact hL.reindex e

theorem uniformIntegrable_stoppedValue_of_ae_finite_usual {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i))
    (hfinite : ∀ i, ∀ᵐ ω ∂P, τ i ω ≠ ⊤) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  have hY := hX.congr hprog.stronglyAdapted heq.ae_eq
  exact (hY.uniformIntegrable_stoppedValue_of_ae_finite_continuous (hu.ae_eq heq.ae_eq)
      hprog (ae_of_all _ hreg) hτ hfinite).ae_eq (fun i ↦ (heq.stoppedValue (τ i)).symm)

end MeasureTheory.Martingale

namespace ProbabilityTheory.IsUIMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem stoppedProcess_of_progressive (hX : IsUIMartingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsUIMartingale (MeasureTheory.stoppedProcess X τ) F P :=
  ⟨hX.1.stoppedProcess_of_progressive hprog hr hτ,
    hX.1.uniformIntegrable_bounded_stoppedValue hX.2 hprog hr
      (fun t : ℝ≥0 ↦ (isStoppingTime_const F t).min hτ)
      (fun t ↦ ⟨t, fun _ ↦ min_le_left _ _⟩)⟩

/-- Protter I.18, with common-event right continuity under the usual conditions. -/
theorem stoppedProcess_of_usual (hX : IsUIMartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsUIMartingale (MeasureTheory.stoppedProcess X τ) F P :=
  ⟨hX.1.stoppedProcess_of_usual hF hr hτ,
    hX.1.uniformIntegrable_bounded_stoppedValue_of_usual hX.2 hF hr
      (fun t : ℝ≥0 ↦ (isStoppingTime_const F t).min hτ)
      (fun t ↦ ⟨t, fun _ ↦ min_le_left _ _⟩)⟩

end ProbabilityTheory.IsUIMartingale

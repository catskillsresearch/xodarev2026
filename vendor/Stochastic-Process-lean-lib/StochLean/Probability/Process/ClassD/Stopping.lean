/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Basic

/-! # Class D and bounded or almost-surely finite stopping families

Uniform integrability over the union of all bounded stopping times is
equivalent to Class D. This is stronger than a separate UI bound on each
fixed horizon. Truncation extends Class D to AE-finite stopping families;
the truncations are eventually exact, so no path continuity is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

private theorem ae_tendsto_truncated_value {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hf : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ X (FiniteStoppingTime.truncate hτ n ω) ω) atTop
      (𝓝 (stoppedValue X τ ω)) := by
  filter_upwards [hf] with ω hω
  lift τ ω to ℝ≥0 using hω with t ht
  obtain ⟨N, hN⟩ := exists_nat_ge t
  refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
  intro n hn
  have htn : (t : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
  change X (WithTop.untopA (min ((n : ℝ≥0) : WithTop ℝ≥0) (τ ω))) ω = _
  simp only [stoppedValue, ← ht, min_eq_right htn]

/-- A single UI estimate over all bounded stopping times suffices. -/
theorem isClassD_iff_uniformIntegrable_bounded : IsClassD X F P ↔
    UniformIntegrable (fun τ : {τ : FiniteStoppingTime F | ∃ T, ∀ ω, τ ω ≤ T} ↦
      fun ω ↦ X (τ.1 ω) ω) 1 P := by
  constructor
  · intro h
    exact h.uniformIntegrable_finiteStoppingTime Subtype.val
  · intro h
    let B := {τ : FiniteStoppingTime F | ∃ T, ∀ ω, τ ω ≤ T}
    let L := {g : Ω → E | ∃ e : ℕ → B,
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ X ((e n).1 ω) ω) atTop (𝓝 (g ω))}
    have hL : UniformIntegrable (fun g : L ↦ g.1) 1 P :=
      h.uniformIntegrable_of_ae_tendsto atTop
    let e : FiniteStoppingTime F → L := fun τ ↦ ⟨(fun ω ↦ X (τ ω) ω),
      (fun n ↦ ⟨FiniteStoppingTime.truncate τ.isStoppingTime n,
        n, FiniteStoppingTime.truncate_le _ n⟩),
      ae_tendsto_truncated_value τ.isStoppingTime (ae_of_all P τ.withTop_ne_top)⟩
    exact hL.reindex e

theorem IsClassD.uniformIntegrable_stoppedValue_of_ae_finite {ι : Type*}
    (hX : IsClassD X F P) {τ : ι → Ω → WithTop ℝ≥0}
    (hτ : ∀ i, IsStoppingTime F (τ i)) (hf : ∀ i, ∀ᵐ ω ∂P, τ i ω ≠ ⊤) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  let ρ : ι × ℕ → FiniteStoppingTime F := fun z ↦
    FiniteStoppingTime.truncate (hτ z.1) z.2
  have hρ := hX.uniformIntegrable_finiteStoppingTime ρ
  let L := {g : Ω → E | ∃ e : ℕ → ι × ℕ,
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (ρ (e n) ω) ω) atTop (𝓝 (g ω))}
  have hL : UniformIntegrable (fun g : L ↦ g.1) 1 P :=
    hρ.uniformIntegrable_of_ae_tendsto atTop
  let e : ι → L := fun i ↦ ⟨stoppedValue X (τ i), (fun n ↦ (i, n)),
    ae_tendsto_truncated_value (hτ i) (hf i)⟩
  exact hL.reindex e

theorem IsClassD.integrable_stoppedValue_of_ae_finite (hX : IsClassD X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hf : ∀ᵐ ω ∂P, τ ω ≠ ⊤) : Integrable (stoppedValue X τ) P :=
  memLp_one_iff_integrable.mp
    ((hX.uniformIntegrable_stoppedValue_of_ae_finite (fun _ : Unit ↦ hτ)
      (fun _ ↦ hf)).memLp ())

end ProbabilityTheory

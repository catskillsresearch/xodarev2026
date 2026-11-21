/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUnbounded
public import StochLean.Probability.Process.Stopping.TerminalValue

/-! # Optional sampling with possibly infinite times and an actual terminal value

Finite truncations converge to the explicit terminal-valued stopping owner.
Uniform integrability of the bounded stopping families gives L1 convergence,
and conditional-expectation contraction passes the minimum formula to the
limit. The supplied variable is required to be the actual full-time limit;
an arbitrary closing variable is not silently substituted for it.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem uniformIntegrable_stoppedValueWithTerminal {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i)) :
    UniformIntegrable (fun i ↦ stoppedValueWithTerminal X Z (τ i)) 1 P := by
  let ρ : ι × ℕ → Ω → WithTop ℝ≥0 := fun z ω ↦ min (τ z.1 ω) (z.2 : ℝ≥0)
  have hρ := hX.uniformIntegrable_bounded_stoppedValue_of_usual hu hF hr
    (fun z : ι × ℕ ↦ (hτ z.1).min_const (z.2 : ℝ≥0))
    (fun z ↦ ⟨(z.2 : ℝ≥0), fun _ ↦ min_le_right _ _⟩)
  let L := {g : Ω → ℝ | ∃ e : ℕ → ι × ℕ,
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (ρ (e n)) ω) atTop (𝓝 (g ω))}
  have hL : UniformIntegrable (fun g : L ↦ g.1) 1 P :=
    hρ.uniformIntegrable_of_ae_tendsto atTop
  let e : ι → L := fun i ↦ ⟨stoppedValueWithTerminal X Z (τ i), fun n ↦ (i, n),
    ae_tendsto_stoppedValue_truncate_withTerminal hlim⟩
  exact hL.reindex e

theorem integrable_stoppedValueWithTerminal
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Integrable (stoppedValueWithTerminal X Z τ) P :=
  memLp_one_iff_integrable.mp ((hX.uniformIntegrable_stoppedValueWithTerminal hu hF hr hlim
    (ι := Unit) (fun _ ↦ hτ)).memLp ())

/-- Both stopping times may be infinite, including on the same event. -/
theorem stoppedValueWithTerminal_min_ae_eq_condExp
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    stoppedValueWithTerminal X Z (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace] := by
  let τn : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ min (τ ω) (n : ℝ≥0)
  let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ min (σ ω) (τn n ω)
  have hτn (n) : IsStoppingTime F (τn n) := hτ.min_const (n : ℝ≥0)
  have hρ (n) : IsStoppingTime F (ρ n) := hσ.min (hτn n)
  have hb (n) (ω) : τn n ω ≤ (n : ℝ≥0) := min_le_right _ _
  have hV := hX.uniformIntegrable_bounded_stoppedValue_of_usual hu hF hr hτn
    (fun n ↦ ⟨(n : ℝ≥0), hb n⟩)
  have hU := hX.uniformIntegrable_bounded_stoppedValue_of_usual hu hF hr hρ
    (fun n ↦ ⟨(n : ℝ≥0), fun _ ↦ (min_le_right _ _).trans (hb n _)⟩)
  have hVlim := ae_tendsto_stoppedValue_truncate_withTerminal (τ := τ) hlim
  have hUlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (ρ n) ω) atTop
      (𝓝 (stoppedValueWithTerminal X Z (fun ω ↦ min (σ ω) (τ ω)) ω)) := by
    simpa only [ρ, τn, min_assoc] using
      (ae_tendsto_stoppedValue_truncate_withTerminal (τ := fun ω ↦ min (σ ω) (τ ω)) hlim)
  have hi := hV.integrable_of_ae_tendsto hVlim
  have hVL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    hV.1 (hV.memLp_of_ae_tendsto hVlim) hV.2.1 hVlim
  have hbounded (n) : stoppedValue X (ρ n) =ᵐ[P]
      P[stoppedValue X (τn n) | hσ.measurableSpace] :=
    hX.stoppedValue_min_ae_eq_condExp_of_bounded_usual hF hr hσ (hτn n) (hb n)
  have hnorm (n) : eLpNorm
      (stoppedValue X (ρ n) - P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace]) 1 P ≤
      eLpNorm (stoppedValue X (τn n) - stoppedValueWithTerminal X Z τ) 1 P := by
    calc
      _ = eLpNorm (P[stoppedValue X (τn n) - stoppedValueWithTerminal X Z τ |
          hσ.measurableSpace]) 1 P := by
        apply eLpNorm_congr_ae
        exact ((hbounded n).sub EventuallyEq.rfl).trans
          (condExp_sub (memLp_one_iff_integrable.mp (hV.memLp n)) hi _).symm
      _ ≤ _ := eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hUL1 : Tendsto (fun n ↦ eLpNorm
      (stoppedValue X (ρ n) - P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace]) 1 P)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVL1
      (fun _ ↦ zero_le) hnorm
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae hU.1 hUlim)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hU.1
      integrable_condExp.aestronglyMeasurable hUL1)

theorem stoppedValueWithTerminal_ae_eq_condExp_of_ae_le
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    stoppedValueWithTerminal X Z σ =ᵐ[P]
      P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace] := by
  refine EventuallyEq.trans ?_
    (hX.stoppedValueWithTerminal_min_ae_eq_condExp hu hF hr hlim hσ hτ)
  filter_upwards [hle] with ω hω
  simp only [stoppedValueWithTerminal, stoppedValue, min_eq_left hω]

theorem stoppedValueWithTerminal_ae_eq_condExp_terminal
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    stoppedValueWithTerminal X Z τ =ᵐ[P] P[Z | hτ.measurableSpace] := by
  have htop : IsStoppingTime F (fun _ ↦ (⊤ : WithTop ℝ≥0)) := fun _ ↦ by simp
  simpa only [stoppedValueWithTerminal_top] using
    hX.stoppedValueWithTerminal_ae_eq_condExp_of_ae_le hu hF hr hlim hτ htop
      (Eventually.of_forall fun _ ↦ le_top)

theorem memLp_stoppedValueWithTerminal
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hZ : MemLp Z p P) :
    MemLp (stoppedValueWithTerminal X Z τ) p P :=
  (hZ.condExp (m := hτ.measurableSpace) hp).ae_eq
    (hX.stoppedValueWithTerminal_ae_eq_condExp_terminal hu hF hr hlim hτ).symm

end MeasureTheory.Martingale

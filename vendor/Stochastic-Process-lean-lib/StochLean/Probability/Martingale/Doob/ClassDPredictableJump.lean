/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Basic
public import StochLean.Probability.Process.Stopping.AnnouncingStability
public import StochLean.Probability.Process.Stopping.TerminalValue
public import StochLean.Probability.Process.Stopping.ThresholdHitting
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Actual predictable jumps of Class D processes are integrable

Class D controls finite stopping values, not arbitrary evaluations of a
totalized lifetime at infinity. We first multiply the actual finite truncation
samples by the measurable finite-lifetime indicator. On that event they are
eventually the original sample; on its complement they are identically zero.
Uniform integrability therefore proves integrability of the original
zero-terminal stopped value without assuming any process terminal limit.

For a positive predictable lifetime, the same finite-lifetime mask is applied
to the truncated announcing samples. Their actual limit is the stopped left
limit on the finite event and zero on the infinite event. Class D proves this
limit integrable before it is subtracted from the actual stopped value.

No supermartingale, adaptation, usual-filtration, bounded-value, finite-lifetime,
or finite-measure hypothesis is needed. The predictable jump theorem retains
the positive-lifetime premise because the source initial jump is `X 0`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- Class D gives integrability of the original stopped value with explicit
terminal zero, even when the lifetime has positive probability of infinity. -/
theorem IsClassD.integrable_stoppedValueWithTerminal_zero
    (hD : IsClassD X F P) (hτ : IsStoppingTime F τ) :
    Integrable (stoppedValueWithTerminal X (fun _ ↦ (0 : ℝ)) τ) P := by
  classical
  let A : Set Ω := {ω | τ ω ≠ ⊤}
  have hA : MeasurableSet A := hτ.measurableSet_eq_top.compl
  let σ : ℕ → FiniteStoppingTime F := fun n ↦ FiniteStoppingTime.truncate hτ n
  have hu := (hD.uniformIntegrable_finiteStoppingTime σ).indicator hA
  apply hu.integrable_of_ae_tendsto (u := atTop)
  filter_upwards with ω
  by_cases ht : τ ω = ⊤
  · have hnot : ω ∉ A := fun hh ↦ hh ht
    simp only [indicator_of_notMem hnot, stoppedValueWithTerminal_of_top ht]
    exact tendsto_const_nhds
  · have hmem : ω ∈ A := ht
    rw [stoppedValueWithTerminal_of_ne_top ht]
    have hcoe : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
      rw [WithTop.untopA_eq_untop ht, WithTop.coe_untop]
    obtain ⟨N, hN⟩ := exists_nat_ge (τ ω).untopA
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    rw [indicator_of_mem hmem]
    have htn : τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
      rw [← hcoe]
      exact WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
    change X (FiniteStoppingTime.truncate hτ n ω) ω = _
    rw [FiniteStoppingTime.truncate_eq_untopA_of_le hτ htn]
    rfl

/-- The actual positive predictable jump is integrable. Announcing samples
are masked before taking limits, so no terminal process value is needed on
the infinite-lifetime event. Integrability is obtained before subtraction. -/
theorem IsClassD.integrable_stopped_jump_of_predictable
    (hD : IsClassD X F P) (hc : HasCadlagPaths X P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) P := by
  classical
  obtain ⟨η, hη, hηle⟩ := hτ.exists_announcing_le
  let A : Set Ω := {ω | τ ω ≠ ⊤}
  have hA : MeasurableSet A := hτ.1.measurableSet_eq_top.compl
  let σ : ℕ → FiniteStoppingTime F := fun n ↦
    FiniteStoppingTime.truncate (hη.isStoppingTime n) n
  let L := stoppedValueWithTerminal (leftLimitProcess X) (fun _ ↦ (0 : ℝ)) τ
  have hu := (hD.uniformIntegrable_finiteStoppingTime σ).indicator hA
  have hiL : Integrable L P := by
    apply hu.integrable_of_ae_tendsto (u := atTop)
    filter_upwards [hc, hpos, hη.tendsto] with ω hcω hpω hlim
    by_cases ht : τ ω = ⊤
    · have hnot : ω ∉ A := fun hh ↦ hh ht
      simp only [L, indicator_of_notMem hnot, stoppedValueWithTerminal_of_top ht]
      exact tendsto_const_nhds
    · have hmem : ω ∈ A := ht
      have hfinite (n : ℕ) : η n ω ≠ ⊤ :=
        ne_top_of_le_ne_top ht (hηle n ω)
      have hcoe : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
        rw [WithTop.untopA_eq_untop ht, WithTop.coe_untop]
      have hp : 0 < (τ ω).untopA := by
        rw [← hcoe] at hpω
        exact WithTop.coe_lt_coe.mp hpω
      have hlt (n : ℕ) : (η n ω).untopA < (τ ω).untopA := by
        have hh := hη.strict n ω hpω
        rw [← hcoe] at hh
        have he : ((η n ω).untopA : WithTop ℝ≥0) = η n ω := by
          rw [WithTop.untopA_eq_untop (hfinite n), WithTop.coe_untop]
        rw [← he] at hh
        exact WithTop.coe_lt_coe.mp hh
      have hevent : (fun n ↦ σ n ω) =ᶠ[atTop] fun n ↦ (η n ω).untopA := by
        obtain ⟨N, hN⟩ := exists_nat_ge (τ ω).untopA
        filter_upwards [eventually_ge_atTop N] with n hn
        have htn : τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
          rw [← hcoe]
          exact WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
        exact FiniteStoppingTime.truncate_eq_untopA_of_le
          (hη.isStoppingTime n) ((hηle n ω).trans htn)
      have htime : Tendsto (fun n ↦ (η n ω).untopA) atTop
          (𝓝[<] (τ ω).untopA) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨(WithTop.tendsto_untopA ht).comp hlim, Eventually.of_forall hlt⟩
      have hleft : Tendsto (fun n ↦ X (σ n ω) ω) atTop
          (𝓝 (leftLimitProcess X (τ ω).untopA ω)) :=
        (hcω.tendsto_leftLimitProcess (ne_of_gt hp)).comp
          (htime.congr' hevent.symm)
      simpa only [L, indicator_of_mem hmem, stoppedValueWithTerminal_of_ne_top ht,
        stoppedValue] using hleft
  have hiV := hD.integrable_stoppedValueWithTerminal_zero hτ.1
  have he : stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ =
      stoppedValueWithTerminal X (fun _ ↦ (0 : ℝ)) τ - L := by
    funext ω
    by_cases ht : τ ω = ⊤
    · simp only [L, stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
    · simp only [L, stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
      rfl
  rw [he]
  exact hiV.sub hiL

end ProbabilityTheory

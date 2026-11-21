/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingStability
public import StochLean.Probability.Process.Stopping.Finite
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Actual jump limits along finite announcing times

Capping an actual announcing sequence by its genuinely finite target makes
every approximating time finite on every path. The existing finite stopping
time constructor then gives ordinary evaluations, with no value assigned at
an artificial finite replacement for infinity.

On the positive-lifetime event, strict announcing and cadlag left limits
identify the terminal increment with the actual jump. On the zero-lifetime
event, the cap forces every approximating time to be zero, and the increment
limit is zero rather than the source initial jump. No adaptation, usualness,
moment assumption, or martingale property of the process is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- An actual finite predictable time admits finite stopping approximants
below it, with the genuine positive-time jump as terminal increment limit.
At a zero target both sampled times coincide and the increment limit is zero. -/
theorem IsPredictableStoppingTime.exists_finite_announcing_jump_limit
    {τ : FiniteStoppingTime F} (hτ : IsPredictableStoppingTime F τ.withTop P)
    (hc : HasCadlagPaths X P) :
    ∃ σ : ℕ → FiniteStoppingTime F,
      (∀ n ω, σ n ω ≤ τ ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ X (τ ω) ω - X (σ n ω) ω) atTop
        (𝓝 (if τ ω = 0 then 0 else jumpProcess X (τ ω) ω))) := by
  obtain ⟨ρ, hρ, hle⟩ := hτ.exists_announcing_le
  have hfinite (n : ℕ) (ω : Ω) : ρ n ω ≠ ⊤ :=
    ne_top_of_le_ne_top (τ.withTop_ne_top ω) (hle n ω)
  let σ (n : ℕ) := FiniteStoppingTime.ofNotTop (hρ.isStoppingTime n) (hfinite n)
  have hcoe (n : ℕ) (ω : Ω) : (σ n ω : WithTop ℝ≥0) = ρ n ω :=
    congrFun (FiniteStoppingTime.withTop_ofNotTop (hρ.isStoppingTime n) (hfinite n)) ω
  have hσle (n : ℕ) (ω : Ω) : σ n ω ≤ τ ω := by
    apply WithTop.coe_le_coe.mp
    rw [hcoe]
    exact hle n ω
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) := by
    filter_upwards [hρ.tendsto] with ω hω
    change Tendsto (fun n ↦ (ρ n ω).untopA) atTop (𝓝 (τ ω))
    exact (WithTop.tendsto_untopA (τ.withTop_ne_top ω)).comp hω
  refine ⟨σ, hσle, hlim, ?_⟩
  filter_upwards [hc, hlim] with ω hcω hlimω
  by_cases hzero : τ ω = 0
  · have hσzero (n : ℕ) : σ n ω = 0 :=
      le_antisymm (by simpa only [hzero] using hσle n ω) bot_le
    simpa only [hzero, hσzero, sub_self, if_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · rw [if_neg hzero]
    have hpos : 0 < τ ω := pos_iff_ne_zero.mpr hzero
    have hstrict (n : ℕ) : σ n ω < τ ω := by
      apply WithTop.coe_lt_coe.mp
      rw [hcoe]
      exact hρ.strict n ω (WithTop.coe_lt_coe.mpr hpos)
    have hleftTime : Tendsto (fun n ↦ σ n ω) atTop (𝓝[<] (τ ω)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlimω, Eventually.of_forall hstrict⟩
    exact tendsto_const_nhds.sub ((hcω.tendsto_leftLimitProcess hzero).comp hleftTime)

end ProbabilityTheory

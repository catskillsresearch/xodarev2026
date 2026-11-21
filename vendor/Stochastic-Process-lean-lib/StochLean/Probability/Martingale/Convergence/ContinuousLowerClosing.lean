/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.ConditionalLowerBound
public import StochLean.Probability.Martingale.Convergence.ContinuousL1Bounded
public import StochLean.Probability.Martingale.Convergence.ContinuousClosingProjection

/-! # Full-time convergence controlled by a conditional lower bound

A supermartingale bounded below by the conditional expectations of one
integrable variable has uniformly bounded first moments. Its actual integrable
path limit dominates the closing variable's terminal projection; equality or
L1 convergence need not hold. No second-moment hypothesis is required.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Y Z : Ω → ℝ}

theorem Supermartingale.integral_norm_le_of_condExp_lower_bound
    (hX : Supermartingale X F P) (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t) (t : ℝ≥0) :
    (∫ ω, ‖X t ω‖ ∂P) ≤ (∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖Y ω‖ ∂P) := by
  have he := integral_mono_ae integrable_condExp (hX.integrable 0)
    (hX.condExp_ae_le (show (0 : ℝ≥0) ≤ t from bot_le))
  rw [integral_condExp (F.le 0)] at he
  exact ((hX.integrable t).integral_norm_le_of_condExp_le (hclose t)).trans
    (add_le_add he le_rfl)

/-- The terminal projection of a lower closing input need not equal the
actual limit. Levy upward convergence gives precisely the inequality. -/
theorem condExp_iSup_le_limit_of_lower_closing
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) :
    P[Y | ⨆ t, F t] ≤ᵐ[P] Z := by
  let e : ℕ → ℝ≥0 := Nat.cast
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hsup : (⨆ n, G n) = ⨆ t, F t := by
    apply le_antisymm
    · exact iSup_le fun n ↦ le_iSup F (e n)
    · apply iSup_le
      intro t
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact (F.mono hn).trans (le_iSup (fun n ↦ G n) n)
  have hY := tendsto_ae_condExp (ℱ := G) (μ := P) Y
  have hN : ∀ᵐ ω ∂P, ∀ n : ℕ, P[Y | F (e n)] ω ≤ X (e n) ω :=
    eventually_countable_forall.mpr (fun n ↦ hclose (e n))
  filter_upwards [hlim, hY, hN] with ω hω hYω hNω
  have hZn : Tendsto (fun n : ℕ ↦ X (e n) ω) atTop (𝓝 (Z ω)) :=
    hω.comp tendsto_natCast_atTop_atTop
  have h := le_of_tendsto_of_tendsto' hYω hZn hNω
  simpa only [hsup] using h

theorem Supermartingale.exists_integrable_limit_of_condExp_lower_bound
    (hX : Supermartingale X F P) (hr : HasRightContinuousPaths X P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      P[Y | ⨆ t, F t] ≤ᵐ[P] Z := by
  obtain ⟨Z, hi, hl⟩ := hX.exists_integrable_limit_of_L1_bounded hr
    (hX.integral_norm_le_of_condExp_lower_bound hclose)
  exact ⟨Z, hi, hl, condExp_iSup_le_limit_of_lower_closing hclose hl⟩

end MeasureTheory

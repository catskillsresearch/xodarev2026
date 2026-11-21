/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousClosingBound
public import StochLean.Probability.Martingale.Convergence.ContinuousLowerClosing
public import StochLean.Probability.Process.Stopping.TerminalValue

/-! # Integrability at arbitrary stopping times for lower-closed supermartingales

Horizon-independent first-moment bounds and Fatou control stopped values using
the actual terminal limit. Replacing that limit on the infinite-time event by
the lower closing input's terminal projection preserves integrability. The
projection can be strictly below the actual limit; no UI or L1 convergence of
the original supermartingale is inferred.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Y Z : Ω → ℝ}

theorem eLpNorm_stoppedValue_actualLimit_le_of_closing
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    eLpNorm (stoppedValueWithTerminal X Z τ) 1 P ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖Y ω‖ ∂P)) := by
  let U (n : ℕ) := FiniteStoppingTime.truncate hτ (n : ℝ≥0)
  have hi (n) : Integrable (fun ω ↦ X (U n ω) ω) P :=
    hX.integrable_finiteStoppingTime_value (U n) (FiniteStoppingTime.truncate_le hτ _) hr
  have he (n : ℕ) : (fun ω ↦ X (U n ω) ω) =
      stoppedValue X (fun ω ↦ min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)) := by
    dsimp only [U]
    rw [FiniteStoppingTime.stoppedValue_truncate, stoppedProcess_eq_stoppedValue]
    simp only [min_comm]
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n ω ↦ X (U n ω) ω)
  · apply Eventually.of_forall
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    exact ENNReal.ofReal_le_ofReal (hX.integral_norm_finiteStoppingTime_value_le_of_closing
      hF hr hY hclose (U n) (FiniteStoppingTime.truncate_le hτ _))
  · exact fun n ↦ (hi n).aestronglyMeasurable
  · have hepoint (n : ℕ) (ω : Ω) := congrFun (he n) ω
    simpa only [hepoint] using ae_tendsto_stoppedValue_truncate_withTerminal (τ := τ) hlim

theorem integrable_stoppedValue_actualLimit_of_closing
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Integrable (stoppedValueWithTerminal X Z τ) P := by
  apply memLp_one_iff_integrable.mp
  have hnorm := hX.eLpNorm_stoppedValue_actualLimit_le_of_closing hF hr hY hclose hlim hτ
  refine ⟨?_, hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  exact aestronglyMeasurable_of_tendsto_ae _
    (fun n : ℕ ↦ (hX.integrable_stoppedValue_of_bounded (hτ.min_const (n : ℝ≥0))
      (fun _ ↦ min_le_right _ _) hr).aestronglyMeasurable)
    (ae_tendsto_stoppedValue_truncate_withTerminal hlim)

theorem stoppedValue_closingProjection_le_actualLimit
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (τ : Ω → WithTop ℝ≥0) :
    stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ ≤ᵐ[P] stoppedValueWithTerminal X Z τ := by
  filter_upwards [condExp_iSup_le_limit_of_lower_closing hclose hlim] with ω hω
  by_cases ht : τ ω = ⊤
  · simpa only [stoppedValueWithTerminal_of_top ht] using hω
  · simp only [stoppedValueWithTerminal_of_ne_top ht, le_refl]

theorem integrable_stoppedValue_closingProjection
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Integrable (stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ) P := by
  classical
  obtain ⟨Z, hiZ, hlim, _⟩ := hX.exists_integrable_limit_of_condExp_lower_bound hr hclose
  have hi := hX.integrable_stoppedValue_actualLimit_of_closing hF hr hY hclose hlim hτ
  have he : stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ =
      stoppedValueWithTerminal X Z τ + {ω | τ ω = ⊤}.indicator (P[Y | ⨆ t, F t] - Z) := by
    funext ω
    by_cases ht : τ ω = ⊤
    · simp only [Pi.add_apply, stoppedValueWithTerminal_of_top ht]
      rw [Set.indicator_of_mem (show ω ∈ {ω | τ ω = ⊤} from ht), Pi.sub_apply]
      ring
    · simp only [Pi.add_apply, stoppedValueWithTerminal_of_ne_top ht]
      rw [Set.indicator_of_notMem (show ω ∉ {ω | τ ω = ⊤} from ht), add_zero]
  rw [he]
  exact hi.add ((integrable_condExp.sub hiZ).indicator hτ.measurableSet_eq_top)

end MeasureTheory.Supermartingale

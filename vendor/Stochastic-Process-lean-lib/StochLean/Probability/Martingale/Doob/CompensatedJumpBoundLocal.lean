/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.CompensatedJumpBound
public import StochLean.Probability.Process.FiniteVariation.CompensatorInitial
public import StochLean.Probability.Process.LocalMartingale.Localization
public import StochLean.Probability.Process.Path.JumpSampling

/-! # Local compensated jump bounds without initial integrability

The two actual Protter fundamental sequences and the actual integrable-variation
localizer are intersected using the native minimum. The resulting sequence is
only required to be almost surely monotone. Further masked stopping preserves
the two UI martingales, while the predictable part retains actual integrable
variation and predictability under stopping and the initial-event mask.

The global UI jump estimate applies at every level. Divergence of the common
localizer then recovers the original jumps at all positive times on one event.
Neither an initial L1 hypothesis nor a bound on process values is introduced.
At time zero the original jump convention is unchanged and no bound is claimed.
The final consumer constructs the predictable compensator from the actual local
existence theorem, rather than assuming a proposed compensator or a localizer.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A B X : ℝ≥0 → Ω → ℝ}

private theorem ui_masked_stopped_of_le (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ σ : Ω → WithTop ℝ≥0}
    (hτ : IsUIMartingale
      (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) F P)
    (hσ : IsStoppingTime F σ) (hle : σ ≤ τ) :
    IsUIMartingale (stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator (X t)) σ) F P := by
  rw [stoppedProcess_indicator_comm',
    ← stoppedProcess_stoppedProcess_of_le_right hle, ← stoppedProcess_indicator_comm']
  convert ((isStable_cadlagUIMartingale hF) _
    ⟨hτ, (hc.indicator {ω | 0 < τ ω}).stoppedProcess τ⟩ σ hσ).1 using 2
  ext t
  rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
  congr with ω
  exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h (hle ω)⟩, fun h ↦ h.1⟩

private theorem predictable_indicator_initial (hp : IsStronglyPredictable F X)
    {E : Set Ω} (hE : MeasurableSet[F 0] E) :
    IsStronglyPredictable F (fun t ↦ E.indicator (X t)) := by
  classical
  have ha : Adapted F (fun _ : ℝ≥0 ↦ E.indicator (fun _ : Ω ↦ (1 : ℝ))) :=
    fun t ↦ measurable_const.indicator (F.mono bot_le E hE)
  have hi := ha.isStronglyPredictable_of_leftContinuous
    (fun _ _ ↦ continuousWithinAt_const)
  have he : Function.uncurry (fun t ↦ E.indicator (X t)) =
      Function.uncurry (fun _ : ℝ≥0 ↦ E.indicator (fun _ : Ω ↦ (1 : ℝ))) *
        Function.uncurry X := by
    ext ⟨t, ω⟩
    by_cases hω : ω ∈ E <;> simp [Function.uncurry, hω]
  change StronglyMeasurable[F.predictable] (Function.uncurry (fun t ↦ E.indicator (X t)))
  rw [he]
  exact StronglyMeasurable.mul hi hp

private theorem jump_masked_stopped (ω : Ω) (hc : IsCadlagPath (X · ω))
    (E : Set Ω) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    jumpProcess (stoppedProcess (fun s ↦ E.indicator (X s)) τ) t ω =
      E.indicator ({ω | (t : WithTop ℝ≥0) ≤ τ ω}.indicator (jumpProcess X t)) ω := by
  simpa only [stoppedValueWithTerminal_coe] using
    hc.stoppedValueWithTerminal_jump_masked_stoppedProcess E τ (fun _ ↦ ↑t)

/-- Actual local compensation preserves a positive-time jump bound, with
constants beta for the predictable part and twice beta for the residual.
The removed process need not have locally integrable variation here. -/
theorem IsLocalMartingale.ae_norm_jumps_compensator_and_compensated_le
    (hM : IsLocalMartingale M F P) (hU : IsLocalMartingale (A - B) F P)
    (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hpB : IsStronglyPredictable F B) (hvB : HasLocallyIntegrableVariation B F P)
    (β : ℝ) (hβ : 0 ≤ β)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (M - A) t ω‖ ≤ β) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ‖jumpProcess B t ω‖ ≤ β ∧ ‖jumpProcess ((M - A) + B) t ω‖ ≤ 2 * β := by
  have hcB : HasCadlagPaths B P := by
    have he : A - (A - B) = B := by
      funext t ω
      change A t ω - (A t ω - B t ω) = B t ω
      ring
    exact he ▸ hcA.sub hU.2.1
  obtain ⟨τ, hτ, hMt⟩ := hM.locally_ui
  obtain ⟨σ, hσ, hUs⟩ := hU.locally_ui
  obtain ⟨ν, hν, hBν⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hvB
  let ρ := min (min τ σ) ν
  have hρ : IsLocalizingSequence F ρ P := (hτ.min hσ).min hν
  let E (n : ℕ) := {ω | 0 < ρ n ω}
  let L (Z : ℝ≥0 → Ω → ℝ) (n : ℕ) :=
    MeasureTheory.stoppedProcess (fun t ↦ (E n).indicator (Z t)) (ρ n)
  have heSub (Z W : ℝ≥0 → Ω → ℝ) (n : ℕ) : L (Z - W) n = L Z n - L W n := by
    funext t ω
    simp only [L, MeasureTheory.stoppedProcess, Pi.sub_apply, Set.indicator_sub']
  have hjB (n : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (L B n) t ω‖ ≤ β := by
    have hMn : IsUIMartingale (L M n) F P :=
      ui_masked_stopped_of_le hF hM.2.1 (hMt n) (hρ.isStoppingTime n)
        (fun ω ↦ (min_le_left _ _).trans (min_le_left _ _))
    have hUn : IsUIMartingale (L A n - L B n) F P := by
      rw [← heSub]
      exact ui_masked_stopped_of_le hF hU.2.1 (hUs n) (hρ.isStoppingTime n)
        (fun ω ↦ (min_le_left _ _).trans (min_le_right _ _))
    have hE : MeasurableSet[F 0] (E n) := by
      simpa only [E, WithTop.coe_zero, compl_ofPred, not_le] using
        (hρ.isStoppingTime n 0).compl
    have hp : IsStronglyPredictable F (L B n) :=
      (predictable_indicator_initial hpB hE).stoppedProcess (hρ.isStoppingTime n)
    have hb := (hBν n).stoppedProcess
      (hpB.stoppedProcess (hν.isStoppingTime n)).stronglyAdapted.adapted hF
      (hcB.stoppedProcess (ν n)) (hρ.isStoppingTime n)
    rw [stoppedProcess_stoppedProcess_of_le_right
      (show ρ n ≤ ν n from fun _ ↦ min_le_right _ _)] at hb
    have hv : HasIntegrableVariation (L B n) P := by
      rw [show L B n = fun t ↦ (E n).indicator (MeasureTheory.stoppedProcess B (ρ n) t) from
        stoppedProcess_indicator_comm']
      exact hb.indicator (F.le 0 _ hE)
    have hr : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
        ‖jumpProcess (L M n - L A n) t ω‖ ≤ β := by
      rw [← heSub]
      filter_upwards [hM.2.1.sub hcA, hR] with ω hc hω t ht
      rw [jump_masked_stopped ω hc (E n) (ρ n) t]
      by_cases he : ω ∈ E n <;> by_cases hle : (t : WithTop ℝ≥0) ≤ ρ n ω
      · simpa only [indicator_of_mem he,
          indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) ≤ ρ n ω} from hle)] using hω t ht
      · simp only [indicator_of_mem he,
          indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℝ≥0) ≤ ρ n ω} from hle), norm_zero]
        exact hβ
      · simp only [indicator_of_notMem he, norm_zero]
        exact hβ
      · simp only [indicator_of_notMem he, norm_zero]
        exact hβ
    exact (hMn.ae_norm_jumps_compensator_and_compensated_le hUn hF
      ((hM.2.1.indicator (E n)).stoppedProcess (ρ n))
      ((hcA.indicator (E n)).stoppedProcess (ρ n))
      ((hcB.indicator (E n)).stoppedProcess (ρ n)) hp hv β hβ hr).mono
        (fun _ hω t ht ↦ (hω t ht).1)
  have hBound : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess B t ω‖ ≤ β := by
    filter_upwards [hcB, hρ.tendsto_top, ae_all_iff.mpr hjB] with ω hc hlim hω t ht
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
    have he : ω ∈ E n := (WithTop.coe_lt_coe.mpr ht).trans hn
    have hj := hω n t ht
    rwa [jump_masked_stopped ω hc (E n) (ρ n) t, indicator_of_mem he,
      indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) ≤ ρ n ω} from hn.le)] at hj
  filter_upwards [hM.2.1.sub hcA, hcB, hBound, hR] with ω hr hb hB hRω t ht
  refine ⟨hB t ht, ?_⟩
  rw [hr.jumpProcess_add hb t]
  calc
    ‖jumpProcess (M - A) t ω + jumpProcess B t ω‖ ≤
        ‖jumpProcess (M - A) t ω‖ + ‖jumpProcess B t ω‖ := norm_add_le _ _
    _ ≤ β + β := add_le_add (hRω t ht) (hB t ht)
    _ = 2 * β := (two_mul β).symm

/-- Construct the actual predictable local compensator and bounded-jump
local-martingale residual, without integrability of either initial value. -/
theorem IsLocalMartingale.exists_predictable_compensator_with_residual_jump_bound
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hvA : HasLocallyIntegrableVariation A F P) (haA : Adapted F A)
    (hcA : HasCadlagPaths A P) (β : ℝ) (hβ : 0 ≤ β)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (M - A) t ω‖ ≤ β) :
    ∃ B : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F B ∧ (∀ ω, IsCadlagPath (B · ω)) ∧ B 0 = 0 ∧
      HasLocallyIntegrableVariation B F P ∧ IsLocalMartingale (A - B) F P ∧
      IsLocalMartingale ((M - A) + B) F P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
        ‖jumpProcess B t ω‖ ≤ β ∧ ‖jumpProcess ((M - A) + B) t ω‖ ≤ 2 * β := by
  obtain ⟨B, hpB, hcB, hB0, hvB, hU, _⟩ :=
    hvA.exists_unique_predictable_compensator haA hF hcA
  have he : (M - A) + B = M - (A - B) := by
    funext t ω
    change (M t ω - A t ω) + B t ω = M t ω - (A t ω - B t ω)
    ring
  have hC : IsLocalMartingale ((M - A) + B) F P := he.symm ▸ hM.sub hU hF
  exact ⟨B, hpB, hcB, hB0, hvB, hU, hC,
    hM.ae_norm_jumps_compensator_and_compensated_le hU hF hcA hpB hvB β hβ hR⟩

end ProbabilityTheory

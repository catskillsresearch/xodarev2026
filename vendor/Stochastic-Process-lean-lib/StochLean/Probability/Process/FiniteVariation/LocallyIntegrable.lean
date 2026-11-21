/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.IntegrableStopping
public import Mathlib.Probability.Process.LocalProperty

/-! # Locally integrable variation

The local owner is Mathlib's `Locally`, including its positive-lifetime mask.
For variation that mask can be removed without any assumption on the initial
random value: at a zero lifetime the stopped path is constant. The resulting
unmasked criterion is Protter's increasing stopping-time formulation. Adapted
cadlag paths give its literal finite expected stopped-variation criterion,
including the terminal variation when a stopping time is infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- No second localization witness or process hierarchy is introduced. -/
abbrev HasLocallyIntegrableVariation (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ HasIntegrableVariation Y P) F X P

variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem hasLocallyIntegrableVariation_iff_exists_stopped :
    HasLocallyIntegrableVariation X F P ↔
      ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧
        ∀ n, HasIntegrableVariation (stoppedProcess X (τ n)) P := by
  constructor
  · rintro ⟨τ, hτ, hX⟩
    exact ⟨τ, hτ, fun n ↦
      (hasIntegrableVariation_stoppedProcess_indicator_pos_iff X (τ n)).mp (hX n)⟩
  · rintro ⟨τ, hτ, hX⟩
    exact ⟨τ, hτ, fun n ↦
      (hasIntegrableVariation_stoppedProcess_indicator_pos_iff X (τ n)).mpr (hX n)⟩

theorem HasIntegrableVariation.hasLocallyIntegrableVariation
    (hX : HasIntegrableVariation X P) : HasLocallyIntegrableVariation X F P :=
  Locally.of_prop hX

/-- The local predicate really gives finite variation on every compact
interval on a common path event; this is not an extra assumed FV field. -/
theorem HasLocallyIntegrableVariation.hasFiniteVariationPaths
    (hX : HasLocallyIntegrableVariation X F P) : HasFiniteVariationPaths X P := by
  obtain ⟨τ, hτ, hv⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hX
  apply hasFiniteVariationPaths_iff_ae_forall_horizon.mpr
  filter_upwards [hτ.tendsto_top,
    eventually_countable_forall.mpr (fun n ↦ (hv n).1)] with ω hlim hω T
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))).exists
  have he : EqOn (X · ω) (fun t ↦ stoppedProcess X (τ n) t ω) (Icc 0 T) := by
    intro t ht
    exact (stoppedProcess_eq_of_le
      (((WithTop.coe_le_coe.mpr ht.2).trans hn.le))).symm
  change eVariationOn (X · ω) (Icc 0 T) ≠ ∞
  rw [eVariationOn.congr he]
  exact (hω n).mono (subset_univ _)

/-- The source expectation at a stopping time is the actual extended
variation, with the endpoint retained and an explicit value at infinity. -/
theorem hasLocallyIntegrableVariation_iff_exists_lintegral_stoppedVariation_lt_top
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    HasLocallyIntegrableVariation X F P ↔
      ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧
        ∀ n, (∫⁻ ω, stoppedValueWithTerminal (eTotalVariationProcess X)
          (fun ω ↦ eVariationOn (X · ω) univ) (τ n) ω ∂P) < ∞ := by
  rw [hasLocallyIntegrableVariation_iff_exists_stopped]
  apply exists_congr
  intro τ
  apply and_congr_right
  intro hτ
  apply forall_congr'
  intro n
  have hs := (ha.stronglyAdapted.stoppedProcess_of_usual hF
    hc.hasRightContinuousPaths (hτ.isStoppingTime n)).adapted
  rw [hasIntegrableVariation_iff_lintegral_lt_top_of_usual hs hF (hc.stoppedProcess (τ n))]
  simp only [eVariationOn_univ_stoppedProcess]

end ProbabilityTheory

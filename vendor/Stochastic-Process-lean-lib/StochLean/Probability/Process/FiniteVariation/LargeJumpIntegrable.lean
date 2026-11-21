/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LargeJumpExitBound
public import StochLean.Probability.Process.Measurability.LargeJumpSum
public import StochLean.Probability.Process.FiniteVariation.MonotoneIntegrable
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Martingale.MonotonePaths

/-! # Actual locally integrable variation of a martingale's large jumps

The joint capped exits of the cumulative norm sum plus the source norm have
an overshoot controlled by the original martingale's actual bounded stopping
sample. Optional sampling makes that envelope integrable. This proves finite
expected variation of the actual stopped signed and norm sums, with variation
finiteness and measurability established before any real conversion.

Only a true cadlag martingale is required here, not uniform integrability,
bounded source values, square integrability, or a semimartingale witness.
The initial random value need not vanish. The local-martingale extension is
a separate native localization argument.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- The original joint capped exits give genuinely integrable total variation
for both actual cumulative processes, including the stopping endpoint. -/
theorem hasIntegrableVariation_largeJumpSumProcesses_stopped_joint_exit
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hb : 0 < b) (n : ℕ) :
    let τ := cappedNormExitSequence
      (fun t ω ↦ largeJumpNormSumProcess X b t ω + ‖X t ω‖) n
    HasIntegrableVariation (stoppedProcess (largeJumpSumProcess X b) τ) P ∧
      HasIntegrableVariation (stoppedProcess (largeJumpNormSumProcess X b) τ) P := by
  let A := largeJumpSumProcess X b
  let C := largeJumpNormSumProcess X b
  let Z : ℝ≥0 → Ω → ℝ := fun t ω ↦ C t ω + ‖X t ω‖
  let τ := cappedNormExitSequence Z n
  change HasIntegrableVariation (stoppedProcess A τ) P ∧
    HasIntegrableVariation (stoppedProcess C τ) P
  have haX := hX.stronglyAdapted.adapted
  obtain ⟨haA, haC⟩ := haX.stronglyAdapted_largeJumpSumProcesses_of_usual hF hc hb
  obtain ⟨hcA, hcC, _, hmC, hnC, hvAC⟩ := hc.largeJumpSumProcesses_properties hb
  have haZ : Adapted F Z := by
    intro t
    let : MeasurableSpace Ω := F t
    exact (haC t).measurable.add (haX t).norm
  have hcZ : HasCadlagPaths Z P := hcC.add (hc.continuous_comp continuous_norm)
  have hτ : IsStoppingTime F τ := haZ.isStoppingTime_cappedNormExitSequence hF hcZ n
  have hiX : Integrable (stoppedValue X τ) P :=
    hX.integrable_stoppedValue_of_bounded_usual hF hc.hasRightContinuousPaths hτ
      (cappedNormExitSequence_le Z n)
  let G : Ω → ℝ := fun ω ↦ 2 * ((n + 1 : ℕ) : ℝ) + ‖stoppedValue X τ ω‖
  have hiG : Integrable G P := (integrable_const _).add hiX.norm
  have hnG (ω : Ω) : 0 ≤ G ω := by dsimp only [G]; positivity
  have heτ (ω : Ω) : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop (cappedNormExitSequence_ne_top Z n ω), WithTop.coe_untop]
  have hCBound : ∀ᵐ ω ∂P, ∀ t, 0 ≤ stoppedProcess C τ t ω ∧
      stoppedProcess C τ t ω ≤ G ω := by
    filter_upwards [hc, hnC] with ω hω hnω t
    refine ⟨hnω _, ?_⟩
    exact hω.largeJumpNormSumProcess_stopped_joint_exit_le hb n t
  have hC0 : stoppedProcess C τ 0 =ᵐ[P] 0 := by
    filter_upwards with ω
    rw [stoppedProcess_eq_of_le (u := C) (τ := τ) (i := (0 : ℝ≥0)) bot_le]
    exact congrFun (largeJumpSumProcesses_initial X b).2 ω
  have haCs := haC.stoppedProcess_of_usual hF hcC.hasRightContinuousPaths hτ
  have hvC : HasIntegrableVariation (stoppedProcess C τ) P :=
    ((hmC.stoppedProcess τ).hasIntegrableVariation_of_integrable_bound haCs.adapted hF
      (hcC.stoppedProcess τ) hC0 hiG hCBound).1
  have hvar : ∀ᵐ ω ∂P,
      eVariationOn (fun t ↦ stoppedProcess A τ t ω) univ ≤ ENNReal.ofReal (G ω) := by
    filter_upwards [hc, hvAC] with ω hω hvω
    rw [eVariationOn_univ_stoppedProcess,
      stoppedValueWithTerminal_of_ne_top (cappedNormExitSequence_ne_top Z n ω)]
    change eVariationOn (A · ω) (Icc 0 (τ ω).untopA) ≤ ENNReal.ofReal (G ω)
    exact (hvω (τ ω).untopA).trans (ENNReal.ofReal_le_ofReal
      (hω.largeJumpNormSumProcess_le_before_joint_exit hb (le_of_eq (heτ ω))))
  have hfin : HasFiniteTotalVariationPaths (stoppedProcess A τ) P :=
    hvar.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have haAs := haA.stoppedProcess_of_usual hF hcA.hasRightContinuousPaths hτ
  have hiV : Integrable (fun ω ↦
      (eVariationOn (fun t ↦ stoppedProcess A τ t ω) univ).toReal) P := by
    apply hiG.mono'
      (haAs.adapted.measurable_eVariationOn_univ_of_usual hF
        (hcA.stoppedProcess τ)).ennreal_toReal.aestronglyMeasurable
    filter_upwards [hvar] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal (hnG ω)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  exact ⟨⟨hfin, hiV⟩, hvC⟩

/-- A true cadlag martingale's actual signed and norm large-jump sums have
locally integrable variation. No proposed localizing sequence is an input. -/
theorem hasLocallyIntegrableVariation_largeJumpSumProcesses
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (hb : 0 < b) :
    HasLocallyIntegrableVariation (largeJumpSumProcess X b) F P ∧
      HasLocallyIntegrableVariation (largeJumpNormSumProcess X b) F P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω ↦ largeJumpNormSumProcess X b t ω + ‖X t ω‖
  have haX := hX.stronglyAdapted.adapted
  have haC := (haX.stronglyAdapted_largeJumpSumProcesses_of_usual hF hc hb).2
  have hcC := (hc.largeJumpSumProcesses_properties hb).2.1
  have haZ : Adapted F Z := by
    intro t
    let : MeasurableSpace Ω := F t
    exact (haC t).measurable.add (haX t).norm
  have hcZ : HasCadlagPaths Z P := hcC.add (hc.continuous_comp continuous_norm)
  have hτ := haZ.isLocalizingSequence_cappedNormExitSequence hF hcZ
  exact ⟨hasLocallyIntegrableVariation_iff_exists_stopped.mpr
      ⟨cappedNormExitSequence Z, hτ, fun n ↦
        (hX.hasIntegrableVariation_largeJumpSumProcesses_stopped_joint_exit hF hc hb n).1⟩,
    hasLocallyIntegrableVariation_iff_exists_stopped.mpr
      ⟨cappedNormExitSequence Z, hτ, fun n ↦
        (hX.hasIntegrableVariation_largeJumpSumProcesses_stopped_joint_exit hF hc hb n).2⟩⟩

end MeasureTheory.Martingale

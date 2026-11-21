/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.Stopping.CadlagExitLocalization

/-! # Bounded jumps give actual locally integrable variation

The positive-time jump of the existing total-variation process is exactly
the norm of the original jump. This follows directly from Mathlib's left-limit
formula for locally bounded variation, without assuming finite total variation
on the whole half-line.

The existing capped norm exits of that zero-initial variation process have
bounded overshoot. Actual whole-half-line variation after stopping is its
compact variation at the finite exit, including the stopping endpoint. The
extended bound proves finiteness before any real conversion or L1 assertion.

Neither the original initial value nor the original stopped value is required
to be bounded, zero, or integrable. No semimartingale premise, new variation
owner, or new localizing sequence is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- The actual variation jump equals the norm of the original jump at every
positive time on one common event. Time zero is excluded: variation has no
initial atom even when the original initial random value is nonzero. -/
theorem HasFiniteVariationPaths.ae_jumpProcess_totalVariationProcess
    (hv : HasFiniteVariationPaths A P) (hc : HasCadlagPaths A P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      jumpProcess (totalVariationProcess A) t ω = ‖jumpProcess A t ω‖ := by
  filter_upwards [hv, hc] with ω hvω hcω t ht
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hlim := variationOnFromTo.tendsto_left (l := leftLimitProcess A t ω)
    (mem_univ 0) (mem_univ t) hvω
  simp only [univ_inter] at hlim
  have hl : Function.leftLim (totalVariationProcess A · ω) t =
      totalVariationProcess A t ω - ‖jumpProcess A t ω‖ := by
    simpa only [totalVariationProcess, pathTotalVariation, jumpProcess, Pi.sub_apply,
      dist_eq_norm] using
      leftLim_eq_of_tendsto (hlim (hcω.tendsto_leftLimitProcess (ne_of_gt ht)))
  change totalVariationProcess A t ω - leftLimitProcess (totalVariationProcess A) t ω = _
  rw [leftLimitProcess, if_neg (ne_of_gt ht), hl]
  exact sub_sub_cancel _ _

variable [IsFiniteMeasure P]

/-- The actual variation exits yield integrable stopped variation, with a
deterministic extended-variation bound that includes the exit jump. -/
theorem HasFiniteVariationPaths.hasIntegrableVariation_stopped_totalVariation_exit_of_jump_bound
    (hv : HasFiniteVariationPaths A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hC : 0 ≤ C)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess A t ω‖ ≤ C) (n : ℕ) :
    let ρ := cappedNormExitSequence (totalVariationProcess A) n
    HasIntegrableVariation (MeasureTheory.stoppedProcess A ρ) P ∧
      ∀ᵐ ω ∂P, eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A ρ t ω) univ ≤
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) + C) := by
  let V := totalVariationProcess A
  let ρ := cappedNormExitSequence V n
  let B : ℝ := ((n + 1 : ℕ) : ℝ) + C
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have haV : Adapted F V := ha.totalVariationProcess_of_usual hF hc
  have hcV : HasCadlagPaths V P :=
    hv.hasCadlagPaths_totalVariationProcess hc.hasRightContinuousPaths
  have hV0 : V 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦
    congrFun (totalVariationProcess_zero A) ω
  have hjV : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess V t ω‖ ≤ C := by
    filter_upwards [hv.ae_jumpProcess_totalVariationProcess hc, hj] with ω he hω t ht
    change ‖jumpProcess (totalVariationProcess A) t ω‖ ≤ C
    rw [he t ht, norm_norm]
    exact hω t ht
  have hs := hcV.ae_norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound hV0 hC hjV
  have hρ : IsStoppingTime F ρ := haV.isStoppingTime_cappedNormExitSequence hF hcV n
  have hvar : ∀ᵐ ω ∂P, eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A ρ t ω) univ ≤
      ENNReal.ofReal B := by
    filter_upwards [hv, hs] with ω hvω hω
    have hfin : ρ ω ≠ ⊤ := cappedNormExitSequence_ne_top V n ω
    let r := (ρ ω).untopA
    have hr : (r : WithTop ℝ≥0) = ρ ω := by
      dsimp only [r]
      rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
    have hb : ‖V r ω‖ ≤ B := by
      have hsamp := hω n r
      change ‖MeasureTheory.stoppedProcess V ρ r ω‖ ≤ B at hsamp
      rwa [stoppedProcess_eq_of_le hr.le] at hsamp
    have hn : 0 ≤ V r ω := pathTotalVariation_nonneg (A · ω) r
    have hvfin : eVariationOn (A · ω) (Icc 0 r) ≠ ∞ := by
      simpa only [univ_inter, BoundedVariationOn] using hvω 0 r (mem_univ _) (mem_univ _)
    rw [eVariationOn_univ_stoppedProcess, stoppedValueWithTerminal_of_ne_top hfin]
    change eVariationOn (A · ω) (Icc 0 r) ≤ ENNReal.ofReal B
    rw [← ENNReal.ofReal_toReal hvfin]
    apply ENNReal.ofReal_le_ofReal
    rw [show (eVariationOn (A · ω) (Icc 0 r)).toReal = V r ω from
      (totalVariationProcess_eq_toReal A r ω).symm]
    simpa only [Real.norm_of_nonneg hn] using hb
  have hfin : HasFiniteTotalVariationPaths (MeasureTheory.stoppedProcess A ρ) P :=
    hvar.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have has := (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hρ).adapted
  have hi : Integrable (fun ω ↦
      (eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A ρ t ω) univ).toReal) P := by
    apply (integrable_const B).mono'
      (has.measurable_eVariationOn_univ_of_usual hF
        (hc.stoppedProcess ρ)).ennreal_toReal.aestronglyMeasurable
    filter_upwards [hvar] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  exact ⟨⟨hfin, hi⟩, hvar⟩

/-- An adapted cadlag finite-variation process with bounded positive-time
jumps has locally integrable variation, without any initial moment condition. -/
theorem HasFiniteVariationPaths.hasLocallyIntegrableVariation_of_jump_bound
    (hv : HasFiniteVariationPaths A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hC : 0 ≤ C)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess A t ω‖ ≤ C) :
    HasLocallyIntegrableVariation A F P := by
  have haV := ha.totalVariationProcess_of_usual hF hc
  have hcV := hv.hasCadlagPaths_totalVariationProcess hc.hasRightContinuousPaths
  exact hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    ⟨cappedNormExitSequence (totalVariationProcess A),
      haV.isLocalizingSequence_cappedNormExitSequence hF hcV,
      fun n ↦ (hv.hasIntegrableVariation_stopped_totalVariation_exit_of_jump_bound
        ha hF hc hC hj n).1⟩

end ProbabilityTheory

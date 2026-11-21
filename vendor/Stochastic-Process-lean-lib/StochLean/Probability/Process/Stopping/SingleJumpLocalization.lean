/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.JumpExitIntegrability
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumpStability
public import StochLean.Probability.Process.Stopping.Restriction
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedStopping

/-! # Isolating the one possibly unbounded jump at a norm exit

Restrict the actual capped exit to the event that its jump norm is strictly
greater than twice the level. The resulting time is totally inaccessible.
The stopped process has no other jump above that level, and the selected
actual jump coefficient is measurable at its stopped field and integrable.
No bounded jump hypothesis is used. The strict threshold deliberately does
not exclude equality at an earlier time.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Every actual norm-exit localization has at most one unbounded jump,
at an actually constructed TI time with an actual integrable coefficient. -/
theorem HasTotallyInaccessibleJumps.exists_integrable_single_jump_at_norm_exit
    (hJ : HasTotallyInaccessibleJumps F X P) (hD : IsClassD X F P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (h0 : X 0 =ᵐ[P] 0) (n : ℕ) :
    let Y := MeasureTheory.stoppedProcess X (cappedNormExitSequence X n)
    ∃ (σ : Ω → WithTop ℝ≥0) (hσ : IsTotallyInaccessibleStoppingTime F σ P),
      StronglyMeasurable[hσ.1.measurableSpace]
        (stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) σ) ∧
      Integrable (stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) σ) P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≠ σ ω →
        ‖jumpProcess Y t ω‖ ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
  classical
  intro Y
  let T := cappedNormExitSequence X n
  have hT : IsStoppingTime F T := ha.isStoppingTime_cappedNormExitSequence hF hc n
  have hTf (ω : Ω) : T ω ≠ ⊤ := cappedNormExitSequence_ne_top X n ω
  let D := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) T
  let b : ℝ := 2 * ((n + 1 : ℕ) : ℝ)
  have hb : 0 < b := by dsimp only [b]; positivity
  let E : Set Ω := {ω | b < ‖D ω‖}
  have hmD : StronglyMeasurable[hT.measurableSpace] D :=
    ha.stronglyMeasurable_stopped_jump_of_usual hF hc hT
  have hiD : Integrable D P :=
    (hD.integrable_and_bound_stopped_jump_cappedNormExitSequence ha hF hc n).1
  have hmE : MeasurableSet[hT.measurableSpace] E := by
    let : MeasurableSpace Ω := hT.measurableSpace
    exact measurableSet_lt measurable_const hmD.measurable.norm
  let σ := restrictedStoppingTime T E
  have hs : IsStoppingTime F σ := hT.restrictedStoppingTime hmE
  have htcoe (ω : Ω) : T ω = ((T ω).untopA : WithTop ℝ≥0) := by
    rw [WithTop.untopA_eq_untop (hTf ω), WithTop.coe_untop]
  have hσ : IsTotallyInaccessibleStoppingTime F σ P := by
    apply hJ.isTotallyInaccessibleStoppingTime_of_norm_jump_ge hs hb
    filter_upwards [hc, h0] with ω hcω h0ω hfin
    have hmem : ω ∈ E := ((restrictedStoppingTime_ne_top_iff T E ω).mp hfin).1
    have heσ : σ ω = T ω := restrictedStoppingTime_of_mem T hmem
    refine ⟨(T ω).untopA, ?_, heσ.trans (htcoe ω), ?_⟩
    · have hp := hcω.cappedNormExitSequence_pos_of_zero h0ω n
      change (0 : WithTop ℝ≥0) < T ω at hp
      rw [htcoe ω] at hp
      exact WithTop.coe_lt_coe.mp hp
    · have heD : D ω = jumpProcess X (T ω).untopA ω :=
        stoppedValueWithTerminal_jump_eq_of_eq_coe (htcoe ω)
      exact (show b < ‖D ω‖ from hmem).le.trans_eq (congrArg norm heD)
  have hcY : HasCadlagPaths Y P := hc.stoppedProcess T
  have haY : Adapted F Y :=
    (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hT).adapted
  have hmC := haY.stronglyMeasurable_stopped_jump_of_usual hF hcY hσ.1
  have hendpoint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, T ω = (t : WithTop ℝ≥0) →
      jumpProcess Y t ω = D ω := by
    filter_upwards [hc] with ω hcω t ht
    change jumpProcess (MeasureTheory.stoppedProcess X T) t ω = D ω
    rw [hcω.jumpProcess_stoppedProcess T t, if_pos (by rw [ht])]
    exact (stoppedValueWithTerminal_jump_eq_of_eq_coe ht).symm
  have hiC : Integrable (stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) σ) P := by
    apply hiD.norm.mono' (hmC.mono hσ.1.measurableSpace_le).aestronglyMeasurable
    filter_upwards [hendpoint] with ω he
    by_cases hmem : ω ∈ E
    · have heσ : σ ω = ((T ω).untopA : WithTop ℝ≥0) :=
        (restrictedStoppingTime_of_mem T hmem).trans (htcoe ω)
      rw [stoppedValueWithTerminal_jump_eq_of_eq_coe heσ, he _ (htcoe ω)]
    · rw [stoppedValueWithTerminal_of_top (restrictedStoppingTime_of_notMem T hmem), norm_zero]
      exact norm_nonneg _
  refine ⟨σ, hσ, hmC, hiC, ?_⟩
  filter_upwards [hc, hendpoint] with ω hcω he t _ hne
  by_cases ht : (t : WithTop ℝ≥0) = T ω
  · have hnot : ω ∉ E := by
      intro hmem
      exact hne (ht.trans (restrictedStoppingTime_of_mem T hmem).symm)
    rw [he t ht.symm]
    exact le_of_not_gt hnot
  · exact hcω.norm_jumpProcess_stopped_cappedNormExitSequence_le_of_ne ht

end ProbabilityTheory

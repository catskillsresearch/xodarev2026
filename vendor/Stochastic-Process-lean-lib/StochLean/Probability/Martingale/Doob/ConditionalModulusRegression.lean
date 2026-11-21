/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulus
public import StochLean.Probability.Process.Path.LifetimeStepJump
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps
public import Mathlib.Probability.Martingale.Basic

/-! # Conditional-modulus semantic regressions

Constant processes have zero increment moduli even when their initial random variable is not
measurable or integrable. A zero compact horizon contains only the initial diagonal. In contrast,
the deterministic downward unit jump has compact modulus exactly one at every positive window
width. It is a bounded cadlag supermartingale starting at zero, but its jump is predictable and
does not satisfy the totally-inaccessible-jump hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.ConditionalModulusRegression

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- No measurability or moment assumption on the initial value is needed for zero increments. -/
theorem constant_compact_modulus (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (C : Ω → ℝ) (T δ : ℝ≥0) :
    IsConditionalIncrementModulus F P (fun _ ↦ C) T δ (fun _ ↦ 0) := by
  have hz (i : ConditionalIncrementIndex T δ) :
      conditionalIncrementFamily F P (fun _ ↦ C) T δ i = 0 := by
    funext ω
    simp only [conditionalIncrementFamily, sub_self, condExp_zero, Pi.zero_apply,
      ENNReal.ofReal_zero]
  refine ⟨measurable_const, fun i ↦ ?_, fun _ _ ↦ Eventually.of_forall fun _ ↦ bot_le⟩
  rw [hz]
  exact Eventually.of_forall fun _ ↦ le_rfl

/-- The same arbitrary initial variable contributes no increment on the whole half-line. -/
theorem constant_global_modulus (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (C : Ω → ℝ) (δ : ℝ≥0) :
    IsGlobalConditionalIncrementModulus F P (fun _ ↦ C) δ (fun _ ↦ 0) := by
  have hz (i : GlobalConditionalIncrementIndex δ) :
      globalConditionalIncrementFamily F P (fun _ ↦ C) δ i = 0 := by
    funext ω
    simp only [globalConditionalIncrementFamily, sub_self, condExp_zero, Pi.zero_apply,
      ENNReal.ofReal_zero]
  refine ⟨measurable_const, fun i ↦ ?_, fun _ _ ↦ Eventually.of_forall fun _ ↦ bot_le⟩
  rw [hz]
  exact Eventually.of_forall fun _ ↦ le_rfl

/-- Horizon zero contains only the pair `(0,0)`, irrespective of the window width. -/
theorem zero_horizon_modulus (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (δ : ℝ≥0) :
    IsConditionalIncrementModulus F P X 0 δ (fun _ ↦ 0) := by
  have hz (i : ConditionalIncrementIndex 0 δ) :
      conditionalIncrementFamily F P X 0 δ i = 0 := by
    have hu : i.1.2 = 0 := le_antisymm i.2.2.1 bot_le
    have ht : i.1.1 = 0 := le_antisymm (i.2.1.trans i.2.2.1) bot_le
    funext ω
    simp only [conditionalIncrementFamily, ht, hu, sub_self, condExp_zero, Pi.zero_apply,
      ENNReal.ofReal_zero]
  refine ⟨measurable_const, fun i ↦ ?_, fun _ _ ↦ Eventually.of_forall fun _ ↦ bot_le⟩
  rw [hz]
  exact Eventually.of_forall fun _ ↦ le_rfl

/-- The deterministic process with a single downward unit jump at time one. -/
noncomputable def downwardUnitJump (t : ℝ≥0) (_ : Ω) : ℝ := if 1 ≤ t then -1 else 0

private theorem downwardUnitJump_conditional_increment
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (t u : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (P[downwardUnitJump t - downwardUnitJump u | F t] ω) =
      ENNReal.ofReal ((if (1 : ℝ≥0) ≤ t then (-1 : ℝ) else 0) -
        (if (1 : ℝ≥0) ≤ u then (-1 : ℝ) else 0)) := by
  change ENNReal.ofReal (P[fun _ : Ω ↦
      (if (1 : ℝ≥0) ≤ t then (-1 : ℝ) else 0) -
        (if (1 : ℝ≥0) ≤ u then (-1 : ℝ) else 0) | F t] ω) = _
  rw [condExp_const (F.le t)]

/-- Every positive window can straddle the deterministic jump, so its actual compact modulus
is one. In particular, the nonzero modulus persists as the window width decreases to zero. -/
theorem downwardUnitJump_compact_modulus_one
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    {δ : ℝ≥0} (hδ : 0 < δ) :
    IsConditionalIncrementModulus F P downwardUnitJump 1 δ (fun _ ↦ 1) := by
  refine ⟨measurable_const, fun i ↦ ?_, fun V hV ↦ ?_⟩
  · apply Eventually.of_forall
    intro ω
    change ENNReal.ofReal (P[downwardUnitJump i.1.1 - downwardUnitJump i.1.2 |
      F i.1.1] ω) ≤ 1
    rw [downwardUnitJump_conditional_increment]
    by_cases ht : (1 : ℝ≥0) ≤ i.1.1 <;>
      by_cases hu : (1 : ℝ≥0) ≤ i.1.2 <;> norm_num [ht, hu]
  · let t : ℝ≥0 := 1 - δ
    have ht1 : t < 1 := tsub_lt_self (by norm_num) hδ
    let i : ConditionalIncrementIndex 1 δ :=
      ⟨(t, 1), tsub_le_self, le_rfl, le_tsub_add⟩
    have hi (ω : Ω) : conditionalIncrementFamily F P downwardUnitJump 1 δ i ω = 1 := by
      change ENNReal.ofReal (P[downwardUnitJump t - downwardUnitJump 1 | F t] ω) = 1
      rw [downwardUnitJump_conditional_increment]
      norm_num [not_le_of_gt ht1]
    filter_upwards [hV i] with ω hω
    exact (hi ω).symm.trans_le hω

/-- The nonvanishing-modulus example is genuinely bounded, cadlag and a supermartingale with
zero initial value. Its deterministic nonzero jump violates exactly the TI-jump requirement. -/
theorem downwardUnitJump_properties
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [IsProbabilityMeasure P] :
    Supermartingale (@downwardUnitJump Ω) F P ∧
      (∀ ω : Ω, IsCadlagPath (downwardUnitJump · ω)) ∧
        (∀ (t : ℝ≥0) (ω : Ω), ‖downwardUnitJump t ω‖ ≤ 1) ∧
          (∀ ω : Ω, downwardUnitJump 0 ω = 0) ∧
            (∀ (t : ℝ≥0) (ω : Ω), downwardUnitJump t ω = downwardUnitJump (min t 1) ω) ∧
              ¬ HasTotallyInaccessibleJumps F downwardUnitJump P := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ ↦ stronglyMeasurable_const, fun s t hst ↦ ?_,
      fun _ ↦ integrable_const _⟩
    change P[(fun _ : Ω ↦ if (1 : ℝ≥0) ≤ t then (-1 : ℝ) else 0) | F s] ≤ᵐ[P]
      (fun _ : Ω ↦ if (1 : ℝ≥0) ≤ s then (-1 : ℝ) else 0)
    rw [condExp_const (F.le s)]
    apply Eventually.of_forall
    intro ω
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · by_cases ht : (1 : ℝ≥0) ≤ t <;> norm_num [hs, ht]
  · exact fun _ ↦ isCadlagPath_step_Ici 1 (-1 : ℝ)
  · intro t ω
    by_cases ht : (1 : ℝ≥0) ≤ t <;> norm_num [downwardUnitJump, ht]
  · intro ω
    norm_num [downwardUnitJump]
  · intro t ω
    by_cases ht : (1 : ℝ≥0) ≤ t
    · rw [min_eq_right ht]
      simp only [downwardUnitJump, if_pos ht, le_refl, if_true]
    · rw [min_eq_left (le_of_not_ge ht)]
  · intro hTI
    have hz := hTI.ae_jumpProcess_eq_zero (show (0 : ℝ≥0) < 1 by norm_num)
    obtain ⟨ω, hω⟩ := hz.exists
    have hj : jumpProcess downwardUnitJump 1 ω = -1 := by
      change jumpProcess (fun (s : ℝ≥0) (_ : Ω) ↦ if 1 ≤ s then (-1 : ℝ) else 0) 1 ω = -1
      simpa only [if_true] using
        jumpProcess_step_Ici 1 (fun _ : Ω ↦ (-1 : ℝ)) 1 ω
    have he : (-1 : ℝ) = 0 := hj.symm.trans hω
    norm_num at he

end ProbabilityTheory.ConditionalModulusRegression

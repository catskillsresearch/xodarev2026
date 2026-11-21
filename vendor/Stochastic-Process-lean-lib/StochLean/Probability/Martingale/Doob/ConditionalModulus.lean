/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilySupremum
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.Process.Adapted

/-! # Version-safe conditional increment moduli

The compact short-window modulus is specified as a measurable essential supremum,
not as the pointwise supremum of arbitrarily chosen uncountably many conditional
expectations. Existence and almost-sure uniqueness precede any representative choice.
The diagonal is included, so taking positive parts does not change a consistent
supremum. These interfaces do not yet assert small-window convergence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- Ordered pairs on a compact horizon with the specified closed-width bound. -/
abbrev ConditionalIncrementIndex (T δ : ℝ≥0) :=
  {p : ℝ≥0 × ℝ≥0 // p.1 ≤ p.2 ∧ p.2 ≤ T ∧ p.2 ≤ p.1 + δ}

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def conditionalIncrementFamily (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (T δ : ℝ≥0)
    (i : ConditionalIncrementIndex T δ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (P[X i.1.1 - X i.1.2 | F i.1.1] ω)

/-- The conditional modulus is a measurable least almost-sure upper bound.
Individual conditional expectations may have different null exceptional events. -/
abbrev IsConditionalIncrementModulus (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (T δ : ℝ≥0) (W : Ω → ℝ≥0∞) : Prop :=
  IsAEFamilySupremum P (conditionalIncrementFamily F P X T δ) W

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  {T δ η : ℝ≥0} {W V : Ω → ℝ≥0∞}

theorem measurable_conditionalIncrementFamily (i : ConditionalIncrementIndex T δ) :
    Measurable (conditionalIncrementFamily F P X T δ i) :=
  ENNReal.measurable_ofReal.comp
    (stronglyMeasurable_condExp.measurable.mono (F.le i.1.1) le_rfl)

theorem exists_conditionalIncrementModulus
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [SFinite P]
    (X : ℝ≥0 → Ω → ℝ) (T δ : ℝ≥0) :
    ∃ W : Ω → ℝ≥0∞, IsConditionalIncrementModulus F P X T δ W :=
  exists_isAEFamilySupremum P (fun i ↦ measurable_conditionalIncrementFamily i)

theorem IsConditionalIncrementModulus.ae_eq
    (hW : IsConditionalIncrementModulus F P X T δ W)
    (hV : IsConditionalIncrementModulus F P X T δ V) : W =ᵐ[P] V :=
  IsAEFamilySupremum.ae_eq hW hV

theorem IsConditionalIncrementModulus.conditional_increment_le
    (hW : IsConditionalIncrementModulus F P X T δ W)
    {t u : ℝ≥0} (htu : t ≤ u) (huT : u ≤ T) (huδ : u ≤ t + δ) :
    (fun ω ↦ ENNReal.ofReal (P[X t - X u | F t] ω)) ≤ᵐ[P] W :=
  hW.le_ae ⟨(t, u), htu, huT, huδ⟩

theorem IsConditionalIncrementModulus.ae_le_of_bound
    (hW : IsConditionalIncrementModulus F P X T δ W) (U : Ω → ℝ≥0∞)
    (hU : ∀ t u : ℝ≥0, t ≤ u → u ≤ T → u ≤ t + δ →
      (fun ω ↦ ENNReal.ofReal (P[X t - X u | F t] ω)) ≤ᵐ[P] U) : W ≤ᵐ[P] U :=
  hW.ae_le U (fun i ↦ hU i.1.1 i.1.2 i.2.1 i.2.2.1 i.2.2.2)

theorem IsConditionalIncrementModulus.mono_width
    (hW : IsConditionalIncrementModulus F P X T δ W)
    (hV : IsConditionalIncrementModulus F P X T η V) (hδη : δ ≤ η) : W ≤ᵐ[P] V := by
  apply hW.ae_le_of_bound V
  intro t u htu huT huδ
  exact hV.conditional_increment_le htu huT
    (huδ.trans (add_le_add le_rfl hδη))

theorem isConditionalIncrementModulus_zero_width (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    IsConditionalIncrementModulus F P X T 0 (fun _ ↦ 0) := by
  have hz (i : ConditionalIncrementIndex T 0) :
      conditionalIncrementFamily F P X T 0 i = 0 := by
    have he : i.1.1 = i.1.2 := le_antisymm i.2.1 (by simpa only [add_zero] using i.2.2.2)
    funext ω
    simp only [conditionalIncrementFamily, he, sub_self, condExp_zero,
      Pi.zero_apply, ENNReal.ofReal_zero]
  refine ⟨measurable_const, fun i ↦ ?_, fun _ _ ↦ Eventually.of_forall fun _ ↦ bot_le⟩
  rw [hz]
  exact Eventually.of_forall fun _ ↦ le_rfl

theorem IsConditionalIncrementModulus.ae_eq_zero_of_zero_width
    (hW : IsConditionalIncrementModulus F P X T 0 W) : W =ᵐ[P] (fun _ ↦ 0) :=
  hW.ae_eq (isConditionalIncrementModulus_zero_width F P X T)

theorem IsConditionalIncrementModulus.ae_le_of_norm_bound [IsFiniteMeasure P]
    (hW : IsConditionalIncrementModulus F P X T δ W) {N : ℝ}
    (hi : ∀ t, t ≤ T → Integrable (X t) P)
    (hb : ∀ t, t ≤ T → ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) :
    W ≤ᵐ[P] (fun _ ↦ ENNReal.ofReal (2 * N)) := by
  apply hW.ae_le_of_bound
  intro t u htu huT _
  have htuT := htu.trans huT
  have hdiff : X t - X u ≤ᵐ[P] (fun _ ↦ 2 * N) := by
    filter_upwards [hb t htuT, hb u huT] with ω ht hu
    have hnorm := (norm_sub_le (X t ω) (X u ω)).trans (add_le_add ht hu)
    have hs : X t ω - X u ω ≤ ‖X t ω - X u ω‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (X t ω - X u ω)
    change X t ω - X u ω ≤ 2 * N
    linarith
  have hce := condExp_mono (m := F t) ((hi t htuT).sub (hi u huT))
    (integrable_const (2 * N)) hdiff
  rw [condExp_const (F.le t)] at hce
  exact hce.mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω

theorem IsConditionalIncrementModulus.ae_ne_top_of_norm_bound [IsFiniteMeasure P]
    (hW : IsConditionalIncrementModulus F P X T δ W) {N : ℝ}
    (hi : ∀ t, t ≤ T → Integrable (X t) P)
    (hb : ∀ t, t ≤ T → ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) :
    ∀ᵐ ω ∂P, W ω ≠ ∞ :=
  (hW.ae_le_of_norm_bound hi hb).mono fun _ hω ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω

end ProbabilityTheory

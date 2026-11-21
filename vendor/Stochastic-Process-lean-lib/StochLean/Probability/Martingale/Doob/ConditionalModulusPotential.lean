/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulus
public import Mathlib.MeasureTheory.Measure.Real

/-! # Global conditional modulus controlled by a potential tail

For widths at most one, increments starting before `T` lie in the compact horizon
`T + 1`. Later conditional increments can be controlled by a potential. The comparison
uses an eventwise essential upper bound, not another selected tail-supremum owner.
The tail event is allowed to be nonmeasurable: its outer measure is used throughout.
No uncountable intersection of the coordinate conditional inequalities is taken.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X U : ℝ≥0 → Ω → ℝ}
  {T δ : ℝ≥0} {G W : Ω → ℝ≥0∞}

theorem IsGlobalConditionalIncrementModulus.measureReal_gt_le_compact_add_potential_tail
    (hG : IsGlobalConditionalIncrementModulus F P X δ G)
    (hW : IsConditionalIncrementModulus F P X (T + 1) δ W) (hδ : δ ≤ 1)
    (hU : ∀ t u : ℝ≥0, t ≤ u → P[X t - X u | F t] ≤ᵐ[P] U t)
    {a : ℝ} (ha : 0 < a) :
    P.real {ω | ENNReal.ofReal a < G ω} ≤
      P.real {ω | ENNReal.ofReal (a / 2) < W ω} +
        P.real {ω | ∃ t : ℝ≥0, T ≤ t ∧ a / 2 < U t ω} := by
  classical
  let A : Set Ω := {ω | ENNReal.ofReal (a / 2) < W ω}
  let B : Set Ω := {ω | ∃ t : ℝ≥0, T ≤ t ∧ a / 2 < U t ω}
  let V : Ω → ℝ≥0∞ := fun ω ↦ if ω ∈ A ∪ B then ∞ else ENNReal.ofReal (a / 2)
  have hupper : G ≤ᵐ[P] V := by
    apply hG.ae_le_of_bound
    intro t u htu huδ
    by_cases htT : t ≤ T
    · have hu : u ≤ T + 1 := huδ.trans (add_le_add htT hδ)
      have hw := hW.conditional_increment_le htu hu huδ
      filter_upwards [hw] with ω hwω
      by_cases hmem : ω ∈ A ∪ B
      · exact (show ENNReal.ofReal (P[X t - X u | F t] ω) ≤ ∞ from le_top).trans_eq
          (if_pos hmem).symm
      · have hnA : ¬ ENNReal.ofReal (a / 2) < W ω := fun h ↦ hmem (Or.inl h)
        exact (hwω.trans (le_of_not_gt hnA)).trans_eq (if_neg hmem).symm
    · filter_upwards [hU t u htu] with ω huω
      by_cases hmem : ω ∈ A ∪ B
      · exact (show ENNReal.ofReal (P[X t - X u | F t] ω) ≤ ∞ from le_top).trans_eq
          (if_pos hmem).symm
      · have hnU : U t ω ≤ a / 2 := le_of_not_gt fun h ↦
          hmem (Or.inr ⟨t, (lt_of_not_ge htT).le, h⟩)
        exact (ENNReal.ofReal_le_ofReal (huω.trans hnU)).trans_eq (if_neg hmem).symm
  have hmeasure : P {ω | ENNReal.ofReal a < G ω} ≤ P (A ∪ B) := by
    apply measure_mono_ae
    filter_upwards [hupper] with ω hω hmem
    by_contra hn
    have hb : G ω ≤ ENNReal.ofReal (a / 2) :=
      hω.trans_eq (show V ω = ENNReal.ofReal (a / 2) from if_neg hn)
    exact not_lt_of_ge (hb.trans (ENNReal.ofReal_le_ofReal (half_lt_self ha).le)) hmem
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hmeasure).trans (measureReal_union_le A B)

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobWeakContinuousL1

/-! # Weak L1 control over the whole half-line

The increasing union of finite-horizon exceedance events is exactly the
all-times exceedance event. The estimate uses outer measure and does not
assume measurability of an uncountable supremum or a finite real envelope.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

theorem Martingale.measure_exists_norm_gt_le_of_eLpNorm_one_le
    (hX : Martingale X F P) (hr : HasRightContinuousPaths X P)
    {C : ℝ≥0∞} (hb : ∀ t, eLpNorm (X t) 1 P ≤ C) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ t, (ε : ℝ) < ‖X t ω‖} ≤ C := by
  let A (n : ℕ) := {ω | ∃ t ≤ (n : ℝ≥0), (ε : ℝ) < ‖X t ω‖}
  have hm : Monotone A := by
    rintro i j hij ω ⟨t, hti, ht⟩
    exact ⟨t, hti.trans (by exact_mod_cast hij), ht⟩
  have he : {ω | ∃ t, (ε : ℝ) < ‖X t ω‖} = ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, A]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, t, hn, ht⟩
    · rintro ⟨n, t, _, ht⟩
      exact ⟨t, ht⟩
  rw [he, hm.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  have h := hX.measure_exists_norm_gt_le hr (n : ℝ≥0) ε
  rw [ofReal_integral_norm_eq_lintegral_enorm (hX.integrable _),
    ← eLpNorm_one_eq_lintegral_enorm] at h
  exact h.trans (hb _)

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyCharacterization
public import StochLean.Probability.Brownian.FiltrationMartingale
public import
  StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousCharacterization

/-! # Levy's characterization with the filtration kept explicit

The left-hand side uses the canonical Brownian law/path predicate together
with adaptedness and independence from the specified past. Forgetting the
latter condition would give a false equivalence for enlarged filtrations.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsBrownianReal.quadraticVariation_eq_time_of_indep_past
    (hB : IsBrownianReal X P) (hF : F.IsUsual P) (ha : Adapted F X)
    (hind : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P) :
    Indistinguishable (IsSemimartingale.quadraticVariation
      ((hB.isContinuousLocalMartingale_of_indep_past ha hind).isSemimartingale hF) hF)
      (fun t _ ↦ (t : ℝ)) P := by
  let hM := hB.isContinuousLocalMartingale_of_indep_past ha hind
  have hc : HasContinuousPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P :=
    Filter.Eventually.of_forall (fun _ ↦ NNReal.continuous_coe)
  have hv : HasFiniteVariationPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P :=
    (show HasMonotonePaths (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P from
      Filter.Eventually.of_forall (fun _ _ _ h ↦ NNReal.coe_le_coe.mpr h)).hasFiniteVariationPaths
  have hsq : HasContinuousPaths (fun t ω ↦ X t ω ^ 2 - (t : ℝ)) P := by
    filter_upwards [hB.cont] with ω hω
    exact (hω.pow 2).sub NNReal.continuous_coe
  apply hM.quadraticVariation_eq_of_sq_sub_localMartingale hF (fun _ ↦ measurable_const) hc hv
    ((hB.toIsPreBrownianReal.square_sub_time_martingale_of_indep_past ha hind).isLocalMartingale
      hsq.hasCadlagPaths)
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  simp [hω]

theorem levy_characterization_iff (hF : F.IsUsual P) :
    (IsBrownianReal X P ∧ Adapted F X ∧ ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P) ↔
      ∃ hM : IsContinuousLocalMartingale X F P,
        Indistinguishable ((hM.isSemimartingale hF).quadraticVariation hF)
          (fun t _ ↦ (t : ℝ)) P := by
  constructor
  · rintro ⟨hB, ha, hind⟩
    exact ⟨hB.isContinuousLocalMartingale_of_indep_past ha hind,
      hB.quadraticVariation_eq_time_of_indep_past hF ha hind⟩
  · rintro ⟨hM, hq⟩
    have hB := hM.isBrownianReal_of_quadraticVariation_eq_time hF hq
    have hcq : Indistinguishable
        ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
        (fun t _ ↦ (t : ℝ)) P := by
      filter_upwards [(hM.isSemimartingale hF).continuousQuadraticVariation_eq_of_continuous
        hF hM.2, hq, hB.eval_zero_ae_eq_zero] with ω hcω hqω h0ω t
      simpa only [hqω t, h0ω, zero_pow (by decide : 2 ≠ 0), sub_zero] using hcω t
    exact ⟨hB, (hM.isSemimartingale hF).adapted,
      fun _ _ hst ↦ hM.indep_increment_past_of_bracket_eq_time hF hcq hst⟩

end ProbabilityTheory

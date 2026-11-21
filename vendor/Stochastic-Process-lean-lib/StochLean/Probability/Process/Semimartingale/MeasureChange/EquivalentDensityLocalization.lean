/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.StoppingDensity
public import StochLean.Probability.Process.Path.LeftLimitMultiplication
public import StochLean.Probability.Process.Stopping.CadlagExitLocalization

/-! # Localization of equivalent density processes

For equivalent probability measures, a single localizing sequence controls
both the forward density and its canonical reverse density.  Their common-event
product identity also gives a strictly positive forward left limit at every
positive time and identifies its reciprocal with the reverse left limit.

These facts justify later bounded uses of `1 / Z₋`.  No Girsanov decomposition
is stated in this file.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ}

/-- The joint density localizer is the minimum of the capped norm exits of the
forward and reverse canonical density processes. -/
noncomputable def equivalentDensityLocalizer (Q P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (cappedNormExitSequence (densityProcess Q P F) n ω)
    (cappedNormExitSequence (densityProcess P Q F) n ω)

/-- The joint density localizer is a localizing sequence under the source
measure. -/
theorem isLocalizingSequence_equivalentDensityLocalizer
    (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    IsLocalizingSequence F (equivalentDensityLocalizer Q P F) P := by
  have hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  have hforward :=
    Adapted.isLocalizingSequence_cappedNormExitSequence
      ((martingale_densityProcess (Q := Q) hF).stronglyAdapted.adapted) hF
        (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F))
  have hreverseQ :=
    Adapted.isLocalizingSequence_cappedNormExitSequence
      ((martingale_densityProcess (P := Q) (Q := P) hFQ).stronglyAdapted.adapted) hFQ
        (hasCadlagPaths_densityProcess (P := Q) (Q := P) (F := F))
  have hreverseP :
      IsLocalizingSequence F (cappedNormExitSequence (densityProcess P Q F)) P :=
    { isStoppingTime := hreverseQ.isStoppingTime
      tendsto_top := hPQ.ae_le hreverseQ.tendsto_top
      mono := hPQ.ae_le hreverseQ.mono }
  refine
    { isStoppingTime := fun n ↦ by
        intro t
        simpa only [equivalentDensityLocalizer, min_le_iff, Set.ofPred_or] using
          (hforward.isStoppingTime n t).union (hreverseP.isStoppingTime n t)
      tendsto_top := by
        filter_upwards [hforward.tendsto_top, hreverseP.tendsto_top] with ω hω₁ hω₂
        rw [WithTop.tendsto_nhds_top_iff] at hω₁ hω₂ ⊢
        intro t
        filter_upwards [hω₁ t, hω₂ t] with n hn₁ hn₂
        exact lt_min hn₁ hn₂
      mono := by
        filter_upwards [hforward.mono, hreverseP.mono] with ω hω₁ hω₂
        intro n m hnm
        exact min_le_min (hω₁ hnm) (hω₂ hnm) }

/-- The same joint density localizer is localizing under the target measure. -/
theorem isLocalizingSequence_equivalentDensityLocalizer_under_target
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    IsLocalizingSequence F (equivalentDensityLocalizer Q P F) Q := by
  have hloc := isLocalizingSequence_equivalentDensityLocalizer hPQ hF
  exact
    { isStoppingTime := hloc.isStoppingTime
      tendsto_top := hQP.ae_le hloc.tendsto_top
      mono := hQP.ae_le hloc.mono }

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- Strictly before the joint exit, the forward density is bounded by its
integer level. -/
theorem norm_densityProcess_le_of_lt_equivalentDensityLocalizer
    {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < equivalentDensityLocalizer Q P F n ω) :
    ‖densityProcess Q P F t ω‖ ≤ ((n + 1 : ℕ) : ℝ) :=
  norm_le_of_lt_cappedNormExitSequence
    (ht.trans_le (min_le_left _ _))

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- Strictly before the joint exit, the reverse density is bounded by the same
integer level. -/
theorem norm_reverse_densityProcess_le_of_lt_equivalentDensityLocalizer
    {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < equivalentDensityLocalizer Q P F n ω) :
    ‖densityProcess P Q F t ω‖ ≤ ((n + 1 : ℕ) : ℝ) :=
  norm_le_of_lt_cappedNormExitSequence
    (ht.trans_le (min_le_right _ _))

/-- At positive times, the forward and reverse left limits have product one on
one common source-full-measure event. -/
theorem ae_forall_leftLimit_densityProcess_reverse_mul_eq_one
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      leftLimitProcess (densityProcess P Q F) t ω *
        leftLimitProcess (densityProcess Q P F) t ω = 1 := by
  have hreverse : HasCadlagPaths (densityProcess P Q F) P :=
    hPQ.ae_le (hasCadlagPaths_densityProcess (P := Q) (Q := P) (F := F))
  have hforward : HasCadlagPaths (densityProcess Q P F) P :=
    hasCadlagPaths_densityProcess
  have hmul := hreverse.leftLimitProcess_mul hforward
  have hone :=
    (densityProcess_reverse_mul_indistinguishable_one hQP hPQ hF).leftLimitProcess
  filter_upwards [hmul, hone] with ω hmulω honeω
  intro t ht
  calc
    leftLimitProcess (densityProcess P Q F) t ω *
        leftLimitProcess (densityProcess Q P F) t ω =
        leftLimitProcess
          (densityProcess P Q F * densityProcess Q P F) t ω :=
      (hmulω t).symm
    _ = leftLimitProcess (fun _ _ ↦ (1 : ℝ)) t ω := honeω t
    _ = 1 := by
      exact IsContinuousPath.leftLimitProcess_eq
        (X := fun _ _ ↦ (1 : ℝ)) (ω := ω) continuous_const (ne_of_gt ht)

/-- Under equivalence, the forward density has a strictly positive left limit
at every positive time on one common source-full-measure event. -/
theorem ae_forall_leftLimit_densityProcess_pos_of_equivalent
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      0 < leftLimitProcess (densityProcess Q P F) t ω := by
  filter_upwards [ae_forall_leftLimit_densityProcess_reverse_mul_eq_one hQP hPQ hF,
      ae_forall_densityProcess_nonneg (Q := Q) hF,
      hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)]
    with ω hproduct hnonneg hcad
  intro t ht
  have hleft_nonneg : 0 ≤ leftLimitProcess (densityProcess Q P F) t ω := by
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    apply ge_of_tendsto (hcad.tendsto_leftLimitProcess (ne_of_gt ht))
    exact Eventually.of_forall fun s ↦ hnonneg s
  have hleft_ne : leftLimitProcess (densityProcess Q P F) t ω ≠ 0 := by
    intro hzero
    have hone := hproduct t ht
    rw [hzero, mul_zero] at hone
    exact zero_ne_one hone
  exact lt_of_le_of_ne hleft_nonneg hleft_ne.symm

/-- At every positive time, the reverse left limit is the reciprocal of the
forward left limit on one common source-full-measure event. -/
theorem ae_forall_leftLimit_reverse_eq_inv_densityProcess
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      leftLimitProcess (densityProcess P Q F) t ω =
        1 / leftLimitProcess (densityProcess Q P F) t ω := by
  filter_upwards [ae_forall_leftLimit_densityProcess_reverse_mul_eq_one hQP hPQ hF,
      ae_forall_leftLimit_densityProcess_pos_of_equivalent hQP hPQ hF]
    with ω hproduct hpos
  intro t ht
  exact (eq_div_iff (hpos t ht).ne').2 (hproduct t ht)

/-- Up to the joint localizer, both density left limits and the reciprocal of
the forward left limit are bounded by the localizer's integer level. -/
theorem ae_equivalentDensityLocalizer_leftLimit_bounds
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      (t : WithTop ℝ≥0) ≤ equivalentDensityLocalizer Q P F n ω →
      ‖leftLimitProcess (densityProcess Q P F) t ω‖ ≤ ((n + 1 : ℕ) : ℝ) ∧
        ‖1 / leftLimitProcess (densityProcess Q P F) t ω‖ ≤
          ((n + 1 : ℕ) : ℝ) := by
  have hreverse : HasCadlagPaths (densityProcess P Q F) P :=
    hPQ.ae_le (hasCadlagPaths_densityProcess (P := Q) (Q := P) (F := F))
  filter_upwards [hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F),
      hreverse, ae_forall_leftLimit_reverse_eq_inv_densityProcess hQP hPQ hF]
    with ω hforward_cad hreverse_cad hrecip
  intro n t htpos ht
  have hforward_le : (t : WithTop ℝ≥0) ≤
      cappedNormExitSequence (densityProcess Q P F) n ω :=
    ht.trans (min_le_left _ _)
  have hreverse_le : (t : WithTop ℝ≥0) ≤
      cappedNormExitSequence (densityProcess P Q F) n ω :=
    ht.trans (min_le_right _ _)
  refine ⟨hforward_cad.norm_leftLimitProcess_le_of_le_cappedNormExitSequence
    hforward_le, ?_⟩
  rw [← hrecip t htpos]
  exact hreverse_cad.norm_leftLimitProcess_le_of_le_cappedNormExitSequence hreverse_le

end ProbabilityTheory

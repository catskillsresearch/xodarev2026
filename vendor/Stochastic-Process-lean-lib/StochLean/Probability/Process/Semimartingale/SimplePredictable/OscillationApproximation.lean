/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Oscillation
public import StochLean.Probability.Process.Partition.TruncateSequence
public import StochLean.Probability.Process.Measurability.RightLimit
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Refinement

/-! # Actual finite simple approximants from oscillation partitions

The first interval is included. The source initial value is sampled independently;
positive-time coefficients sample the right-limit process at finite capped left
endpoints, never at infinity. Bounds hold on the original common caglad path event.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.CagladApproximation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  (H : ℝ≥0 → Ω → ℝ) (ha : Adapted F H) (hF : F.IsUsual P) (hc : HasCagladPaths H P)

noncomputable def partition (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (T : ℝ≥0) :
    StoppingTimePartition F :=
  StoppingTimePartition.truncateSequence (oscillationTimes (rightLimitProcess H) ε)
    (isStoppingTime_oscillationTimes (ha.rightLimitProcess_of_usual hF hc) hF
      hc.hasCadlagPaths_rightLimitProcess.hasRightContinuousPaths ε)
    (monotone_oscillationTimes hε) (oscillationTimes_zero ε) n T

noncomputable def representation (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (T : ℝ≥0) :
    SimplePredictableRep F where
  partition := partition H ha hF hc ε hε n T
  initial := H 0
  measurable_initial := ha 0
  coefficient := fun i ω ↦ rightLimitProcess H
    ((partition H ha hF hc ε hε n T).point i.castSucc ω) ω
  measurable_coefficient := fun i ↦
    (ha.rightLimitProcess_of_usual hF hc).stronglyAdapted.measurable_stoppedValue_of_usual hF
      hc.hasCadlagPaths_rightLimitProcess.hasRightContinuousPaths
      ((partition H ha hF hc ε hε n T).point i.castSucc).isStoppingTime

theorem norm_toProcess_sub_le (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (T : ℝ≥0)
    {ω : Ω} (hω : IsCagladPath (H · ω)) {t : ℝ≥0} (htT : t ≤ T)
    (htn : (t : WithTop ℝ≥0) ≤ oscillationTimes (rightLimitProcess H) ε n ω) :
    ‖(representation H ha hF hc ε hε n T).toProcess t ω - H t ω‖ ≤ ε := by
  let π := partition H ha hF hc ε hε n T
  let R := representation H ha hF hc ε hε n T
  change ‖R.toProcess t ω - H t ω‖ ≤ ε
  by_cases ht0 : t = 0
  · subst t
    rw [R.toProcess_zero]
    change ‖H 0 ω - H 0 ω‖ ≤ ε
    simpa only [sub_self, norm_zero] using hε
  · have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht0
    have hterminal : t ≤ π.terminal ω :=
      StoppingTimePartition.le_truncateSequence_terminal _ _ _ _ n T htT htn
    have hcell : ∃ i : Fin n, π.point i.castSucc ω < t ∧ t ≤ π.point i.succ ω :=
      (π.path ω).exists_cell ⟨htpos, hterminal⟩
    obtain ⟨i, hi⟩ := hcell
    have horiginal : oscillationTimes (rightLimitProcess H) ε i ω =
        (π.point i.castSucc ω : WithTop ℝ≥0) :=
      StoppingTimePartition.original_eq_truncateSequence_point_of_lt _ _ _ _ n T
        (hi.1.trans_le htT)
    have hleft : oscillationTimes (rightLimitProcess H) ε i ω < (t : WithTop ℝ≥0) := by
      rw [horiginal]
      exact WithTop.coe_lt_coe.mpr hi.1
    have hright : (t : WithTop ℝ≥0) ≤
        nextOscillationTime (rightLimitProcess H) ε
          (oscillationTimes (rightLimitProcess H) ε i) ω :=
      (WithTop.coe_le_coe.mpr hi.2).trans
        (StoppingTimePartition.coe_truncateSequence_point_le_original _ _ _ _ n T i.succ ω)
    have hb := norm_leftLimit_sub_le_of_oscillation_interval
      (oscillationTimes (rightLimitProcess H) ε i) hω.isCadlagPath_rightLimitProcess hleft hright
    rw [hω.leftLimitProcess_rightLimitProcess ht0, horiginal] at hb
    rw [R.toProcess_eq_coefficient_of_mem_cell (i := i) hi]
    change ‖rightLimitProcess H (π.point i.castSucc ω) ω - H t ω‖ ≤ ε
    simpa only [WithTop.untopA, WithTop.untopD_coe, norm_sub_rev] using hb

end ProbabilityTheory.CagladApproximation

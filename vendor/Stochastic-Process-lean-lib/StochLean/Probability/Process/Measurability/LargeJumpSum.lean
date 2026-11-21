/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LargeJumpSum
public import StochLean.Probability.Process.Stopping.LargeJumpSumEnumeration
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # Measurability of the actual large-jump cumulative processes

The literal sums over positive times are identified with the existing countable
stopping-time enumeration. For almost-sure cadlag paths, an everywhere-cadlag
indistinguishable version and relative completeness recover measurability of
the original sums, not merely of a chosen replacement process.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- Signed and norm sums are strongly adapted without any moment assumption.
Only right continuity is needed when every source path is cadlag. -/
theorem Adapted.stronglyAdapted_largeJumpSumProcesses_of_cadlag [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) :
    StronglyAdapted F (largeJumpSumProcess X b) ∧
      StronglyAdapted F (largeJumpNormSumProcess X b) :=
  ⟨ha.stronglyAdapted_tsum_Ioc_large_jumps_of_cadlag hc hb measurable_id,
    ha.stronglyAdapted_tsum_Ioc_large_jumps_of_cadlag hc hb measurable_norm⟩

/-- Under the usual conditions the original sums of an AE-cadlag adapted
process are strongly adapted. The exceptional event is handled at time zero;
no uncountable intersection of coordinatewise null events is used. -/
theorem Adapted.stronglyAdapted_largeJumpSumProcesses_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (hb : 0 < b) :
    StronglyAdapted F (largeJumpSumProcess X b) ∧
      StronglyAdapted F (largeJumpNormSumProcess X b) := by
  let : F.IsRightContinuous := hF.rightContinuous
  have hsa : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  obtain ⟨Y, hXY, hYa, hYc⟩ := hsa.exists_cadlag_indistinguishable_of_usual hF hc
  have haY := hYa.stronglyAdapted.adapted
  obtain ⟨hA, hC⟩ := haY.stronglyAdapted_largeJumpSumProcesses_of_cadlag hYc hb
  obtain ⟨heA, heC⟩ := hXY.largeJumpSumProcesses b
  have hcomplete (t : ℝ≥0) : IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  constructor
  · intro t
    exact ((hcomplete t).measurable_congr_ae (hA t).measurable
      (heA.symm.mono fun _ hω ↦ hω t)).stronglyMeasurable
  · intro t
    exact ((hcomplete t).measurable_congr_ae (hC t).measurable
      (heC.symm.mono fun _ hω ↦ hω t)).stronglyMeasurable

end MeasureTheory

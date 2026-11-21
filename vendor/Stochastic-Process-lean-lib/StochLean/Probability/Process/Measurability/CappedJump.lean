/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.LeftLimit

/-! # Joint jump measurability using only a fixed finite horizon

The capped jump uses the original adapted cadlag process and its source
left limit. Both progressive restrictions are measurable in the horizon
sigma-algebra. No measurability from future coordinates is used.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

theorem Adapted.measurable_capped_jumpProcess_of_cadlag
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) (T : ℝ≥0) :
    @Measurable (Ω × ℝ≥0) ℝ ((F T).prod inferInstance) inferInstance
      (fun p ↦ jumpProcess X (min p.2 T) p.1) := by
  have hx := (ha.stronglyAdapted.isStronglyProgressive_of_rightContinuous
    (fun ω ↦ (hc ω).1)) T
  have hla := (ha.leftLimitProcess_of_cadlag hc).stronglyAdapted
  have hl := (hla.isStronglyProgressive_of_leftContinuous
    (fun ω ↦ (hc ω).isCagladPath_leftLimitProcess.1)) T
  have hj := (hx.sub hl).measurable
  let : MeasurableSpace Ω := F T
  have hm : Measurable (fun p : Ω × ℝ≥0 ↦
      ((⟨min p.2 T, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic T), p.1)) :=
    ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst
  exact hj.comp hm

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.ConditionalVariationSign

/-! # The integrable part of the elementary-integral unit image

Yan separation is applied after changing to an equivalent law under which the
finite-horizon process coordinates are integrable.  The separating convex set
is the part of the canonical unit elementary-integral image which is integrable
under that auxiliary law.  This keeps the set independent of the later Yan
measure while retaining every deterministic conditional-variation sign test.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ} {P Q R : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

/-- The `Q`-integrable members of the source unit elementary-integral image. -/
def integrableUnitElementaryIntegralSet (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (Q : Measure Ω) : Set (Ω → ℝ) :=
  unitElementaryIntegralSet X F ∩ {Y | Integrable Y Q}

theorem zero_mem_integrableUnitElementaryIntegralSet :
    (0 : Ω → ℝ) ∈ integrableUnitElementaryIntegralSet X F Q := by
  exact ⟨zero_mem_unitElementaryIntegralSet, integrable_zero _ _ _⟩

theorem integrableUnitElementaryIntegralSet_neg_mem {Y : Ω → ℝ}
    (hY : Y ∈ integrableUnitElementaryIntegralSet X F Q) :
    -Y ∈ integrableUnitElementaryIntegralSet X F Q := by
  exact ⟨unitElementaryIntegralSet_neg_mem hY.1, hY.2.neg⟩

theorem convex_integrableUnitElementaryIntegralSet :
    Convex ℝ (integrableUnitElementaryIntegralSet X F Q) := by
  apply (convex_unitElementaryIntegralSet (X := X) (F := F)).inter
  rw [convex_iff_add_mem]
  intro Y hY Z hZ a b ha hb hab
  change Integrable (a • Y + b • Z) Q
  exact (hY.smul a).add (hZ.smul b)

theorem IsBoundedInProbability.integrableUnitElementaryIntegralSet
    (hX : IsBoundedInProbability (unitElementaryIntegralSet X F) P) :
    IsBoundedInProbability (integrableUnitElementaryIntegralSet X F Q) P := by
  intro η hη
  obtain ⟨r, hr, hbound⟩ := hX η hη
  exact ⟨r, hr, fun Y hY ↦ hbound Y hY.1⟩

/-- Every deterministic conditional-variation sign test belongs to the
integrable unit image of any law under which all process coordinates are
integrable.  The conditioning law `R` and the auxiliary integrability law `Q`
are deliberately independent. -/
theorem conditionalVariationSignRep_integral_mem_integrableUnitElementaryIntegralSet
    [IsFiniteMeasure Q] (hi : ∀ t, Integrable (X t) Q) {T : ℝ≥0}
    (π : StochLean.TimePartition T) :
    (conditionalVariationSignRep (F := F) (Q := R) (X := X) π).integral X ∈
      integrableUnitElementaryIntegralSet X F Q := by
  exact ⟨conditionalVariationSignRep_integral_mem_unitElementaryIntegralSet
      (F := F) (Q := R) (X := X) π,
    integrable_conditionalVariationSignRep_integral
      (F := F) (Q := Q) (R := R) (X := X) hi π⟩

theorem deterministicInterval_one_toProcess_norm_le_one (T t : ℝ≥0) (ω : Ω) :
    ‖(SimplePredictableRep.deterministicInterval F T 1 1).toProcess t ω‖ ≤ 1 := by
  rw [SimplePredictableRep.toProcess]
  by_cases ht : t = 0
  · simp [ht, SimplePredictableRep.deterministicInterval]
  · rw [if_neg ht]
    change ‖∑ i : Fin 1,
      if (![0, T] : Fin 2 → ℝ≥0) i.castSucc < t ∧
          t ≤ (![0, T] : Fin 2 → ℝ≥0) i.succ then 1 else 0‖ ≤ 1
    rw [Fin.sum_univ_one]
    split_ifs <;> norm_num

/-- The closed deterministic interval test is in the integrable unit image;
its integral is exactly the terminal coordinate. -/
theorem deterministicInterval_one_integral_mem_integrableUnitElementaryIntegralSet
    (T : ℝ≥0) (hi : Integrable (X T) Q) :
    (SimplePredictableRep.deterministicInterval F T 1 1).integral X ∈
      integrableUnitElementaryIntegralSet X F Q := by
  let H := SimplePredictableRep.deterministicInterval F T 1 1
  let hH : IsSimplePredictable H.toProcess F := ⟨H, rfl⟩
  refine ⟨?_, ?_⟩
  · refine ⟨H.toProcess, hH, ?_, ?_⟩
    · intro t ω
      exact deterministicInterval_one_toProcess_norm_le_one (F := F) T t ω
    · exact (hH.elementaryIntegral_eq H rfl X).symm
  · have heq : H.integral X = X T := by
      funext ω
      exact SimplePredictableRep.integral_one_closed F T X ω
    rw [heq]
    exact hi

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Algebra

/-! # Boundedness in probability for the Bichteler--Dellacherie image

The positive scale formulation below is equivalent to the usual tail
formulation: the scale `r` corresponds to the cutoff `1 / r`.  It is the
form naturally supplied by continuity of the elementary-integral map at
zero and avoids totalized division at the definition boundary.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A family of finite random variables is bounded in probability.  The
cutoff is encoded by a strictly positive rescaling to the fixed level one. -/
def IsBoundedInProbability (β : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ η : ℝ≥0∞, 0 < η → ∃ r : ℝ, 0 < r ∧
    ∀ Y ∈ β, P {ω | 1 ≤ ‖r * Y ω‖} ≤ η

/-- Boundedness in probability passes to a measure dominated by a finite
constant multiple of the source measure. -/
theorem IsBoundedInProbability.mono_measure_of_le_smul
    {β : Set (Ω → ℝ)} {P Q : Measure Ω} {C : ℝ≥0∞}
    (hβ : IsBoundedInProbability β P) (hQP : Q ≤ C • P) (hC : C ≠ ∞) :
    IsBoundedInProbability β Q := by
  intro η hη
  let D : ℝ≥0∞ := C + 1
  have hD0 : D ≠ 0 := by
    dsimp [D]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_left le_rfl))
  have hDtop : D ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC, ENNReal.one_ne_top⟩
  have hsmall : 0 < η / D := ENNReal.div_pos hη.ne' hDtop
  obtain ⟨r, hr, hrbound⟩ := hβ (η / D) hsmall
  refine ⟨r, hr, fun Y hY ↦ ?_⟩
  let A : Set Ω := {ω | 1 ≤ ‖r * Y ω‖}
  calc
    Q A ≤ (C • P) A := hQP A
    _ = C * P A := by rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ C * (η / D) := by
      apply mul_le_mul le_rfl
        (show P A ≤ η / D by simpa only [A] using hrbound Y hY)
        zero_le zero_le
    _ ≤ D * (η / D) := by
      apply mul_le_mul (show C ≤ D by
        dsimp only [D]
        exact le_add_right le_rfl) le_rfl zero_le zero_le
    _ = η := ENNReal.mul_div_cancel hD0 hDtop

/-- Elementary-integral outputs of source simple predictable integrands
whose process values are bounded by one everywhere. -/
def unitElementaryIntegralSet (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) : Set (Ω → ℝ) :=
  {Y | ∃ H : ℝ≥0 → Ω → ℝ, ∃ hH : IsSimplePredictable H F,
    (∀ t ω, ‖H t ω‖ ≤ 1) ∧ Y = hH.elementaryIntegral X}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem zero_mem_unitElementaryIntegralSet :
    (0 : Ω → ℝ) ∈ unitElementaryIntegralSet X F := by
  refine ⟨0, IsSimplePredictable.zero F, ?_, ?_⟩
  · simp
  · exact (IsSimplePredictable.elementaryIntegral_zero F X).symm

/-- The unit elementary-integral image is symmetric. -/
theorem unitElementaryIntegralSet_neg_mem {Y : Ω → ℝ}
    (hY : Y ∈ unitElementaryIntegralSet X F) :
    -Y ∈ unitElementaryIntegralSet X F := by
  obtain ⟨H, hH, hb, rfl⟩ := hY
  refine ⟨-H, hH.neg, ?_, ?_⟩
  · intro t ω
    simpa only [Pi.neg_apply, norm_neg] using hb t ω
  · exact (hH.elementaryIntegral_neg X).symm

/-- The unit elementary-integral image is convex. -/
theorem convex_unitElementaryIntegralSet :
    Convex ℝ (unitElementaryIntegralSet X F) := by
  rw [convex_iff_add_mem]
  intro Y hY Z hZ a b ha hb hab
  obtain ⟨H, hH, hHb, rfl⟩ := hY
  obtain ⟨K, hK, hKb, rfl⟩ := hZ
  let L : ℝ≥0 → Ω → ℝ := a • H + b • K
  let hL : IsSimplePredictable L F := (hH.smul a).add (hK.smul b)
  refine ⟨L, hL, ?_, ?_⟩
  · intro t ω
    change ‖a * H t ω + b * K t ω‖ ≤ 1
    calc
      ‖a * H t ω + b * K t ω‖ ≤
          ‖a * H t ω‖ + ‖b * K t ω‖ := norm_add_le _ _
      _ = a * ‖H t ω‖ + b * ‖K t ω‖ := by
        rw [norm_mul, norm_mul, Real.norm_of_nonneg ha,
          Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hHb t ω) ha)
          (mul_le_mul_of_nonneg_left (hKb t ω) hb)
      _ = 1 := by simpa only [mul_one] using hab
  · rw [show hL.elementaryIntegral X =
        fun ω ↦ a * hH.elementaryIntegral X ω +
          b * hK.elementaryIntegral X ω by
      rw [(hH.smul a).elementaryIntegral_add (hK.smul b) X,
        hH.elementaryIntegral_smul, hK.elementaryIntegral_smul]]
    rfl

/-- Continuity at zero makes the unit elementary-integral image bounded in
probability.  This is the first load-bearing step in Protter III.47. -/
theorem ElementaryIntegralContinuousAtZero.isBoundedInProbability_unitElementaryIntegralSet
    (hX : ElementaryIntegralContinuousAtZero X F P) :
    IsBoundedInProbability (unitElementaryIntegralSet X F) P := by
  intro η hη
  obtain ⟨r, hr, hbound⟩ := hX 1 zero_lt_one η hη
  refine ⟨r, hr, ?_⟩
  intro Y hY
  obtain ⟨H, hH, hHb, rfl⟩ := hY
  let hR : IsSimplePredictable (r • H) F := hH.smul r
  have hrnonneg : 0 ≤ r := hr.le
  have hRb : ∀ t ω, ‖(r • H) t ω‖ ≤ r := by
    intro t ω
    change ‖r * H t ω‖ ≤ r
    rw [norm_mul, Real.norm_of_nonneg hrnonneg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hHb t ω) hrnonneg
  have htail := hbound (r • H) hR hRb
  simpa only [hH.elementaryIntegral_smul r X] using htail

/-- The sequential good-integrator definition yields the same bounded image
through the proved source-neighborhood equivalence. -/
theorem IsGoodIntegrator.isBoundedInProbability_unitElementaryIntegralSet
    (hX : IsGoodIntegrator X F P) :
    IsBoundedInProbability (unitElementaryIntegralSet X F) P :=
  isGoodIntegrator_iff_continuousAtZero.mp hX
    |>.isBoundedInProbability_unitElementaryIntegralSet

end ProbabilityTheory

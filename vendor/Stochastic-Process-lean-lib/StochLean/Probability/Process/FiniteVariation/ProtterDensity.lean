/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Measure.StieltjesRadonNikodym
public import StochLean.Probability.Process.FiniteVariation.Integral
public import StochLean.Probability.Process.Measurability.Progressive
public import Mathlib.Data.NNRat.Encodable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # The measurable rational-liminf density in Protter I.52

For positive time, Protter defines the density of an increasing process `A`
with respect to an increasing process `C` by

`liminf_{r ↑ t, r ∈ ℚ₊} (A t - A r) / (C t - C r)`, with `0 / 0 = 0`.

The definitions below spell that liminf as a countable `iSup` of countable
`iInf`s.  This makes both product measurability and adaptedness formal
consequences of the corresponding properties of `A` and `C`.  Ratios are
formed in `ℝ≥0∞`; under the increment hypotheses they are finite and this is
the same zero-denominator convention as the real formula.

Protter defines the source density only on `(0, ∞)`.  Since StochLean's
pathwise Stieltjes integral keeps `H 0 * C 0` as a separate initial term, the
extension at zero is the ratio `A 0 / C 0`, again with `0 / 0 = 0`.

The remaining analytic bridge is to prove that the positive-time rational
liminf agrees `C.measure`-almost everywhere with the RN density from
`StieltjesRadonNikodym`.  Mathlib's one-sided interval differentiation theorem
is currently specialized to Lebesgue measure; its arbitrary locally finite
reference-measure analogue is not assumed in this file.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology NNRat

namespace ProbabilityTheory

variable {T Ω : Type*}

/-- The extended-valued increment ratio, with the native `ℝ≥0∞` convention
`0 / 0 = 0`. -/
noncomputable def protterIncrementRatioENNReal (A C : ℝ≥0 → Ω → ℝ) (r : ℚ≥0)
    (t : ℝ≥0) (w : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (A t w - A (r : ℝ≥0) w) /
    ENNReal.ofReal (C t w - C (r : ℝ≥0) w)

/-- A countable tail of rational ratios.  The auxiliary lower endpoint `p`
is itself allowed in the tail; this makes nonemptiness explicit and does not
change the liminf as `p ↑ t`. -/
noncomputable def protterTailRatioENNReal (A C : ℝ≥0 → Ω → ℝ) (p q : ℚ≥0)
    (t : ℝ≥0) (w : Ω) : ℝ≥0∞ :=
  if (p : ℝ≥0) ≤ (q : ℝ≥0) then
    if (q : ℝ≥0) < t then protterIncrementRatioENNReal A C q t w else ∞
  else ∞

/-- The lower envelope of rational ratios whose left endpoint lies between
`p` and `t`. -/
noncomputable def protterLowerSlopeENNReal (A C : ℝ≥0 → Ω → ℝ) (p : ℚ≥0)
    (t : ℝ≥0) (w : Ω) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, protterTailRatioENNReal A C p q t w

/-- Protter's positive-time rational liminf, before conversion to `ℝ`. -/
noncomputable def protterPositiveDensityENNReal (A C : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (w : Ω) : ℝ≥0∞ :=
  ⨆ p : ℚ≥0, if (p : ℝ≥0) < t then protterLowerSlopeENNReal A C p t w else 0

/-- The source density, extended to time zero in the way required by
StochLean's initial-value-inclusive Stieltjes convention. -/
noncomputable def protterDensityENNReal (A C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (w : Ω) : ℝ≥0∞ :=
  if t = 0 then ENNReal.ofReal (A 0 w) / ENNReal.ofReal (C 0 w)
  else protterPositiveDensityENNReal A C t w

/-- The real-valued Protter density. -/
noncomputable def protterDensity (A C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (w : Ω) : ℝ :=
  (protterDensityENNReal A C t w).toReal

theorem protterDensity_zero (A C : ℝ≥0 → Ω → ℝ) (w : Ω) :
    protterDensity A C 0 w =
      (ENNReal.ofReal (A 0 w) / ENNReal.ofReal (C 0 w)).toReal := by
  simp [protterDensity, protterDensityENNReal]

/-- The zero-time extension exactly supplies the separate initial term in
StochLean's Stieltjes integral. -/
theorem protterDensity_zero_mul (A C : ℝ≥0 → Ω → ℝ) (w : Ω)
    (hA0 : 0 ≤ A 0 w) (hAC0 : A 0 w ≤ C 0 w) :
    protterDensity A C 0 w * C 0 w = A 0 w := by
  rw [protterDensity_zero]
  by_cases hC : C 0 w = 0
  · have hA : A 0 w = 0 := le_antisymm (hAC0.trans_eq hC) hA0
    simp [hA, hC]
  · have hC0 : 0 < C 0 w := lt_of_le_of_ne (hA0.trans hAC0) (Ne.symm hC)
    rw [← ENNReal.ofReal_div_of_pos hC0,
      ENNReal.toReal_ofReal (div_nonneg hA0 hC0.le), div_mul_cancel₀ _ hC]

theorem protterDensity_of_pos (A C : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : 0 < t)
    (w : Ω) :
    protterDensity A C t w = (protterPositiveDensityENNReal A C t w).toReal := by
  simp [protterDensity, protterDensityENNReal, ht.ne']

section Measurability

variable [MeasurableSpace Ω]

theorem measurable_protterIncrementRatioENNReal
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Measurable (uncurry A)) (hC : Measurable (uncurry C)) (r : ℚ≥0) :
    Measurable (fun z : ℝ≥0 × Ω ↦ protterIncrementRatioENNReal A C r z.1 z.2) := by
  have hAr : Measurable (A (r : ℝ≥0)) := hA.of_uncurry_left
  have hCr : Measurable (C (r : ℝ≥0)) := hC.of_uncurry_left
  exact ((hA.sub (hAr.comp measurable_snd)).ennreal_ofReal).div
    ((hC.sub (hCr.comp measurable_snd)).ennreal_ofReal)

theorem measurable_protterTailRatioENNReal
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Measurable (uncurry A)) (hC : Measurable (uncurry C)) (p q : ℚ≥0) :
    Measurable (fun z : ℝ≥0 × Ω ↦ protterTailRatioENNReal A C p q z.1 z.2) := by
  by_cases hpq : (p : ℝ≥0) ≤ (q : ℝ≥0)
  · simp only [protterTailRatioENNReal, hpq, if_true]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (measurable_protterIncrementRatioENNReal hA hC q) measurable_const
  · simp [protterTailRatioENNReal, hpq]

theorem measurable_protterLowerSlopeENNReal
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Measurable (uncurry A)) (hC : Measurable (uncurry C)) (p : ℚ≥0) :
    Measurable (fun z : ℝ≥0 × Ω ↦ protterLowerSlopeENNReal A C p z.1 z.2) := by
  exact Measurable.iInf fun q ↦ measurable_protterTailRatioENNReal hA hC p q

theorem measurable_protterPositiveDensityENNReal
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Measurable (uncurry A)) (hC : Measurable (uncurry C)) :
    Measurable (fun z : ℝ≥0 × Ω ↦ protterPositiveDensityENNReal A C z.1 z.2) := by
  apply Measurable.iSup
  intro p
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (measurable_protterLowerSlopeENNReal hA hC p) measurable_const

theorem measurable_protterDensityENNReal
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Measurable (uncurry A)) (hC : Measurable (uncurry C)) :
    Measurable (uncurry (protterDensityENNReal A C)) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · have hA0 : Measurable (A 0) := hA.of_uncurry_left
    have hC0 : Measurable (C 0) := hC.of_uncurry_left
    exact ((hA0.comp measurable_snd).ennreal_ofReal).div
      ((hC0.comp measurable_snd).ennreal_ofReal)
  · exact measurable_protterPositiveDensityENNReal hA hC

theorem measurable_protterDensity
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Measurable (uncurry A)) (hC : Measurable (uncurry C)) :
    Measurable (uncurry (protterDensity A C)) :=
  (measurable_protterDensityENNReal hA hC).ennreal_toReal

end Measurability

section Adapted

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem adapted_protterDensityENNReal {A C : ℝ≥0 → Ω → ℝ}
    (hA : Adapted F A) (hC : Adapted F C) :
    Adapted F (protterDensityENNReal A C) := by
  intro t
  change @Measurable Ω ℝ≥0∞ (F t) ENNReal.measurableSpace
    (fun w ↦ protterDensityENNReal A C t w)
  by_cases ht : t = 0
  · subst t
    have hfun : protterDensityENNReal A C 0 =
        fun w ↦ ENNReal.ofReal (A 0 w) / ENNReal.ofReal (C 0 w) := by
      funext w
      simp [protterDensityENNReal]
    rw [hfun]
    change @Measurable Ω ℝ≥0∞ (F 0) ENNReal.measurableSpace
      ((fun w ↦ ENNReal.ofReal (A 0 w)) / fun w ↦ ENNReal.ofReal (C 0 w))
    exact (hA 0).ennreal_ofReal.div (hC 0).ennreal_ofReal
  · simp only [protterDensityENNReal, ht, if_false, protterPositiveDensityENNReal]
    apply Measurable.iSup
    intro p
    by_cases hpt : (p : ℝ≥0) < t
    · simp only [hpt, if_true]
      simp only [protterLowerSlopeENNReal]
      apply Measurable.iInf
      intro q
      by_cases hpq : (p : ℝ≥0) ≤ (q : ℝ≥0)
      · by_cases hqt : (q : ℝ≥0) < t
        · have hfun : protterTailRatioENNReal A C p q t = fun w ↦
              ENNReal.ofReal (A t w - A (q : ℝ≥0) w) /
                ENNReal.ofReal (C t w - C (q : ℝ≥0) w) := by
            funext w
            simp [protterTailRatioENNReal, hpq, hqt, protterIncrementRatioENNReal]
          rw [hfun]
          change @Measurable Ω ℝ≥0∞ (F t) ENNReal.measurableSpace
            ((fun w ↦ ENNReal.ofReal (A t w - A (q : ℝ≥0) w)) /
              fun w ↦ ENNReal.ofReal (C t w - C (q : ℝ≥0) w))
          exact (((hA t).sub ((hA (q : ℝ≥0)).mono (F.mono hqt.le) le_rfl)).ennreal_ofReal).div
            (((hC t).sub ((hC (q : ℝ≥0)).mono (F.mono hqt.le) le_rfl)).ennreal_ofReal)
        · have hfun : protterTailRatioENNReal A C p q t = fun _ ↦ ∞ := by
            funext w
            simp [protterTailRatioENNReal, hpq, hqt]
          rw [hfun]
          exact measurable_const
      · have hfun : protterTailRatioENNReal A C p q t = fun _ ↦ ∞ := by
          funext w
          simp [protterTailRatioENNReal, hpq]
        rw [hfun]
        exact measurable_const
    · simpa only [hpt, if_false] using
        (measurable_const : @Measurable Ω ℝ≥0∞ (F t) ENNReal.measurableSpace (fun _ ↦ 0))

theorem adapted_protterDensity {A C : ℝ≥0 → Ω → ℝ}
    (hA : Adapted F A) (hC : Adapted F C) :
    Adapted F (protterDensity A C) :=
  fun t ↦ (adapted_protterDensityENNReal hA hC t).ennreal_toReal

/-- Adapted right-continuous inputs give the jointly measurable, adapted
source density without separately assuming product measurability. -/
theorem measurable_adapted_protterDensity_of_rightContinuous
    {A C : ℝ≥0 → Ω → ℝ}
    (hA : Adapted F A) (hC : Adapted F C)
    (hrA : ∀ w, IsRightContinuousPath (fun t ↦ A t w))
    (hrC : ∀ w, IsRightContinuousPath (fun t ↦ C t w)) :
    Measurable (uncurry (protterDensity A C)) ∧ Adapted F (protterDensity A C) := by
  have hmA : Measurable (uncurry A) :=
    hA.stronglyAdapted.isProductMeasurable_of_rightContinuous hrA
  have hmC : Measurable (uncurry C) :=
    hC.stronglyAdapted.isProductMeasurable_of_rightContinuous hrC
  exact ⟨measurable_protterDensity hmA hmC, adapted_protterDensity hA hC⟩

end Adapted

section Bounds

variable {A C : ℝ≥0 → Ω → ℝ}

private theorem protterIncrementRatioENNReal_le_one
    (hCA : ∀ w, Monotone (fun t ↦ C t w - A t w))
    (w : Ω) {r : ℚ≥0} {t : ℝ≥0} (hrt : (r : ℝ≥0) ≤ t) :
    protterIncrementRatioENNReal A C r t w ≤ 1 := by
  rw [protterIncrementRatioENNReal]
  apply ENNReal.div_le_of_le_mul'
  simp only [mul_one]
  apply ENNReal.ofReal_le_ofReal
  have h := hCA w hrt
  dsimp only at h
  linarith

theorem protterPositiveDensityENNReal_le_one
    (hCA : ∀ w, Monotone (fun t ↦ C t w - A t w))
    (t : ℝ≥0) (w : Ω) :
    protterPositiveDensityENNReal A C t w ≤ 1 := by
  apply iSup_le
  intro p
  by_cases hpt : (p : ℝ≥0) < t
  · rw [if_pos hpt]
    calc
      protterLowerSlopeENNReal A C p t w ≤
          protterTailRatioENNReal A C p p t w := iInf_le _ p
      _ = protterIncrementRatioENNReal A C p t w := by
        simp [protterTailRatioENNReal, hpt]
      _ ≤ 1 := protterIncrementRatioENNReal_le_one hCA w hpt.le
  · simp [hpt]

theorem protterDensityENNReal_le_one
    (hCA : ∀ w, Monotone (fun t ↦ C t w - A t w))
    (hAC0 : ∀ w, A 0 w ≤ C 0 w)
    (t : ℝ≥0) (w : Ω) :
    protterDensityENNReal A C t w ≤ 1 := by
  by_cases ht : t = 0
  · rw [ht, protterDensityENNReal, if_pos rfl]
    apply ENNReal.div_le_of_le_mul'
    simpa only [mul_one] using ENNReal.ofReal_le_ofReal (hAC0 w)
  · rw [protterDensityENNReal, if_neg ht]
    exact protterPositiveDensityENNReal_le_one hCA t w

theorem protterDensity_mem_Icc
    (hCA : ∀ w, Monotone (fun t ↦ C t w - A t w))
    (_hA0 : ∀ w, 0 ≤ A 0 w) (hAC0 : ∀ w, A 0 w ≤ C 0 w)
    (t : ℝ≥0) (w : Ω) :
    protterDensity A C t w ∈ Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hle := protterDensityENNReal_le_one hCA hAC0 t w
  have htop : protterDensityENNReal A C t w ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  simpa only [protterDensity, ENNReal.toReal_one] using
    (ENNReal.toReal_le_toReal htop ENNReal.one_ne_top).2 hle

end Bounds

end ProbabilityTheory

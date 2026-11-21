/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilyDirected
public import StochLean.ForMathlib.MeasureTheory.ConditionalOrder

/-! # Conditional bounds for directed essential suprema

The existing essential-supremum relation persists on a measurable restriction.
Testing on events in the conditioning sigma-field then passes conditional
upper bounds from an almost-surely directed family to its actual integrable
essential supremum. No pointwise interchange of conditional expectation and
an arbitrary supremum, or uncountable intersection of null events, is used.
-/

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {f : ι → Ω → ℝ≥0∞} {W : Ω → ℝ≥0∞}

/-- Restricting to a measurable event preserves the actual essential-family
supremum. The comparison functions in its minimality property remain arbitrary. -/
theorem IsAEFamilySupremum.restrict (hW : IsAEFamilySupremum P f W)
    {A : Set Ω} (hA : MeasurableSet A) : IsAEFamilySupremum (P.restrict A) f W := by
  classical
  refine ⟨hW.measurable, fun i ↦ ae_restrict_of_ae (hW.le_ae i), fun g hg ↦ ?_⟩
  let b : Ω → ℝ≥0∞ := fun ω ↦ if ω ∈ A then g ω else W ω
  have hb : W ≤ᵐ[P] b := by
    apply hW.ae_le b
    intro i
    filter_upwards [(ae_restrict_iff' hA).mp (hg i), hW.le_ae i] with ω hgω hwω
    by_cases hω : ω ∈ A
    · simpa only [b, if_pos hω] using hgω hω
    · simpa only [b, if_neg hω] using hwω
  filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem hA] with ω hbω hω
  simpa only [b, if_pos hω] using hbω

variable [IsFiniteMeasure P]

/-- An integrable directed essential supremum satisfies every common
conditional upper bound of its real coordinates. Nonnegativity of the bound
also covers the empty family, whose essential supremum is zero. -/
theorem IsAEFamilySupremum.condExp_toReal_le_of_ae_directed
    (hW : IsAEFamilySupremum P f W) (hf : ∀ i, Measurable (f i))
    (hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P] v) f)
    (hfin : ∀ᵐ ω ∂P, W ω ≠ ∞) (hWi : Integrable (fun ω ↦ (W ω).toReal) P)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Z : Ω → ℝ}
    (hZm : StronglyMeasurable[m] Z) (hZi : Integrable Z P) (hZn : 0 ≤ᵐ[P] Z)
    (hb : ∀ i, P[(fun ω ↦ (f i ω).toReal) | m] ≤ᵐ[P] Z) :
    P[(fun ω ↦ (W ω).toReal) | m] ≤ᵐ[P] Z := by
  have hfi (i : ι) : Integrable (fun ω ↦ (f i ω).toReal) P := by
    apply hWi.mono' (hf i).ennreal_toReal.aestronglyMeasurable
    filter_upwards [hW.le_ae i, hfin] with ω hiω hfω
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
      ENNReal.toReal_mono hfω hiω
  have hffi (i : ι) : ∀ᵐ ω ∂P, f i ω ≠ ∞ := by
    filter_upwards [hW.le_ae i, hfin] with ω hiω hfω
    exact ne_top_of_le_ne_top hfω hiω
  have hset (A : Set Ω) (hA : MeasurableSet[m] A) :
      (∫ ω in A, (W ω).toReal ∂P) ≤ ∫ ω in A, Z ω ∂P := by
    have hAm : MeasurableSet[mΩ] A := hm A hA
    have hdir : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P.restrict A] v) f := by
      intro i j
      obtain ⟨k, hi, hj⟩ := hd i j
      exact ⟨k, ae_restrict_of_ae hi, ae_restrict_of_ae hj⟩
    have hbound (i : ι) : (∫⁻ ω in A, f i ω ∂P) ≤
        ENNReal.ofReal (∫ ω in A, Z ω ∂P) := by
      have he : ENNReal.ofReal (∫ ω in A, (f i ω).toReal ∂P) =
          ∫⁻ ω in A, f i ω ∂P := by
        rw [ofReal_integral_eq_lintegral_ofReal (hfi i).integrableOn
          (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)]
        exact lintegral_congr_ae ((ae_restrict_of_ae (hffi i)).mono
          fun _ hω ↦ ENNReal.ofReal_toReal hω)
      rw [← he, ← setIntegral_condExp hm (hfi i) hA]
      exact ENNReal.ofReal_le_ofReal
        (integral_mono_ae integrable_condExp.integrableOn hZi.integrableOn
          (ae_restrict_of_ae (hb i)))
    have hh := (hW.restrict hAm).lintegral_le_of_ae_directed hf hdir hbound
    rw [integral_toReal hW.measurable.aemeasurable
      ((ae_restrict_of_ae hfin).mono fun _ hω ↦ hω.lt_top)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq
      (ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hZn)))
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le
    (Integrable.trim hm integrable_condExp stronglyMeasurable_condExp)
    (Integrable.trim hm hZi hZm)
  intro A hA _
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hA,
    ← setIntegral_trim hm hZm hA, setIntegral_condExp hm hWi hA]
  exact hset A hA

end MeasureTheory

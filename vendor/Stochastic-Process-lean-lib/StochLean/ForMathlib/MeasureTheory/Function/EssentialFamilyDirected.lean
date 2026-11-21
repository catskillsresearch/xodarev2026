/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilySupremum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Data.Finset.Order
public import Mathlib.Order.CompleteLattice.Finset

/-! # Integral bounds for almost-surely directed essential suprema

A finite maximum of a selected countable subfamily is bounded almost surely
by an actual member of the original directed family. Monotone convergence
over these finite maxima therefore preserves uniform integral bounds.
Directedness is only almost sure; no uncountable null-set intersection or
pointwise monotonicity of arbitrary representatives is required.
-/

@[expose] public section

open Filter Set Finset
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [SFinite μ]
  {f : ι → Ω → ℝ≥0∞} {W : Ω → ℝ≥0∞} {C : ℝ≥0∞}

/-- Uniform lower-integral bounds pass to the existing essential-supremum
relation for an almost-surely directed family, including the empty family. -/
theorem IsAEFamilySupremum.lintegral_le_of_ae_directed
    (hW : IsAEFamilySupremum μ f W) (hf : ∀ i, Measurable (f i))
    (hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[μ] v) f)
    (hb : ∀ i, (∫⁻ ω, f i ω ∂μ) ≤ C) : (∫⁻ ω, W ω ∂μ) ≤ C := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    have hh := hW.ae_le (fun _ ↦ 0) (fun i ↦ isEmptyElim i)
    exact (lintegral_mono_ae hh).trans (by simp)
  | inr hi =>
    let : IsTrans (Ω → ℝ≥0∞) (fun u v ↦ u ≤ᵐ[μ] v) :=
      ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩
    obtain ⟨I, hI, hdom⟩ := μ.exists_countable_subfamily_ae_le_iSup hf
    let : Countable I := hI.to_subtype
    let B (s : Finset I) (ω : Ω) := ⨆ i ∈ s, f i.1 ω
    have hm (s : Finset I) : Measurable (B s) :=
      Measurable.iSup fun i ↦ Measurable.iSup fun _ ↦ hf i.1
    have hdir : Directed (· ≤ ·) B := by
      intro s t
      refine ⟨s ∪ t, fun ω ↦ ?_, fun ω ↦ ?_⟩
      · exact iSup_le fun i ↦ iSup_le fun hi ↦
          le_iSup_of_le i (le_iSup_of_le (mem_union_left t hi) le_rfl)
      · exact iSup_le fun i ↦ iSup_le fun hi ↦
          le_iSup_of_le i (le_iSup_of_le (mem_union_right s hi) le_rfl)
    have hB (s : Finset I) : (∫⁻ ω, B s ω ∂μ) ≤ C := by
      obtain ⟨k, hk⟩ := hd.finset_le (s.image Subtype.val)
      have hh : B s ≤ᵐ[μ] f k := by
        have he (i : {i : I // i ∈ s}) : f i.1.1 ≤ᵐ[μ] f k :=
          hk _ (mem_image.mpr ⟨i.1, i.2, rfl⟩)
        filter_upwards [ae_all_iff.mpr he] with ω hω
        exact iSup_le fun i ↦ iSup_le fun hi ↦ hω ⟨i, hi⟩
      exact (lintegral_mono_ae hh).trans (hb k)
    have he := hW.ae_eq (isAEFamilySupremum_iSup_subtype hf hI hdom)
    calc
      (∫⁻ ω, W ω ∂μ) = ∫⁻ ω, ⨆ i : I, f i.1 ω ∂μ := lintegral_congr_ae he
      _ = ∫⁻ ω, ⨆ s : Finset I, B s ω ∂μ := by
        congr 1
        ext ω
        exact iSup_eq_iSup_finset (fun i : I ↦ f i.1 ω)
      _ = ⨆ s : Finset I, ∫⁻ ω, B s ω ∂μ :=
        lintegral_iSup_directed_of_measurable hm hdir
      _ ≤ C := iSup_le hB

/-- The lower integral of an almost-surely directed essential supremum is
exactly the supremum of the original family's lower integrals. -/
theorem IsAEFamilySupremum.lintegral_eq_iSup_of_ae_directed
    (hW : IsAEFamilySupremum μ f W) (hf : ∀ i, Measurable (f i))
    (hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[μ] v) f) :
    (∫⁻ ω, W ω ∂μ) = ⨆ i, ∫⁻ ω, f i ω ∂μ := by
  apply le_antisymm
  · exact hW.lintegral_le_of_ae_directed hf hd
      (fun i ↦ le_iSup (fun j : ι ↦ ∫⁻ ω, f j ω ∂μ) i)
  · exact iSup_le fun i ↦ lintegral_mono_ae (hW.le_ae i)

/-- Finiteness is established before converting an extended essential
supremum to a real integrable random variable. -/
theorem IsAEFamilySupremum.ae_ne_top_and_integrable_toReal_of_ae_directed
    (hW : IsAEFamilySupremum μ f W) (hf : ∀ i, Measurable (f i))
    (hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[μ] v) f)
    (hb : ∀ i, (∫⁻ ω, f i ω ∂μ) ≤ C) (hC : C ≠ ∞) :
    (∀ᵐ ω ∂μ, W ω ≠ ∞) ∧ Integrable (fun ω ↦ (W ω).toReal) μ := by
  have hfin : (∫⁻ ω, W ω ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hC (hW.lintegral_le_of_ae_directed hf hd hb)
  exact ⟨(ae_lt_top hW.measurable hfin).mono fun _ hω ↦ hω.ne,
    integrable_toReal_of_lintegral_ne_top hW.measurable.aemeasurable hfin⟩

end MeasureTheory

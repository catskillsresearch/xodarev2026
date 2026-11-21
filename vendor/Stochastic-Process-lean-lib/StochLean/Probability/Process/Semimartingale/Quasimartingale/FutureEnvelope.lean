/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.HorizonComparison

/-! # Actual conditional envelopes over the whole future

All finite future horizons and their actual partitions index the family.
Adaptedness, terminal-tail extension, and common refinement establish its
almost-sure directedness. Countable essential subfamilies construct versions
measurable at the requested time on the original measure.

Both signs have integral bound given by the original whole-half-line conditional
variation, without a shifted-quasimartingale assumption. Finiteness of that
actual owner establishes almost-sure finiteness before real conversion and
gives genuine L1 random variables. This is a fixed-time construction, not yet
a supermartingale or cadlag Rao decomposition.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Negation preserves the existing whole-half-line conditional variation,
including the artificial terminal-zero tail. No integrability is assumed. -/
theorem eConditionalVariation_neg_eq :
    eConditionalVariation (-X) F P = eConditionalVariation X F P := by
  unfold eConditionalVariation
  apply iSup_congr
  intro H
  apply iSup_congr
  intro π
  have he (i : Fin π.size) :
      P[(-X) (π.left i) - (-X) (π.right i) | F (π.left i)] =ᵐ[P]
        -P[X (π.left i) - X (π.right i) | F (π.left i)] := by
    have hid : (-X) (π.left i) - (-X) (π.right i) =
        -(X (π.left i) - X (π.right i)) := by
      ext ω
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    rw [hid]
    exact condExp_neg _ _
  unfold eConditionalVariationOnPartition
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  simp only [Pi.neg_apply] at hω
  simp only [conditionalVariationSum, Pi.neg_apply, hω, abs_neg, sub_zero]

variable [IsFiniteMeasure P]

/-- An actual positive conditional envelope over all finite future horizons
at time zero, bounded in integral by the existing global variation owner. -/
theorem exists_positive_futureEnvelope (ha : Adapted F X)
    (hi : ∀ t, Integrable (X t) P) :
    let f : (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ := fun p ω ↦ ENNReal.ofReal
      (P[(fun ω ↦
        (∑ i, max (P[X (p.2.left i) - X (p.2.right i) | F (p.2.left i)] ω) 0) +
          max (X p.1 ω) 0) | F 0] ω)
    ∃ W : Ω → ℝ≥0∞, Measurable[F 0] W ∧ IsAEFamilySupremum P f W ∧
      (∫⁻ ω, W ω ∂P) ≤ eConditionalVariation X F P ∧
      (HasFiniteConditionalVariation X F P →
        (∀ᵐ ω ∂P, W ω ≠ ∞) ∧ Integrable (fun ω ↦ (W ω).toReal) P) := by
  classical
  dsimp only
  let f : (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ := fun p ω ↦ ENNReal.ofReal
    (P[(fun ω ↦
      (∑ i, max (P[X (p.2.left i) - X (p.2.right i) | F (p.2.left i)] ω) 0) +
        max (X p.1 ω) 0) | F 0] ω)
  have hm (p : Σ H : ℝ≥0, TimePartition H) : Measurable[F 0] (f p) :=
    stronglyMeasurable_condExp.measurable.ennreal_ofReal
  have hma (p : Σ H : ℝ≥0, TimePartition H) : Measurable (f p) :=
    (hm p).mono (F.le 0) le_rfl
  have hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P] v) f :=
    directed_positive_conditional_decrements_all_horizons ha hi
  have hb (p : Σ H : ℝ≥0, TimePartition H) :
      (∫⁻ ω, f p ω ∂P) ≤ eConditionalVariation X F P := by
    obtain ⟨V, _, hV, hbV, _⟩ := exists_positive_partitionEnvelope (F := F) hi p.1
    exact (lintegral_mono_ae (hV.le_ae p.2)).trans
      (hbV.trans (iSup_le fun π ↦ eConditionalVariationOnPartition_le π))
  obtain ⟨I, hI, hdom⟩ := P.exists_countable_subfamily_ae_le_iSup hma
  let : Countable I := hI.to_subtype
  let W : Ω → ℝ≥0∞ := fun ω ↦ ⨆ i : I, f i.1 ω
  have hW : IsAEFamilySupremum P f W := isAEFamilySupremum_iSup_subtype hma hI hdom
  exact ⟨W, Measurable.iSup (fun i : I ↦ hm i.1), hW,
    hW.lintegral_le_of_ae_directed hma hd hb,
    hW.ae_ne_top_and_integrable_toReal_of_ae_directed hma hd hb⟩

/-- At any fixed time, actual positive and negative whole-future envelopes
have the original process's global conditional-variation integral bound.
No future terminal value, shifted finiteness, or candidate envelope is input. -/
theorem exists_future_positive_negative_partitionEnvelopes
    (ha : Adapted F X) (hi : ∀ s, Integrable (X s) P) (t : ℝ≥0) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
    let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
    let f (Z : ℝ≥0 → Ω → ℝ) : (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ :=
      fun p ω ↦ ENNReal.ofReal
        (P[(fun ω ↦
          (∑ i, max (P[Z (p.2.left i) - Z (p.2.right i) | G (p.2.left i)] ω) 0) +
            max (Z p.1 ω) 0) | G 0] ω)
    ∃ Wp Wn : Ω → ℝ≥0∞,
      Measurable[F t] Wp ∧ Measurable[F t] Wn ∧
      IsAEFamilySupremum P (f Y) Wp ∧ IsAEFamilySupremum P (f (-Y)) Wn ∧
      (∫⁻ ω, Wp ω ∂P) ≤ eConditionalVariation X F P ∧
      (∫⁻ ω, Wn ω ∂P) ≤ eConditionalVariation X F P ∧
      (HasFiniteConditionalVariation X F P →
        (∀ᵐ ω ∂P, Wp ω ≠ ∞ ∧ Wn ω ≠ ∞) ∧
        Integrable (fun ω ↦ (Wp ω).toReal) P ∧
        Integrable (fun ω ↦ (Wn ω).toReal) P) := by
  dsimp only
  let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
  let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
  have haY : Adapted G Y := fun s ↦ ha (t + s)
  have hiY (s : ℝ≥0) : Integrable (Y s) P := hi (t + s)
  obtain ⟨Wp, hmp, hp, hbp, hfp⟩ := exists_positive_futureEnvelope haY hiY
  obtain ⟨Wn, hmn, hn, hbn, hfn⟩ :=
    exists_positive_futureEnvelope (X := -Y) haY.neg (fun s ↦ (hiY s).neg)
  rw [eConditionalVariation_neg_eq] at hbn
  have hshift : eConditionalVariation Y G P ≤ eConditionalVariation X F P :=
    eConditionalVariation_shift_le t
  have hGzero : G 0 = F t := by
    change F (t + 0) = F t
    rw [add_zero]
  rw [hGzero] at hmp hmn
  refine ⟨Wp, Wn, hmp, hmn, hp, hn, hbp.trans hshift, hbn.trans hshift, ?_⟩
  intro hfin
  have hfinY : HasFiniteConditionalVariation Y G P := ne_top_of_le_ne_top hfin hshift
  have hfinNeg : HasFiniteConditionalVariation (-Y) G P := by
    unfold HasFiniteConditionalVariation
    rw [eConditionalVariation_neg_eq]
    exact hfinY
  obtain ⟨hfWp, hiWp⟩ := hfp hfinY
  obtain ⟨hfWn, hiWn⟩ := hfn hfinNeg
  exact ⟨hfWp.and hfWn, hiWp, hiWn⟩

end ProbabilityTheory

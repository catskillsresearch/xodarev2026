/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilyDirected
public import StochLean.Analysis.PathVariation.CommonRefinement
public import StochLean.Probability.Process.Semimartingale.Quasimartingale.Refinement
public import StochLean.Probability.Process.Filtration.Reindex

/-! # Actual directed partition envelopes on a fixed future horizon

The family consists of initial conditional expectations of positive conditional
decrements and their positive terminal-zero tail. Common refinements give actual
almost-sure directedness. The existing essential-family-supremum relation then
constructs a version measurable at the initial time, on the original measure.

At an arbitrary fixed time, deterministic reindexing gives positive and negative
envelopes over a fixed future horizon. Their integral bounds use the actual
conditional variation of that shifted process; no shifted quasimartingale,
candidate envelope, convergence certificate, or Rao decomposition is assumed.
Finiteness and real integrability follow when this actual bound is finite.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {H : ℝ≥0}

/-- Positive partition decrements are directed in almost-sure order after
conditioning at time zero. The terminal-zero tail is included. -/
theorem directed_positive_conditional_decrements
    (hi : ∀ t, Integrable (X t) P) :
    Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P] v)
      (fun π : TimePartition H ↦ fun ω ↦ ENNReal.ofReal
        (P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
          max (X H ω) 0) | F 0] ω)) := by
  intro π ρ
  refine ⟨π.commonRefinement ρ, ?_, ?_⟩
  · exact (condExp_positive_conditional_decrements_le_of_refines hi
      (π.commonRefinement_refines_left ρ)).mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω
  · exact (condExp_positive_conditional_decrements_le_of_refines hi
      (π.commonRefinement_refines_right ρ)).mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω

private theorem lintegral_positive_conditional_decrements_le
    (hi : ∀ t, Integrable (X t) P) (π : TimePartition H) :
    (∫⁻ ω, ENNReal.ofReal
      (P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
        max (X H ω) 0) | F 0] ω) ∂P) ≤ eConditionalVariationOnPartition X F P π := by
  let B (ω : Ω) :=
    (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) + max (X H ω) 0
  have hB : Integrable B P :=
    (integrable_finsetSum Finset.univ (fun i _ ↦
      (integrable_condExp (f := X (π.left i) - X (π.right i))
        (m := F (π.left i))).sup (integrable_zero _ _ _))).add
      ((hi H).sup (integrable_zero _ _ _))
  have hBn (ω : Ω) : 0 ≤ B ω :=
    add_nonneg (sum_nonneg fun _ _ ↦ le_max_right _ _) (le_max_right _ _)
  have hle (ω : Ω) : B ω ≤ conditionalVariationSum X F P π ω := by
    apply add_le_add
    · exact sum_le_sum fun _ _ ↦ max_le (le_abs_self _) (abs_nonneg _)
    · simpa only [sub_zero] using max_le (le_abs_self (X H ω)) (abs_nonneg (X H ω))
  change (∫⁻ ω, ENNReal.ofReal (P[B | F 0] ω) ∂P) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_condExp
    (condExp_nonneg (Eventually.of_forall hBn)), integral_condExp (F.le 0),
    eConditionalVariationOnPartition_eq_ofReal_integral hi]
  exact ENNReal.ofReal_le_ofReal
    (integral_mono_ae hB (integrable_conditionalVariationSum hi π) (Eventually.of_forall hle))

/-- An actual positive partition envelope, measurable at time zero on the
original measure, with the fixed-horizon conditional-variation integral bound. -/
theorem exists_positive_partitionEnvelope (hi : ∀ t, Integrable (X t) P) (H : ℝ≥0) :
    let f : TimePartition H → Ω → ℝ≥0∞ := fun π ω ↦ ENNReal.ofReal
      (P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
        max (X H ω) 0) | F 0] ω)
    let C := ⨆ π : TimePartition H, eConditionalVariationOnPartition X F P π
    ∃ W : Ω → ℝ≥0∞, Measurable[F 0] W ∧ IsAEFamilySupremum P f W ∧
      (∫⁻ ω, W ω ∂P) ≤ C ∧
      (C ≠ ∞ → (∀ᵐ ω ∂P, W ω ≠ ∞) ∧ Integrable (fun ω ↦ (W ω).toReal) P) := by
  classical
  dsimp only
  let f : TimePartition H → Ω → ℝ≥0∞ := fun π ω ↦ ENNReal.ofReal
    (P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
      max (X H ω) 0) | F 0] ω)
  have hm (π : TimePartition H) : Measurable[F 0] (f π) :=
    stronglyMeasurable_condExp.measurable.ennreal_ofReal
  have hma (π : TimePartition H) : Measurable (f π) := (hm π).mono (F.le 0) le_rfl
  have hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P] v) f :=
    directed_positive_conditional_decrements hi
  have hb (π : TimePartition H) : (∫⁻ ω, f π ω ∂P) ≤
      ⨆ ρ : TimePartition H, eConditionalVariationOnPartition X F P ρ :=
    (lintegral_positive_conditional_decrements_le hi π).trans (le_iSup _ π)
  obtain ⟨I, hI, hdom⟩ := P.exists_countable_subfamily_ae_le_iSup hma
  let : Countable I := hI.to_subtype
  let W : Ω → ℝ≥0∞ := fun ω ↦ ⨆ i : I, f i.1 ω
  have hW : IsAEFamilySupremum P f W := isAEFamilySupremum_iSup_subtype hma hI hdom
  exact ⟨W, Measurable.iSup (fun i : I ↦ hm i.1), hW,
    hW.lintegral_le_of_ae_directed hma hd hb,
    hW.ae_ne_top_and_integrable_toReal_of_ae_directed hma hd hb⟩

omit [IsFiniteMeasure P] in
private theorem eConditionalVariationOnPartition_neg_eq (π : TimePartition H) :
    eConditionalVariationOnPartition (-X) F P π =
      eConditionalVariationOnPartition X F P π := by
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

/-- Positive and negative envelopes of actual future partitions, at any fixed
time and finite horizon. Their common bound is an actual shifted variation,
not an extra shifted-quasimartingale or finiteness premise. -/
theorem exists_fixedTime_positive_negative_partitionEnvelopes
    (hi : ∀ t, Integrable (X t) P) (t H : ℝ≥0) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
    let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
    let f (Z : ℝ≥0 → Ω → ℝ) : TimePartition H → Ω → ℝ≥0∞ := fun π ω ↦ ENNReal.ofReal
      (P[(fun ω ↦ (∑ i, max (P[Z (π.left i) - Z (π.right i) | G (π.left i)] ω) 0) +
        max (Z H ω) 0) | G 0] ω)
    let C := ⨆ π : TimePartition H, eConditionalVariationOnPartition Y G P π
    ∃ Wp Wn : Ω → ℝ≥0∞,
      Measurable[F t] Wp ∧ Measurable[F t] Wn ∧
      IsAEFamilySupremum P (f Y) Wp ∧ IsAEFamilySupremum P (f (-Y)) Wn ∧
      (∫⁻ ω, Wp ω ∂P) ≤ C ∧ (∫⁻ ω, Wn ω ∂P) ≤ C ∧
      (C ≠ ∞ → (∀ᵐ ω ∂P, Wp ω ≠ ∞ ∧ Wn ω ≠ ∞) ∧
        Integrable (fun ω ↦ (Wp ω).toReal) P ∧
        Integrable (fun ω ↦ (Wn ω).toReal) P) := by
  dsimp only
  let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
  let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
  have hiY (s : ℝ≥0) : Integrable (Y s) P := hi (t + s)
  obtain ⟨Wp, hmp, hp, hbp, hfp⟩ := exists_positive_partitionEnvelope (F := G) hiY H
  obtain ⟨Wn, hmn, hn, hbn, hfn⟩ :=
    exists_positive_partitionEnvelope (X := -Y) (F := G) (fun s ↦ (hiY s).neg) H
  have he : (⨆ π : TimePartition H, eConditionalVariationOnPartition (-Y) G P π) =
      ⨆ π : TimePartition H, eConditionalVariationOnPartition Y G P π := by
    simp_rw [eConditionalVariationOnPartition_neg_eq]
  rw [he] at hbn hfn
  have hGzero : G 0 = F t := by
    change F (t + 0) = F t
    rw [add_zero]
  rw [hGzero] at hmp hmn
  refine ⟨Wp, Wn, hmp, hmn, hp, hn, hbp, hbn, ?_⟩
  intro hC
  obtain ⟨hfWp, hiWp⟩ := hfp hC
  obtain ⟨hfWn, hiWn⟩ := hfn hC
  exact ⟨hfWp.and hfWn, hiWp, hiWn⟩

end ProbabilityTheory

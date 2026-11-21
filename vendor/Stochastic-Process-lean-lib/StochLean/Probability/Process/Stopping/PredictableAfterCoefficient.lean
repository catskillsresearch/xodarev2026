/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingStability
public import StochLean.Probability.Process.Stopping.Graph

/-! # Revealing predictable stopped information at its lifetime

A predictable lifetime has a predictable closed-future region. The source
announcing convention only gives almost-sure convergence; initial completeness
repairs the exceptional paths without changing the original lifetime or its
finite-time graph. Right continuity of the filtration and finiteness of the
measure are not needed.

A coefficient measurable strictly before this lifetime can be revealed at and
after it to obtain an actual strongly predictable process. The proof uses the
before-field generators on the closed-future region, and does not regard the
coefficient as initial information. At lifetime zero the coefficient is already
initial information. At infinite lifetime every finite-time value is zero,
regardless of the coefficient there; no value of a process at infinity is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

private theorem measurableSet_predictable_univ_prod_initial {A : Set Ω}
    (hA : MeasurableSet[F 0] A) :
    MeasurableSet[F.predictable] ((univ : Set ℝ≥0) ×ˢ A) := by
  have he : (univ : Set ℝ≥0) ×ˢ A = ({0} ×ˢ A) ∪ (Ioi 0 ×ˢ A) := by
    ext ⟨t, ω⟩
    simp only [mem_prod, mem_univ, true_and, mem_union, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h ↦ (eq_or_lt_of_le (show 0 ≤ t from bot_le)).elim
      (fun ht ↦ Or.inl ⟨ht.symm, h⟩) (fun ht ↦ Or.inr ⟨ht, h⟩),
      fun h ↦ h.elim And.right And.right⟩
  rw [he]
  exact (measurableSet_predictable_singleton_bot_prod hA).union
    (measurableSet_predictable_Ioi_prod hA)

private theorem measurable_predictable_fst :
    Measurable[F.predictable] (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := by
  apply measurable_of_Ioi
  intro t
  simpa only [prod_univ] using
    measurableSet_predictable_Ioi_prod (𝓕 := F) (i := t) MeasurableSet.univ

private theorem measurable_predictable_snd_initial :
    @Measurable (ℝ≥0 × Ω) Ω F.predictable (F 0) Prod.snd := by
  intro A hA
  simpa only [univ_prod] using measurableSet_predictable_univ_prod_initial hA

/-- The actual closed future of a predictable time is predictable. Completeness
is needed only to retain the original lifetime on exceptional announcing paths. -/
theorem IsPredictableStoppingTime.measurableSet_predictable_le
    (hτ : IsPredictableStoppingTime F τ P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[F.predictable]
      {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} := by
  classical
  obtain ⟨σ, hσ, _⟩ := hτ.exists_announcing_le
  let bad : Set Ω := {ω | ¬ Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))}
  have hbad : MeasurableSet[F 0] bad := hc0 bad (ae_iff.mp hσ.tendsto)
  let τbad : Ω → WithTop ℝ≥0 := fun ω ↦ if ω ∈ bad then τ ω else ⊤
  have heBad : (fun _ : Ω ↦ (⊤ : WithTop ℝ≥0)) =ᵐ[P] τbad := by
    filter_upwards [hσ.tendsto] with ω hω
    simp [τbad, bad, hω]
  have hmBad : Measurable[F 0] τbad := hc0.measurable_congr_ae measurable_const heBad
  have hmBadFuture : MeasurableSet[F.predictable]
      {p : ℝ≥0 × Ω | τbad p.2 ≤ (p.1 : WithTop ℝ≥0)} :=
    measurableSet_le (hmBad.comp measurable_predictable_snd_initial)
      (WithTop.continuous_coe.measurable.comp measurable_predictable_fst)
  have hzero : MeasurableSet[F 0] {ω | τ ω = 0} := by
    have he : {ω | τ ω = 0} = {ω | τ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h bot_le⟩
    rw [he]
    exact hτ.1 0
  have he : {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} =
      {p : ℝ≥0 × Ω | τbad p.2 ≤ (p.1 : WithTop ℝ≥0)} ∪
      (((univ : Set ℝ≥0) ×ˢ badᶜ) ∩
        (((univ : Set ℝ≥0) ×ˢ {ω | τ ω = 0}) ∪
          ⋂ n : ℕ, {p : ℝ≥0 × Ω | σ n p.2 < (p.1 : WithTop ℝ≥0)})) := by
    ext ⟨t, ω⟩
    by_cases hω : ω ∈ bad
    · simp [τbad, hω]
    · have hlim : Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) := by
        simpa only [bad, mem_ofPred_eq, not_not] using hω
      have hgood : τ ω ≤ (t : WithTop ℝ≥0) ↔
          τ ω = 0 ∨ ∀ n, σ n ω < (t : WithTop ℝ≥0) := by
        constructor
        · intro hle
          by_cases hz : τ ω = 0
          · exact Or.inl hz
          · exact Or.inr fun n ↦
              (hσ.strict n ω (lt_of_le_of_ne bot_le (Ne.symm hz))).trans_le hle
        · rintro (hz | hlt)
          · rw [hz]
            exact bot_le
          · exact le_of_tendsto hlim (Eventually.of_forall fun n ↦ (hlt n).le)
      simpa only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_prod, mem_univ,
        mem_compl_iff, hω, not_false_eq_true, true_and, mem_iInter, τbad, if_false,
        top_le_iff, WithTop.coe_ne_top, false_or] using hgood
  rw [he]
  exact hmBadFuture.union
    ((measurableSet_predictable_univ_prod_initial hbad.compl).inter
      ((measurableSet_predictable_univ_prod_initial hzero).union
        (MeasurableSet.iInter fun n ↦ (hσ.isStoppingTime n).measurableSet_predictable_lt)))

/-- Predictable lifetimes have predictable finite-time graphs, including their
zero-time graph and excluding infinite lifetime. -/
theorem IsPredictableStoppingTime.measurableSet_predictable_graph
    (hτ : IsPredictableStoppingTime F τ P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[F.predictable] (stoppingTimeGraph τ) := by
  have he : stoppingTimeGraph τ =
      {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} \
        {p : ℝ≥0 × Ω | τ p.2 < (p.1 : WithTop ℝ≥0)} := by
    ext p
    simp only [mem_stoppingTimeGraph, Set.mem_sdiff, mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨h.le, not_lt_of_ge h.ge⟩,
      fun h ↦ le_antisymm h.1 (le_of_not_gt h.2)⟩
  rw [he]
  exact (hτ.measurableSet_predictable_le hc0).diff hτ.1.measurableSet_predictable_lt

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

/-- Information measurable strictly before a predictable lifetime can be
revealed at that lifetime as an actual strongly predictable closed-step process. -/
theorem StronglyMeasurable.isStronglyPredictable_indicator_stoppingTime_le
    (hτ : IsPredictableStoppingTime F τ P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[hτ.1.measurableSpaceBefore] Z) :
    IsStronglyPredictable F
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) := by
  classical
  let U : Set (ℝ≥0 × Ω) := {p | τ p.2 ≤ (p.1 : WithTop ℝ≥0)}
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hU : MeasurableSet U := hτ.measurableSet_predictable_le hc0
  have hg : @Measurable U Ω _ hτ.1.measurableSpaceBefore (fun p ↦ p.val.2) := by
    apply Measurable.of_le_map
    change F 0 ⊔ MeasurableSpace.generateFrom _ ≤ _
    refine sup_le ?_ (MeasurableSpace.generateFrom_le ?_)
    · intro A hA
      change MeasurableSet ((fun p : U ↦ p.val.2) ⁻¹' A)
      simpa only [univ_prod, preimage_preimage, Function.comp_def] using
        measurable_subtype_coe (measurableSet_predictable_univ_prod_initial hA)
    · rintro _ ⟨s, A, hA, rfl⟩
      change MeasurableSet
        ((fun p : U ↦ p.val.2) ⁻¹' (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}))
      have he : (fun p : U ↦ p.val.2) ⁻¹' (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}) =
          (Subtype.val : U → ℝ≥0 × Ω) ⁻¹'
            (Ioi s ×ˢ (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω})) := by
        ext p
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioi]
        exact ⟨fun h ↦ ⟨WithTop.coe_lt_coe.mp (h.2.trans_le p.property), h⟩,
          fun h ↦ h.2⟩
      rw [he]
      exact measurable_subtype_coe
        (measurableSet_predictable_Ioi_prod (hA.inter (hτ.1.measurableSet_gt s)))
  change StronglyMeasurable (U.indicator (fun p : ℝ≥0 × Ω ↦ Z p.2))
  apply stronglyMeasurable_of_restrict_of_restrict_compl hU
  · have he : U.domRestrict (U.indicator (fun p : ℝ≥0 × Ω ↦ Z p.2)) =
        (fun p : U ↦ Z p.val.2) := by
      funext p
      exact indicator_of_mem p.property _
    rw [he]
    exact hZ.comp_measurable hg
  · have he : Uᶜ.domRestrict (U.indicator (fun p : ℝ≥0 × Ω ↦ Z p.2)) =
        (fun _ : (Uᶜ : Set (ℝ≥0 × Ω)) ↦ (0 : ℝ)) := by
      funext p
      exact indicator_of_notMem p.property _
    rw [he]
    exact stronglyMeasurable_const

end MeasureTheory

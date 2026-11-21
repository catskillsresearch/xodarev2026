/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Equivalence
public import StochLean.Probability.Process.Measurability.ProgressiveSigma
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.PiSystem

/-!
# Strictness of progressive measurability

This is the diagonal example immediately following the definitions in Protter III.1.
The ambient sample sigma-field is the full sigma-field on `ℝ`, while the filtration
is constantly the countable--cocountable sigma-field.  The process

`X t ω = 1` if `(t : ℝ) = ω`, and `0` otherwise

is adapted and product measurable, but is not progressive.  Under any diffuse law
it nevertheless has the progressively measurable zero process as a modification.

The non-progressiveness proof is internal.  A measurable subset of a product whose
second sigma-field is countable--cocountable has identical first-coordinate sections
outside one countable exceptional set; the diagonal over `[0,1]` violates this.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace StochLean.ProgressiveStrict

/-- The countable--cocountable sigma-field on an arbitrary type. -/
@[instance_reducible]
def countableCocountable (α : Type*) : MeasurableSpace α where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl := by
    intro s hs
    rcases hs with hs | hs
    · exact Or.inr (by simpa only [compl_compl] using hs)
    · exact Or.inl hs
  measurableSet_iUnion := by
    classical
    intro f hf
    by_cases h : ∃ n, ¬ (f n).Countable
    · obtain ⟨n, hn⟩ := h
      rcases hf n with hfn | hfn
      · exact (hn hfn).elim
      · refine Or.inr (hfn.mono ?_)
        intro x hx hxu
        exact hx (Set.mem_iUnion.mpr ⟨n, hxu⟩)
    · apply Or.inl
      apply Set.countable_iUnion
      intro n
      by_contra hn
      exact h ⟨n, hn⟩

theorem measurableSet_countableCocountable_iff {α : Type*} {s : Set α} :
    @MeasurableSet α (countableCocountable α) s ↔ s.Countable ∨ sᶜ.Countable :=
  Iff.rfl

/-- Product events with a countable--cocountable second coordinate have sections
which are all identical away from a countable set of second-coordinate points. -/
theorem measurableSet_prod_eventually_constant_sections
    {α β : Type*} [MeasurableSpace α] [mβ : MeasurableSpace β]
    (hcc : ∀ s : Set β, MeasurableSet s → s.Countable ∨ sᶜ.Countable)
    {A : Set (α × β)} (hA : MeasurableSet A) :
    ∃ C : Set β, C.Countable ∧
      ∀ y, y ∉ C → ∀ z, z ∉ C → ∀ x, ((x, y) ∈ A ↔ (x, z) ∈ A) := by
  induction A, hA using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
  | empty =>
      exact ⟨∅, Set.countable_empty, by simp⟩
  | basic A hA =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hA
      rcases hcc v hv with hv | hv
      · refine ⟨v, hv, ?_⟩
        intro y hy z hz x
        simp only [mem_prod]
        simp only [hy, hz, and_false]
      · refine ⟨vᶜ, hv, ?_⟩
        intro y hy z hz x
        have hyv : y ∈ v := by simpa only [mem_compl_iff, not_not] using hy
        have hzv : z ∈ v := by simpa only [mem_compl_iff, not_not] using hz
        simp only [mem_prod, hyv, hzv, and_true]
  | compl A hA ih =>
      obtain ⟨C, hC, hsections⟩ := ih
      refine ⟨C, hC, ?_⟩
      intro y hy z hz x
      simpa only [mem_compl_iff, not_iff_not] using hsections y hy z hz x
  | iUnion f hdisjoint hf ih =>
      choose C hC hsections using ih
      refine ⟨⋃ n, C n, Set.countable_iUnion hC, ?_⟩
      intro y hy z hz x
      have hyC (n : ℕ) : y ∉ C n := fun hyn ↦ hy (Set.mem_iUnion.mpr ⟨n, hyn⟩)
      have hzC (n : ℕ) : z ∉ C n := fun hzn ↦ hz (Set.mem_iUnion.mpr ⟨n, hzn⟩)
      simp only [mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, (hsections n y (hyC n) z (hzC n) x).mp hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, (hsections n y (hyC n) z (hzC n) x).mpr hn⟩

/-- Protter's point-generated filtration, embedded in the full ambient sigma-field. -/
def pointFiltration : Filtration ℝ≥0 (⊤ : MeasurableSpace ℝ) :=
  Filtration.const ℝ≥0 (countableCocountable ℝ) le_top

/-- The diagonal spike from Protter III.1. -/
noncomputable def diagonalSpike (t : ℝ≥0) (ω : ℝ) : ℝ :=
  if (t : ℝ) = ω then 1 else 0

/-- Each coordinate is a singleton indicator, hence the diagonal spike is adapted. -/
theorem diagonalSpike_adapted : Adapted pointFiltration diagonalSpike := by
  intro t
  have hs : @MeasurableSet ℝ (countableCocountable ℝ) {ω | (t : ℝ) = ω} := by
    apply measurableSet_countableCocountable_iff.mpr
    left
    simpa [eq_comm] using Set.countable_singleton (t : ℝ)
  exact measurable_const.indicator hs

/-- The diagonal is measurable for the ambient full sigma-field, so the process
is product measurable. -/
theorem diagonalSpike_isProductMeasurable :
    @IsProductMeasurable ℝ≥0 ℝ ℝ inferInstance (⊤ : MeasurableSpace ℝ) inferInstance
      diagonalSpike := by
  unfold IsProductMeasurable Function.uncurry diagonalSpike
  apply Measurable.ite
  · exact measurableSet_eq_fun (NNReal.continuous_coe.measurable.comp measurable_fst)
      ((measurable_id'' (show (inferInstance : MeasurableSpace ℝ) ≤ ⊤ from le_top)).comp
        measurable_snd)
  · exact measurable_const
  · exact measurable_const

/-- The diagonal restricted to a positive finite horizon is not measurable for
the time-Borel times countable--cocountable product sigma-field. -/
theorem not_measurable_diagonal_Iic_one :
    ¬ @MeasurableSet (Set.Iic (1 : ℝ≥0) × ℝ)
      (Subtype.instMeasurableSpace.prod (countableCocountable ℝ))
      {p | (p.1.1 : ℝ) = p.2} := by
  intro hdiag
  letI : MeasurableSpace ℝ := countableCocountable ℝ
  obtain ⟨C, hC, hsections⟩ := measurableSet_prod_eventually_constant_sections
    (fun s hs ↦ measurableSet_countableCocountable_iff.mp hs) hdiag
  have hinterval : ¬ (Set.Icc (0 : ℝ) 1).Countable := by
    rw [← Cardinal.le_aleph0_iff_set_countable,
      Cardinal.mk_Icc_real (by norm_num : (0 : ℝ) < 1), not_le]
    exact Cardinal.aleph0_lt_continuum
  have hex : ∃ y ∈ Set.Icc (0 : ℝ) 1, y ∉ C := by
    by_contra h
    apply hinterval
    refine hC.mono ?_
    intro y hy
    by_contra hyC
    exact h ⟨y, hy, hyC⟩
  obtain ⟨y, hy, hyC⟩ := hex
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ C ∪ {y} := by
    intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inl hzC
    · right
      let x : Set.Iic (1 : ℝ≥0) :=
        ⟨⟨y, hy.1⟩, by exact_mod_cast hy.2⟩
      have hxy : ((x, y) : Set.Iic (1 : ℝ≥0) × ℝ) ∈
          {p | (p.1.1 : ℝ) = p.2} := by
        change (x.1 : ℝ) = y
        rfl
      have hxz := (hsections y hyC z hzC x).mp hxy
      change (x.1 : ℝ) = z at hxz
      change z = y
      rw [← hxz]
      rfl
  exact hinterval ((hC.union (Set.countable_singleton y)).mono hsub)

/-- The Protter diagonal spike is not progressive.  Thus adaptedness plus product
measurability does not imply progressiveness of the process itself. -/
theorem diagonalSpike_not_progressive :
    ¬ IsProgressive pointFiltration diagonalSpike := by
  intro hprogressive
  have hm := hprogressive (1 : ℝ≥0)
  have hone : MeasurableSet ({1} : Set ℝ) := measurableSet_singleton 1
  have hpre := hm hone
  apply not_measurable_diagonal_Iic_one
  have heq : {q : Set.Iic (1 : ℝ≥0) × ℝ | (q.1.1 : ℝ) = q.2} =
      (fun q : Set.Iic (1 : ℝ≥0) × ℝ ↦ diagonalSpike q.1 q.2) ⁻¹' {1} := by
    apply Set.ext
    intro q
    change (q.1.1 : ℝ) = q.2 ↔
      (if (q.1.1 : ℝ) = q.2 then (1 : ℝ) else 0) = 1
    by_cases h : (q.1.1 : ℝ) = q.2 <;> simp [h]
  rw [heq]
  exact hpre

/-- For the point-generated filtration, the progressive sigma-field is strictly
smaller than the ambient product sigma-field. -/
theorem pointFiltration_progressive_lt_prod :
    pointFiltration.progressive <
      (inferInstance : MeasurableSpace ℝ≥0).prod (⊤ : MeasurableSpace ℝ) := by
  refine lt_of_le_of_ne pointFiltration.progressive_le_prod ?_
  intro hEq
  apply diagonalSpike_not_progressive
  apply (pointFiltration.measurable_progressive_iff).mp
  rw [hEq]
  exact diagonalSpike_isProductMeasurable

/-- Under a diffuse law, the zero process is a progressive modification of the
non-progressive diagonal spike.  This is the exact distinction required by the
general adapted-plus-product-measurable modification theorem. -/
theorem diagonalSpike_zero_modification
    (P : Measure ℝ) (hP : ∀ x : ℝ, P {x} = 0) :
    IsModification diagonalSpike (fun _ _ ↦ (0 : ℝ)) P := by
  intro t
  rw [Filter.EventuallyEq, ae_iff]
  have heq : {ω | diagonalSpike t ω ≠ 0} = {(t : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_singleton_iff]
    by_cases h : (t : ℝ) = ω
    · constructor
      · intro _
        exact h.symm
      · intro _
        simp [diagonalSpike, h]
    · constructor
      · intro hne
        exfalso
        apply hne
        simp [diagonalSpike, h]
      · intro hw
        exact (h hw.symm).elim
  rw [heq, hP]

theorem diagonalSpike_exists_progressive_modification
    (P : Measure ℝ) (hP : ∀ x : ℝ, P {x} = 0) :
    ∃ Y : ℝ≥0 → ℝ → ℝ, IsModification diagonalSpike Y P ∧
      IsProgressive pointFiltration Y := by
  refine ⟨fun _ _ ↦ 0, diagonalSpike_zero_modification P hP, ?_⟩
  exact MeasureTheory.isProgressive_const pointFiltration 0

end StochLean.ProgressiveStrict

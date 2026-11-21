/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalConstruction

/-! # Right continuity of the raw natural filtration of an arrival count

At each observation time, every valid nonexplosive arrival path has a
strictly later window with no further arrival. Represent a future event
by its measurable set of count observations, and evaluate that set on the
observations frozen at the present time. This gives present-measurable
events that eventually agree, pointwise, with the original event as the
future observation times decrease to the present.

A countable eventual-event construction proves raw right continuity. The
proof does not interchange an intersection with a comap, use probability
completion, or claim this property for arbitrary cadlag processes. It uses
the actual everywhere-valid count, including paths with infinite arrival
tails, and introduces no new history or count owner.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- The actual everywhere nonexplosive arrival count has a right-continuous
raw natural filtration on any sample space, without any probability hypothesis. -/
theorem natural_count_isRightContinuous
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) :
    (Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)).IsRightContinuous := by
  classical
  let N : ℝ≥0 → Ω → ℕ := fun s ω ↦ (hΓ ω).count s
  let hN : ∀ s, StronglyMeasurable (N s) :=
    fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable
  let F := Filtration.natural N hN
  have ha : StronglyAdapted F N := Filtration.stronglyAdapted_natural hN
  constructor
  intro t E hE
  obtain ⟨u, _, htu, hlim⟩ := exists_seq_strictAnti_tendsto t
  have hfuture (k : ℕ) : MeasurableSet[F (u k)] E := by
    have hle : F.rightCont t ≤ F (u k) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le (u k) (htu k)
    exact hle E hE
  have hrep (k : ℕ) : ∃ B : Set (Iic (u k) → ℕ), MeasurableSet B ∧
      (fun ω (s : Iic (u k)) ↦ N s ω) ⁻¹' B = E := by
    have hk := hfuture k
    change MeasurableSet[(Filtration.natural N hN) (u k)] E at hk
    rw [Filtration.natural_eq_comap] at hk
    exact MeasurableSpace.measurableSet_comap.mp hk
  choose B hmB heB using hrep
  let C : ℕ → Set Ω := fun k ↦
    (fun ω (s : Iic (u k)) ↦ N (min s t) ω) ⁻¹' B k
  have hmC (k : ℕ) : MeasurableSet[F t] (C k) := by
    have hpast : Measurable[F t]
        (fun ω (s : Iic (u k)) ↦ N (min s t) ω) := by
      let : MeasurableSpace Ω := F t
      refine measurable_pi_lambda _ fun s ↦ ?_
      exact (ha.stronglyMeasurable_le (min_le_right (s : ℝ≥0) t)).measurable
    exact hpast (hmB k)
  have hsame (ω : Ω) : ∀ᶠ k in atTop, ω ∈ C k ↔ ω ∈ E := by
    obtain ⟨b, htb, hb⟩ : ∃ b : ℝ≥0, t < b ∧
        (b : WithTop ℝ≥0) ≤ Γ (N t ω) ω := by
      cases he : Γ (N t ω) ω with
      | top => exact ⟨t + 1, lt_add_one t, le_top⟩
      | coe b =>
          refine ⟨b, ?_, le_rfl⟩
          exact WithTop.coe_lt_coe.mp (he ▸ (hΓ ω).lt_arrival_count t)
    filter_upwards [hlim.eventually (Iio_mem_nhds htb)] with k hk
    have hpath : (fun s : Iic (u k) ↦ N (min s t) ω) =
        fun s : Iic (u k) ↦ N s ω := by
      funext s
      by_cases hs : (s : ℝ≥0) ≤ t
      · rw [min_eq_left hs]
      · have hts : t ≤ (s : ℝ≥0) := le_of_not_ge hs
        rw [min_eq_right hts]
        apply Nat.le_antisymm ((hΓ ω).monotone_count hts)
        apply ((hΓ ω).count_le_iff s (N t ω)).mpr
        exact (WithTop.coe_lt_coe.mpr (s.property.trans_lt hk)).trans_le hb
    change (fun s : Iic (u k) ↦ N (min s t) ω) ∈ B k ↔ ω ∈ E
    rw [hpath]
    exact Set.ext_iff.mp (heB k) ω
  have he : E = ⋃ K : ℕ, ⋂ k : ℕ, ⋂ (_ : K ≤ k), C k := by
    ext ω
    simp only [mem_iUnion, mem_iInter]
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hsame ω)
    constructor
    · intro hω
      exact ⟨K, fun k hk ↦ (hK k hk).mpr hω⟩
    · rintro ⟨L, hL⟩
      exact (hK (max K L) (le_max_left _ _)).mp (hL _ (le_max_right _ _))
  rw [he]
  exact MeasurableSet.iUnion fun K ↦ MeasurableSet.iInter fun k ↦
    MeasurableSet.iInter fun (_ : K ≤ k) ↦ hmC k

end ProbabilityTheory.IsNonexplosiveArrivalSequence

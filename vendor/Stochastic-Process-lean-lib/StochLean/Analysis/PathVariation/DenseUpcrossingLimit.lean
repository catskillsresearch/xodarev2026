/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.DenseUpcrossings
public import StochLean.Analysis.PathVariation.CeilingIndex

/-! # Finite dense upcrossings exclude persistent continuous-time oscillations

Right continuity transports two late strict level visits to a sufficiently
fine existing grid. Embedding all earlier endpoints into its initial segment
then produces an additional native upcrossing, contradicting a maximal count.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean

/-- A strict upcrossing after the old horizon increases its count, even if
the finer grid has repeated endpoints. Both old and new endpoints are counted. -/
theorem TimePartition.upcrossingsBefore_lt_of_later_crossing
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ} {S T s t : ℝ≥0}
    (hab : a < b) (ρ : TimePartition S) (π : TimePartition T)
    (hρ : Set.range ρ.point ⊆ Set.range π.point) (hSs : S < s) (hst : s ≤ t) (ht : t ≤ T)
    (hsX : X (π.ceilingPoint s) ω < a) (htX : b < X (π.ceilingPoint t) ω) :
    upcrossingsBefore a b (fun k ↦ X (ρ.pointNat k)) (ρ.size + 1) ω <
      upcrossingsBefore a b (fun k ↦ X (π.pointNat k)) (π.size + 1) ω := by
  let e (k : ℕ) : ℕ := (π.ceilingIndex (ρ.pointNat k)).val
  let N := (π.ceilingIndex S).val + 1
  let i := π.ceilingIndex s
  let j := π.ceilingIndex t
  have he : Monotone e := fun _ _ h ↦ π.ceilingIndex_mono (ρ.pointNat_mono h)
  have hb (k : ℕ) (_hk : k < ρ.size + 1) : e k < N := by
    apply Nat.lt_succ_of_le
    exact π.ceilingIndex_mono (ρ.point_le_horizon _)
  have hsamp : (fun k ↦ X (π.pointNat (e k))) = fun k ↦ X (ρ.pointNat k) := by
    funext k
    exact congrArg X (π.pointNat_ceilingIndex_eq_of_mem (hρ (ρ.pointNat_mem k)))
  have hprefix : upcrossingsBefore a b (fun k ↦ X (ρ.pointNat k)) (ρ.size + 1) ω ≤
      upcrossingsBefore a b (fun k ↦ X (π.pointNat k)) N ω := by
    simpa only [hsamp] using
      (upcrossingsBefore_comp_le (f := fun k ↦ X (π.pointNat k)) hab he hb (ω := ω))
  have hS : π.ceilingPoint S = S :=
    π.ceilingPoint_eq_of_mem (hρ ⟨Fin.last ρ.size, ρ.last_eq_horizon⟩)
  have hsi : s ≤ π.ceilingPoint s := by
    simpa only [min_eq_left (hst.trans ht)] using π.min_le_ceilingPoint s
  have hNi : N ≤ i.val := by
    have hv : π.ceilingIndex S < i := by
      apply lt_of_not_ge
      intro hle
      have hx := π.monotone_point hle
      change π.ceilingPoint s ≤ π.ceilingPoint S at hx
      rw [hS] at hx
      exact (not_le_of_gt hSs) (hsi.trans hx)
    exact Nat.succ_le_of_lt hv
  have hij : i.val ≤ j.val := π.ceilingIndex_mono hst
  have hv₁ : X (π.pointNat i.val) ω < a := by
    rw [π.pointNat_fin i]
    exact hsX
  have hv₂ : b < X (π.pointNat j.val) ω := by
    rw [π.pointNat_fin j]
    exact htX
  have hinc := upcrossingsBefore_lt_of_exists_upcrossing
    (f := fun k ↦ X (π.pointNat k)) (ω := ω) hab hNi hv₁ hij hv₂
  exact (hprefix.trans_lt hinc).trans_le
    (upcrossingsBefore_mono hab (Nat.succ_le_of_lt j.isLt) ω)

/-- Finite dense-grid counts control visits at all real times, using one
right-continuous path, not an uncountable collection of almost-sure claims. -/
theorem not_frequently_of_denseUpcrossings_lt_top
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ} (hab : a < b)
    (hr : ∀ t, ContinuousWithinAt (fun s ↦ X s ω) (Ici t) t)
    (hf : denseUpcrossings a b X ω < ⊤) :
    ¬ ((∃ᶠ t in atTop, X t ω < a) ∧ ∃ᶠ t in atTop, b < X t ω) := by
  obtain ⟨n, hn⟩ := exists_max_upcrossings_expandingDyadic hf
  rintro ⟨hl, hu⟩
  rw [frequently_atTop] at hl hu
  obtain ⟨s, hns, hs⟩ := hl ((n : ℝ≥0) + 1)
  obtain ⟨t, hst, ht⟩ := hu s
  have hsEv : ∀ᶠ m : ℕ in atTop,
      X ((TimePartition.expandingDyadic m).ceilingPoint s) ω < a :=
    (TimePartition.tendsto_eval_expandingDyadic_ceilingPoint (hr s)).eventually_lt_const hs
  have htEv : ∀ᶠ m : ℕ in atTop,
      b < X ((TimePartition.expandingDyadic m).ceilingPoint t) ω :=
    (TimePartition.tendsto_eval_expandingDyadic_ceilingPoint (hr t)).eventually_const_lt ht
  obtain ⟨K, hK⟩ := exists_nat_ge t
  obtain ⟨m, ⟨⟨hnm, hKm⟩, hsm⟩, htm⟩ :=
    (eventually_ge_atTop n |>.and (eventually_ge_atTop K) |>.and hsEv |>.and htEv).exists
  have hS : (n : ℝ≥0) < s := lt_of_lt_of_le (lt_add_one _) hns
  have hmT : t ≤ (m : ℝ≥0) := hK.trans (by exact_mod_cast hKm)
  exact (not_lt_of_ge (hn m))
    (TimePartition.upcrossingsBefore_lt_of_later_crossing hab
      (TimePartition.expandingDyadic n) (TimePartition.expandingDyadic m)
      (TimePartition.expandingDyadic_range_mono hnm) hS hst hmT hsm htm)

/-- An integer-time limit extends to the full time axis when right continuity
and finite dense upcrossings rule out intervening excursions. No integrability
or probability assumptions occur in this deterministic bridge. -/
theorem tendsto_of_integer_limit_of_denseUpcrossings
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {z : ℝ}
    (hr : ∀ t, ContinuousWithinAt (fun s ↦ X s ω) (Ici t) t)
    (hn : Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 z))
    (hf : ∀ a b : ℚ, a < b → denseUpcrossings a b X ω < ⊤) :
    Tendsto (fun t ↦ X t ω) atTop (𝓝 z) := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro a haz
    obtain ⟨r, har, hrz⟩ := exists_rat_btwn haz
    obtain ⟨s, hrs, hsz⟩ := exists_rat_btwn hrz
    have hno := not_frequently_of_denseUpcrossings_lt_top hrs hr
      (hf r s (Rat.cast_lt.mp hrs))
    by_contra h
    have hl : ∃ᶠ t : ℝ≥0 in atTop, X t ω ≤ a := by
      simpa only [not_eventually, not_lt] using h
    exact hno ⟨hl.mono (fun _ hle ↦ hle.trans_lt har),
      ht.frequently (hn.eventually_const_lt hsz).frequently⟩
  · intro b hzb
    obtain ⟨s, hzs, hsb⟩ := exists_rat_btwn hzb
    obtain ⟨r, hzr, hrs⟩ := exists_rat_btwn hzs
    have hno := not_frequently_of_denseUpcrossings_lt_top hrs hr
      (hf r s (Rat.cast_lt.mp hrs))
    by_contra h
    have hu : ∃ᶠ t : ℝ≥0 in atTop, b ≤ X t ω := by
      simpa only [not_eventually, not_lt] using h
    exact hno ⟨ht.frequently (hn.eventually_lt_const hzr).frequently,
      hu.mono (fun _ hle ↦ hsb.trans_le hle)⟩

end StochLean

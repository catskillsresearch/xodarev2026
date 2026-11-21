/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import StochLean.Probability.Process.Measurability.Progressive

/-! # Strict-past deterministic grids for predictable processes

At a positive grid endpoint the preceding cell is used, as required for predictable
`(s,t]` rectangles. At zero the original initial value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

noncomputable def strictLeftGrid (δ t : ℝ≥0) : ℝ≥0 :=
  δ * ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0)

@[simp] theorem strictLeftGrid_zero (δ : ℝ≥0) : strictLeftGrid δ 0 = 0 := by
  simp [strictLeftGrid]

theorem strictLeftGrid_mem_cell {δ t : ℝ≥0} (hδ : 0 < δ) (ht : 0 < t) :
    t ∈ Ioc (strictLeftGrid δ t) (strictLeftGrid δ t + δ) := by
  have hn : 0 < Nat.ceil (t / δ) := Nat.ceil_pos.mpr (div_pos ht hδ)
  have hs : Nat.ceil (t / δ) - 1 + 1 = Nat.ceil (t / δ) := Nat.sub_add_cancel hn
  have hlo : ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0) < t / δ :=
    Nat.lt_ceil.mp (Nat.sub_lt hn (by decide))
  have hhi := Nat.le_ceil (t / δ)
  constructor
  · simpa only [strictLeftGrid, mul_comm δ] using (lt_div_iff₀ hδ).mp hlo
  · have h := (div_le_iff₀ hδ).mp hhi
    have heq : (Nat.ceil (t / δ) : ℝ≥0) = ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0) + 1 := by
      exact_mod_cast hs.symm
    simpa only [heq, add_mul, one_mul, strictLeftGrid, mul_comm δ] using h

theorem strictLeftGrid_eq_of_mem_cell {δ t : ℝ≥0} (hδ : 0 < δ) (k : ℕ)
    (ht : t ∈ Ioc (δ * k) (δ * (k + 1))) : strictLeftGrid δ t = δ * k := by
  have hceil : Nat.ceil (t / δ) = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr
    constructor
    · simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using
        (lt_div_iff₀ hδ).mpr (by simpa only [mul_comm δ] using ht.1)
    · exact (div_le_iff₀ hδ).mpr
        (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, mul_comm δ] using ht.2)
  simp only [strictLeftGrid, hceil, Nat.add_sub_cancel]

theorem strictLeftGrid_le {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) : strictLeftGrid δ t ≤ t := by
  rcases eq_or_lt_of_le (show 0 ≤ t from bot_le) with ht | ht
  · subst t
    rw [strictLeftGrid_zero]
  · exact (strictLeftGrid_mem_cell hδ ht).1.le

theorem le_strictLeftGrid_add {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) :
    t ≤ strictLeftGrid δ t + δ := by
  rcases eq_or_lt_of_le (show 0 ≤ t from bot_le) with ht | ht
  · subst t
    exact bot_le
  · exact (strictLeftGrid_mem_cell hδ ht).2

theorem tendsto_strictLeftGrid (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ strictLeftGrid (1 / ((n : ℝ≥0) + 1)) t) atTop (𝓝[≤] t) := by
  have hδ : ∀ n : ℕ, 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) := fun n ↦ by positivity
  have hlim : Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (fun n ↦ strictLeftGrid_le (hδ n) t)⟩
  have hlo : Tendsto (fun n : ℕ ↦ t - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
    simpa only [tsub_zero] using tendsto_const_nhds.sub hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n ↦ tsub_le_iff_right.mpr (le_strictLeftGrid_add (hδ n) t))
    (fun n ↦ strictLeftGrid_le (hδ n) t)

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

theorem Adapted.measurable_strictLeftGrid_sample (ha : Adapted F X)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    Measurable[F.predictable] (fun z : ℝ≥0 × Ω ↦ X (strictLeftGrid δ z.1) z.2) := by
  intro s hs
  have heq : (fun z : ℝ≥0 × Ω ↦ X (strictLeftGrid δ z.1) z.2) ⁻¹' s =
      ({0} ×ˢ ((X 0) ⁻¹' s)) ∪
        ⋃ k : ℕ, Ioc (δ * k) (δ * (k + 1)) ×ˢ ((X (δ * k)) ⁻¹' s) := by
    ext ⟨t, ω⟩
    constructor
    · intro h
      by_cases ht : t = 0
      · left
        simpa only [ht, mem_prod, mem_singleton_iff, strictLeftGrid_zero, mem_preimage,
          true_and] using h
      · right
        let k := Nat.ceil (t / δ) - 1
        apply mem_iUnion.mpr ⟨k, ?_⟩
        have hcell := strictLeftGrid_mem_cell hδ (pos_iff_ne_zero.mpr ht)
        refine ⟨?_, h⟩
        simpa only [strictLeftGrid, k, mul_add, mul_one] using hcell
    · rintro (h | h)
      · rcases h with ⟨ht, hω⟩
        have ht' : t = 0 := ht
        change X (strictLeftGrid δ t) ω ∈ s
        simpa only [ht', strictLeftGrid_zero, mem_preimage] using hω
      · obtain ⟨k, hk, hω⟩ := mem_iUnion.mp h
        change X (strictLeftGrid δ t) ω ∈ s
        simpa only [strictLeftGrid_eq_of_mem_cell hδ k hk, mem_preimage] using hω
  rw [heq]
  exact (measurableSet_predictable_singleton_bot_prod (ha 0 hs)).union
    (MeasurableSet.iUnion (fun k ↦ measurableSet_predictable_Ioc_prod _ _ (ha _ hs)))

end MeasureTheory

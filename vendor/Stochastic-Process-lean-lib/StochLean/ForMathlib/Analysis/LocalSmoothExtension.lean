/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.Separation.Regular

/-! # Smooth extension near a closed subset of an open finite-dimensional domain

The cutoff is built from Mathlib's smooth functions with prescribed open
support. The input function can be arbitrary outside its smooth domain.
Equality holds on a neighborhood of each point of the closed set, so it
also transports derivatives there. No extension hypothesis is assumed.
-/

@[expose] public section

open Set Filter Function
open scoped Topology ContDiff

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contDiff_cutoff_near_closed {K D : Set E}
    (hK : IsClosed K) (hD : IsOpen D) (hKD : K ⊆ D) :
    ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ range φ ⊆ Icc 0 1 ∧ tsupport φ ⊆ D ∧
      ∀ x ∈ K, φ =ᶠ[𝓝 x] 1 := by
  obtain ⟨V, hV, hKV, hVD⟩ := normal_exists_closure_subset hK hD hKD
  obtain ⟨U, hU, hKU, hUV⟩ := normal_exists_closure_subset hK hV hKV
  obtain ⟨u, huS, hu, huR⟩ := hV.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨v, hvS, hv, hvR⟩ := isClosed_closure.isOpen_compl.exists_contDiff_support_eq
    (n := ⊤) (s := (closure U)ᶜ)
  have hu0 : ∀ x, 0 ≤ u x := fun x ↦ (huR (mem_range_self x)).1
  have hv0 : ∀ x, 0 ≤ v x := fun x ↦ (hvR (mem_range_self x)).1
  have hpos : ∀ x, 0 < u x + v x := by
    intro x
    by_cases hx : x ∈ V
    · have hx' : u x ≠ 0 := by simpa only [← mem_support, huS] using hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hu0 x) (Ne.symm hx')) (hv0 x)
    · have hx' : v x ≠ 0 := by
        rw [← mem_support, hvS]
        exact fun h ↦ hx (hUV h)
      exact add_pos_of_nonneg_of_pos (hu0 x) (lt_of_le_of_ne (hv0 x) (Ne.symm hx'))
  let φ := fun x ↦ u x / (u x + v x)
  have hS : support φ = V := by
    have hd : support (fun x ↦ u x + v x) = univ :=
      eq_univ_of_forall (fun x ↦ (hpos x).ne')
    simp only [φ, support_div, huS, hd, inter_univ]
  refine ⟨φ, hu.div (hu.add hv) (fun x ↦ (hpos x).ne'), ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨div_nonneg (hu0 x) (hpos x).le,
      div_le_one_of_le₀ (le_add_of_nonneg_right (hv0 x)) (hpos x).le⟩
  · simpa only [tsupport, hS] using hVD
  · intro x hx
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    have hvy : v y = 0 := by
      rw [← notMem_support, hvS]
      exact not_not_intro (subset_closure hy)
    change u y / (u y + v y) = 1
    exact (div_eq_one_iff_eq (hpos y).ne').2 (by rw [hvy, add_zero])

theorem exists_contDiff_extension_near_closed {K D : Set E} {f : E → ℝ}
    {n : ℕ∞} (hK : IsClosed K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ n f D) :
    ∃ g : E → ℝ, ContDiff ℝ n g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨φ, hφ, _, hφD, hφ1⟩ := exists_contDiff_cutoff_near_closed hK hD hKD
  refine ⟨fun x ↦ φ x * f x, contDiff_iff_contDiffAt.mpr (fun x ↦ ?_), ?_⟩
  · by_cases hx : x ∈ tsupport φ
    · exact ((hφ.of_le (mod_cast le_top)).contDiffAt).mul
        (hf.contDiffAt (hD.mem_nhds (hφD hx)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
  · intro x hx
    filter_upwards [hφ1 x hx] with y hy
    simp only [hy, Pi.one_apply, one_mul]

end StochLean

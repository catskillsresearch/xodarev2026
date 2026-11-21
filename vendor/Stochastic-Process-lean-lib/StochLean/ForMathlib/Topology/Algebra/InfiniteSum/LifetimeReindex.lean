/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Order.WithBot

/-! # Reindexing sums along disjoint finite lifetime graphs

Only the values at finite lifetimes are used. Infinite lifetimes contribute
zero and may be repeated. The sum identity needs no summability hypothesis;
absolute summability is separately used for quantitative partial-sum bounds.
No new lifetime evaluation or sum owner is introduced.
-/

@[expose] public section

open Function Set

namespace StochLean

private theorem exists_lifetime_support_embedding {α ι E : Type*} [Zero E]
    {f : α → E} {g : ι → E} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t) :
    ∃ e : support g → α, Injective e ∧
      (∀ i : support g, τ i = (e i : WithTop α)) ∧ (∀ i, f (e i) = g i) := by
  classical
  have hfinite (i : support g) : ∃ t : α, τ i = (t : WithTop α) := by
    have hn : τ i ≠ ⊤ := fun h ↦ i.property (htop i h)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hn
    exact ⟨t, ht.symm⟩
  choose e he using hfinite
  refine ⟨e, ?_, he, fun i ↦ (hcoe i (e i) (he i)).symm⟩
  intro i j hij
  apply Subtype.ext
  exact hdisj i j (e i) (he i)
    ((he j).trans (congrArg (fun t : α ↦ (t : WithTop α)) hij.symm))

/-- A cover of the actual nonzero terms gives an exact reindexing. Neither
the original series nor the lifetime-indexed series is assumed summable. -/
theorem tsum_eq_tsum_of_disjoint_finite_lifetimes {α ι : Type*}
    {f : α → ℝ} {g : ι → ℝ} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t)
    (hcover : ∀ t, f t ≠ 0 → ∃ i, τ i = (t : WithTop α)) :
    (∑' t, f t) = ∑' i, g i := by
  classical
  obtain ⟨e, he, hτe, hfe⟩ := exists_lifetime_support_embedding hdisj htop hcoe
  apply tsum_eq_tsum_of_ne_zero_bij e he _ hfe
  intro t ht
  obtain ⟨i, hi⟩ := hcover t ht
  have hgi : g i ≠ 0 := by rwa [hcoe i t hi]
  refine ⟨⟨i, hgi⟩, ?_⟩
  exact WithTop.coe_injective ((hτe ⟨i, hgi⟩).symm.trans hi)

/-- Deleting or reindexing terms along disjoint finite lifetime graphs
preserves summability. A cover of the original support is not needed. -/
theorem summable_of_disjoint_finite_lifetimes {α ι : Type*}
    {f : α → ℝ} {g : ι → ℝ} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t)
    (hf : Summable f) : Summable g := by
  obtain ⟨e, he, _, hfe⟩ := exists_lifetime_support_embedding hdisj htop hcoe
  have hs : Summable (fun i : support g ↦ g i) := (hf.comp_injective he).congr hfe
  exact hasSum_subtype_support.mp hs.hasSum |>.summable

/-- Every finite partial sum of absolute values is dominated by the actual
original absolute series. Missing support points are permitted. -/
theorem sum_abs_le_tsum_abs_of_disjoint_finite_lifetimes {α ι : Type*}
    {f : α → ℝ} {g : ι → ℝ} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t)
    (hf : Summable (fun t ↦ |f t|)) (s : Finset ι) :
    (∑ i ∈ s, |g i|) ≤ ∑' t, |f t| := by
  classical
  have htop' : ∀ i, τ i = ⊤ → |g i| = 0 := fun i hi ↦ by rw [htop i hi, abs_zero]
  have hcoe' : ∀ i (t : α), τ i = (t : WithTop α) → |g i| = |f t| :=
    fun i t hi ↦ congrArg abs (hcoe i t hi)
  have hg := summable_of_disjoint_finite_lifetimes hdisj htop' hcoe' hf
  obtain ⟨e, he, _, hfe⟩ := exists_lifetime_support_embedding hdisj htop' hcoe'
  have hs : Summable (fun i : support (fun i ↦ |g i|) ↦ |g i|) :=
    (hf.comp_injective he).congr hfe
  have hle := hs.tsum_le_tsum_of_inj e he (fun t _ ↦ abs_nonneg (f t))
    (fun i ↦ (hfe i).ge) hf
  rw [tsum_subtype_support] at hle
  exact (hg.sum_le_tsum s (fun i _ ↦ abs_nonneg (g i))).trans hle

/-- The signed finite partial sum has the same absolute-series envelope. -/
theorem abs_sum_le_tsum_abs_of_disjoint_finite_lifetimes {α ι : Type*}
    {f : α → ℝ} {g : ι → ℝ} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t)
    (hf : Summable (fun t ↦ |f t|)) (s : Finset ι) :
    |∑ i ∈ s, g i| ≤ ∑' t, |f t| :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_abs_le_tsum_abs_of_disjoint_finite_lifetimes hdisj htop hcoe hf s)

end StochLean

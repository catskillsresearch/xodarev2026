/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.RefinementSums
public import StochLean.Probability.Process.Semimartingale.Quasimartingale.StrictPartition
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Refinement of conditional variation

Refining a deterministic partition increases expected conditional variation.
More precisely, the sums are ordered after conditioning at the initial sigma
field. The same statement holds separately for positive and negative conditional
decrements, retaining the corresponding positive or negative terminal-zero tail.
The unconditioned random sums are not asserted to be pointwise ordered.

Only finitely many endpoint pairs and triples enter the common almost-everywhere
event. No second partition, conditional-variation, or Rao decomposition owner is
introduced, and no path regularity or adaptedness is needed for this finite result.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

omit [IsFiniteMeasure P] in
private theorem max_condExp_zero_le {f : Ω → ℝ} (hi : Integrable f P)
    (m : MeasurableSpace Ω) :
    (fun ω ↦ max (P[f | m] ω) 0) ≤ᵐ[P] P[(fun ω ↦ max (f ω) 0) | m] := by
  have hm := condExp_mono (m := m) hi (hi.sup (integrable_zero _ _ _))
    (Eventually.of_forall fun ω ↦ le_max_left (f ω) 0)
  have hn := condExp_nonneg (m := m) (μ := P)
    (Eventually.of_forall fun ω ↦ le_max_right (f ω) 0)
  filter_upwards [hm, hn] with ω hmω hnω
  exact max_le hmω hnω

private theorem condExp_transformed_cell_triangle
    (hi : ∀ t, Integrable (X t) P) (φ : ℝ → ℝ)
    (hφi : ∀ {f : Ω → ℝ}, Integrable f P → Integrable (fun ω ↦ φ (f ω)) P)
    (hφadd : ∀ x y, φ (x + y) ≤ φ x + φ y)
    (hφj : ∀ {f : Ω → ℝ}, Integrable f P → ∀ m : MeasurableSpace Ω,
      (fun ω ↦ φ (P[f | m] ω)) ≤ᵐ[P] P[(fun ω ↦ φ (f ω)) | m])
    {a b c : ℝ≥0} (hab : a ≤ b) (_hbc : b ≤ c) :
    P[(fun ω ↦ φ (P[X a - X c | F a] ω)) | F 0] ≤ᵐ[P]
      P[(fun ω ↦ φ (P[X a - X b | F a] ω)) | F 0] +
        P[(fun ω ↦ φ (P[X b - X c | F b] ω)) | F 0] := by
  have hid : X a - X c = (X a - X b) + (X b - X c) := by
    ext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hsplit : P[X a - X c | F a] =ᵐ[P]
      P[X a - X b | F a] + P[P[X b - X c | F b] | F a] := by
    rw [hid]
    exact (condExp_add ((hi a).sub (hi b)) ((hi b).sub (hi c)) (F a)).trans
      (EventuallyEq.rfl.add (condExp_condExp_of_le (F.mono hab) (F.le b)).symm)
  have hinner : (fun ω ↦ φ (P[X a - X c | F a] ω)) ≤ᵐ[P]
      (fun ω ↦ φ (P[X a - X b | F a] ω)) +
        P[(fun ω ↦ φ (P[X b - X c | F b] ω)) | F a] := by
    filter_upwards [hsplit, hφj (integrable_condExp (f := X b - X c) (m := F b))
      (F a)] with ω hs hj
    simp only [Pi.add_apply] at hs ⊢
    rw [hs]
    exact (hφadd _ _).trans (add_le_add (le_refl _) hj)
  have ho := condExp_mono (m := F 0) (hφi integrable_condExp)
    ((hφi integrable_condExp).add integrable_condExp) hinner
  have hadd := condExp_add (hφi (integrable_condExp (f := X a - X b) (m := F a)))
    (integrable_condExp (f := fun ω ↦ φ (P[X b - X c | F b] ω)) (m := F a)) (F 0)
  have ht := condExp_condExp_of_le (μ := P) (F.mono (show 0 ≤ a from bot_le)) (F.le a)
    (f := fun ω ↦ φ (P[X b - X c | F b] ω))
  filter_upwards [ho, hadd, ht] with ω hoω haω htω
  simpa only [haω, Pi.add_apply, htω] using hoω

private theorem condExp_transformed_sum_le_of_refines
    (hi : ∀ t, Integrable (X t) P) {ρ π : TimePartition T} (h : ρ.Refines π)
    (φ : ℝ → ℝ) (hφzero : φ 0 = 0) (hφn : ∀ x, 0 ≤ φ x)
    (hφi : ∀ {f : Ω → ℝ}, Integrable f P → Integrable (fun ω ↦ φ (f ω)) P)
    (hφadd : ∀ x y, φ (x + y) ≤ φ x + φ y)
    (hφj : ∀ {f : Ω → ℝ}, Integrable f P → ∀ m : MeasurableSpace Ω,
      (fun ω ↦ φ (P[f | m] ω)) ≤ᵐ[P] P[(fun ω ↦ φ (f ω)) | m]) :
    P[(fun ω ↦ (∑ i, φ (P[X (π.left i) - X (π.right i) | F (π.left i)] ω)) +
      φ (X T ω)) | F 0] ≤ᵐ[P]
    P[(fun ω ↦ (∑ j, φ (P[X (ρ.left j) - X (ρ.right j) | F (ρ.left j)] ω)) +
      φ (X T ω)) | F 0] := by
  classical
  let w (a b : ℝ≥0) := P[(fun ω ↦ φ (P[X a - X b | F a] ω)) | F 0]
  have hn (i j : Fin (ρ.size + 1)) : 0 ≤ᵐ[P] w (ρ.point i) (ρ.point j) :=
    condExp_nonneg (Eventually.of_forall fun _ ↦ hφn _)
  have ht (i j k : Fin (ρ.size + 1)) :
      ∀ᵐ ω ∂P, ρ.point i ≤ ρ.point j → ρ.point j ≤ ρ.point k →
        w (ρ.point i) (ρ.point k) ω ≤
          w (ρ.point i) (ρ.point j) ω + w (ρ.point j) (ρ.point k) ω := by
    by_cases hij : ρ.point i ≤ ρ.point j
    · by_cases hjk : ρ.point j ≤ ρ.point k
      · exact (condExp_transformed_cell_triangle hi φ hφi hφadd hφj hij hjk).mono
          fun _ hω _ _ ↦ hω
      · exact Eventually.of_forall fun _ _ hh ↦ (hjk hh).elim
    · exact Eventually.of_forall fun _ hh _ ↦ (hij hh).elim
  have hsum : (fun ω ↦ ∑ i, w (π.left i) (π.right i) ω) ≤ᵐ[P]
      fun ω ↦ ∑ j, w (ρ.left j) (ρ.right j) ω := by
    filter_upwards [ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (hn i)),
      ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (ht i j)))]
      with ω hnω htω
    apply h.sum_cells_le (fun a b ↦ w a b ω)
    · intro t
      simp [w, hφzero]
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hnω i j
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk
      exact htω i j k hij hjk
  have he (σ : TimePartition T) :
      P[(fun ω ↦ (∑ i, φ (P[X (σ.left i) - X (σ.right i) | F (σ.left i)] ω)) +
        φ (X T ω)) | F 0] =ᵐ[P]
        fun ω ↦ (∑ i, w (σ.left i) (σ.right i) ω) +
          P[(fun ω ↦ φ (X T ω)) | F 0] ω := by
    have hadd := condExp_add
      (integrable_finsetSum Finset.univ (fun i _ ↦ hφi
        (integrable_condExp (f := X (σ.left i) - X (σ.right i)) (m := F (σ.left i)))))
      (hφi (hi T)) (F 0)
    have hs := condExp_finsetSum (μ := P) (s := Finset.univ)
      (f := fun i : Fin σ.size ↦ fun ω ↦
        φ (P[X (σ.left i) - X (σ.right i) | F (σ.left i)] ω))
      (fun _ _ ↦ hφi integrable_condExp) (F 0)
    filter_upwards [hadd, hs] with ω haω hsω
    simp only [Finset.sum_fn, Pi.add_apply] at haω hsω
    simpa only [Pi.add_def, Finset.sum_apply, w] using
      haω.trans (congrArg (fun z ↦ z + P[(fun ω ↦ φ (X T ω)) | F 0] ω) hsω)
  filter_upwards [he π, he ρ, hsum] with ω hp hρ hs
  rw [hp, hρ]
  exact add_le_add hs (le_refl _)

/-- Conditional variation is ordered under refinement after conditioning at
the initial sigma field. Its actual terminal-zero contribution is retained. -/
theorem condExp_conditionalVariationSum_le_of_refines
    (hi : ∀ t, Integrable (X t) P) {ρ π : TimePartition T} (h : ρ.Refines π) :
    P[conditionalVariationSum X F P π | F 0] ≤ᵐ[P]
      P[conditionalVariationSum X F P ρ | F 0] := by
  unfold conditionalVariationSum
  simp only [sub_zero]
  exact condExp_transformed_sum_le_of_refines (F := F) hi h abs abs_zero abs_nonneg
    (fun hf ↦ hf.abs) abs_add_le (fun _ _ ↦ abs_condExp_ae_le_condExp_abs _)

/-- Positive conditional decrements, with the positive terminal-zero tail,
increase under refinement in the initial conditional-expectation order. -/
theorem condExp_positive_conditional_decrements_le_of_refines
    (hi : ∀ t, Integrable (X t) P) {ρ π : TimePartition T} (h : ρ.Refines π) :
    P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
      max (X T ω) 0) | F 0] ≤ᵐ[P]
    P[(fun ω ↦ (∑ j, max (P[X (ρ.left j) - X (ρ.right j) | F (ρ.left j)] ω) 0) +
      max (X T ω) 0) | F 0] := by
  apply condExp_transformed_sum_le_of_refines hi h (fun x ↦ max x 0) (max_self 0)
    (fun x ↦ le_max_right x 0) (fun hf ↦ hf.sup (integrable_zero _ _ _))
  · intro x y
    exact max_le (add_le_add (le_max_left x 0) (le_max_left y 0))
      (add_nonneg (le_max_right x 0) (le_max_right y 0))
  · exact fun hf m ↦ max_condExp_zero_le hf m

/-- The negative half is the positive-decrement theorem for the actual process
`-X`; its terminal contribution is `max (-X T) 0`, not an omitted tail. -/
theorem condExp_negative_conditional_decrements_le_of_refines
    (hi : ∀ t, Integrable (X t) P) {ρ π : TimePartition T} (h : ρ.Refines π) :
    P[(fun ω ↦ (∑ i, max (P[(-X) (π.left i) - (-X) (π.right i) |
      F (π.left i)] ω) 0) + max (-X T ω) 0) | F 0] ≤ᵐ[P]
    P[(fun ω ↦ (∑ j, max (P[(-X) (ρ.left j) - (-X) (ρ.right j) |
      F (ρ.left j)] ω) 0) + max (-X T ω) 0) | F 0] :=
  condExp_positive_conditional_decrements_le_of_refines (fun t ↦ (hi t).neg) h

/-- Refinement cannot decrease the real expectation of conditional variation. -/
theorem integral_conditionalVariationSum_le_of_refines
    (hi : ∀ t, Integrable (X t) P) {ρ π : TimePartition T} (h : ρ.Refines π) :
    (∫ ω, conditionalVariationSum X F P π ω ∂P) ≤
      ∫ ω, conditionalVariationSum X F P ρ ω ∂P := by
  have hh := integral_mono_ae integrable_condExp integrable_condExp
    (condExp_conditionalVariationSum_le_of_refines hi h (F := F))
  simpa only [integral_condExp (F.le 0)] using hh

/-- The existing extended conditional-variation owner is monotone in the
actual endpoint-set refinement relation. -/
theorem eConditionalVariationOnPartition_le_of_refines
    (hi : ∀ t, Integrable (X t) P) {ρ π : TimePartition T} (h : ρ.Refines π) :
    eConditionalVariationOnPartition X F P π ≤ eConditionalVariationOnPartition X F P ρ := by
  rw [eConditionalVariationOnPartition_eq_ofReal_integral hi,
    eConditionalVariationOnPartition_eq_ofReal_integral hi]
  exact ENNReal.ofReal_le_ofReal (integral_conditionalVariationSum_le_of_refines hi h)

end ProbabilityTheory

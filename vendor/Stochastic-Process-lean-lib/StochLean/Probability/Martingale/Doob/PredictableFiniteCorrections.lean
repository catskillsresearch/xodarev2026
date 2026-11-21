/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ClassDPredictableJumpMean
public import StochLean.Probability.Martingale.Doob.PredictableJumpRemoval
public import StochLean.Probability.Process.Path.LeftLimitAddition
public import StochLean.Probability.Process.Path.Monotone
public import StochLean.Probability.Process.Stopping.Graph

/-! # Actual finite predictable jump corrections

Each coefficient is the negative before-field conditional mean of the jump of
the original Class D supermartingale. These original coefficients are not
recomputed from an assumed corrected supermartingale.

For disjoint finite stopping-time graphs, earlier closed steps have zero jump
at the next graph. Their finite-sum jump formula identifies the next actual
conditional jump mean with the fixed original coefficient. Induction can then
apply the proved single-jump removal theorem to obtain supermartingality of
every actual finite correction. Class D and common cadlag paths are preserved
independently by finite addition.

The coefficients are integrable, nonnegative almost surely, and vanish almost
surely on their infinite-lifetime events by a before-field indicator identity.
Positive lifetimes give exact zero initial finite corrections. No budget,
summability, infinite series, or compensator existence is assumed or asserted.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The fixed original jump-mean coefficients supply the genuine measurable,
integrable, nonnegative, and infinite-lifetime-zero data used by later budgets. -/
theorem Supermartingale.predictable_jump_correction_coefficients
    (hX : Supermartingale X F P) (hD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (Γ : ℕ → Ω → WithTop ℝ≥0)
    (hΓ : ∀ n, IsPredictableStoppingTime F (Γ n) P) (hp : ∀ n ω, 0 < Γ n ω) :
    let K : ℕ → Ω → ℝ := fun n ↦
      -P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) |
        (hΓ n).1.measurableSpaceBefore]
    ∀ n, StronglyMeasurable[(hΓ n).1.measurableSpaceBefore] (K n) ∧
      Integrable (K n) P ∧ (0 ≤ᵐ[P] K n) ∧
      (∀ᵐ ω ∂P, Γ n ω = ⊤ → K n ω = 0) := by
  classical
  dsimp only
  intro n
  refine ⟨stronglyMeasurable_condExp.neg, integrable_condExp.neg, ?_, ?_⟩
  · exact (hX.condExp_stopped_jump_before_ae_le_zero_of_classD hD hF hc (hΓ n)
      (Eventually.of_forall (hp n))).mono fun _ hω ↦ neg_nonneg.mpr hω
  · let J := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n)
    have hiJ : Integrable J P := hD.integrable_stopped_jump_of_predictable hc (hΓ n)
      (Eventually.of_forall (hp n))
    have hm : MeasurableSet[(hΓ n).1.measurableSpaceBefore] {ω | Γ n ω = ⊤} :=
      (hΓ n).1.measurable_before (measurableSet_singleton _)
    have he : {ω | Γ n ω = ⊤}.indicator J = 0 := by
      funext ω
      by_cases ht : Γ n ω = ⊤
      · have hmem : ω ∈ {ω | Γ n ω = ⊤} := ht
        simp only [indicator_of_mem hmem, J, stoppedValueWithTerminal_of_top ht, Pi.zero_apply]
      · have hnot : ω ∉ {ω | Γ n ω = ⊤} := ht
        simp only [indicator_of_notMem hnot, Pi.zero_apply]
    have hCE := condExp_indicator hiJ hm
    rw [he, condExp_zero] at hCE
    filter_upwards [hCE] with ω hω ht
    have hmem : ω ∈ {ω | Γ n ω = ⊤} := ht
    have hz : P[J | (hΓ n).1.measurableSpaceBefore] ω = 0 := by
      simpa only [Pi.zero_apply, indicator_of_mem hmem] using hω.symm
    change -P[J | (hΓ n).1.measurableSpaceBefore] ω = 0
    rw [hz, neg_zero]

/-- Every actual finite correction is a cadlag Class D supermartingale. The
corrections themselves start exactly at zero and have monotone paths almost
surely. Supermartingality is proved inductively, not a premise of this result. -/
theorem Supermartingale.finite_predictable_jump_corrections
    (hX : Supermartingale X F P) (hD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (Γ : ℕ → Ω → WithTop ℝ≥0)
    (hΓ : ∀ n, IsPredictableStoppingTime F (Γ n) P) (hp : ∀ n ω, 0 < Γ n ω)
    (hd : Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (Γ n))
      (stoppingTimeGraph (Γ m)))) :
    let K : ℕ → Ω → ℝ := fun n ↦
      -P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) |
        (hΓ n).1.measurableSpaceBefore]
    let A : ℕ → ℝ≥0 → Ω → ℝ := fun N t ω ↦ ∑ n ∈ Finset.range N,
      {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
    (∀ N, Supermartingale (X + A N) F P ∧ IsClassD (X + A N) F P ∧
      HasCadlagPaths (X + A N) P) ∧
      (∀ N, A N 0 = 0) ∧ (∀ N, HasMonotonePaths (A N) P) := by
  classical
  let K : ℕ → Ω → ℝ := fun n ↦
    -P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) |
      (hΓ n).1.measurableSpaceBefore]
  let B : ℕ → ℝ≥0 → Ω → ℝ := fun n t ↦
    {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n)
  let A : ℕ → ℝ≥0 → Ω → ℝ := fun N t ω ↦ ∑ n ∈ Finset.range N,
    {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  change (∀ N, Supermartingale (X + A N) F P ∧ IsClassD (X + A N) F P ∧
    HasCadlagPaths (X + A N) P) ∧
    (∀ N, A N 0 = 0) ∧ (∀ N, HasMonotonePaths (A N) P)
  have hdata := hX.predictable_jump_correction_coefficients hD hF hc Γ hΓ hp
  have hmK (n : ℕ) : StronglyMeasurable[(hΓ n).1.measurableSpace] (K n) :=
    (hdata n).1.mono (hΓ n).1.measurableSpaceBefore_le
  have hBD (n : ℕ) : IsClassD (B n) F P :=
    isClassD_indicator_stoppingTime_le (hΓ n).1 (hmK n) (hdata n).2.1
  have hBa (n : ℕ) : StronglyAdapted F (B n) := fun t ↦
    (hmK n).indicator_stoppingTime_le (hΓ n).1 t
  have hAc (N : ℕ) (ω : Ω) : IsCadlagPath (A N · ω) := by
    apply IsCadlagPath.finset_sum
    intro n _
    exact isCadlagPath_indicator_lifetime_le (Γ n) (K n) ω
  have hAsucc (N : ℕ) : A (N + 1) = A N + B N := by
    funext t ω
    simp only [A, B, Finset.sum_range_succ, Pi.add_apply]
  have hAzero : A 0 = 0 := by
    funext t ω
    simp only [A, Finset.range_zero, Finset.sum_empty, Pi.zero_apply]
  have hAD (N : ℕ) : IsClassD (A N) F P := by
    induction N with
    | zero =>
      rw [hAzero]
      exact isClassD_const (F := F) (integrable_zero Ω ℝ P)
    | succ N ih =>
      rw [hAsucc]
      exact ih.add (hBD N)
  have hAa (N : ℕ) : StronglyAdapted F (A N) := by
    intro t
    convert Finset.stronglyMeasurable_sum (Finset.range N) (fun n _ ↦ hBa n t) using 1
    funext ω
    simp only [A, B, Finset.sum_apply]
  have hdc (N : ℕ) : IsClassD (X + A N) F P ∧ HasCadlagPaths (X + A N) P :=
    ⟨hD.add (hAD N), hc.add (Eventually.of_forall (hAc N))⟩
  have hSM (N : ℕ) : Supermartingale (X + A N) F P := by
    induction N with
    | zero =>
      rw [hAzero, add_zero]
      exact hX
    | succ N ih =>
      have hJ : stoppedValueWithTerminal (jumpProcess (X + A N)) (fun _ ↦ (0 : ℝ)) (Γ N)
          =ᵐ[P] stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ N) := by
        filter_upwards [hc] with ω hcω
        by_cases ht : Γ N ω = ⊤
        · simp only [stoppedValueWithTerminal_of_top ht]
        · rw [stoppedValueWithTerminal_of_ne_top ht, stoppedValueWithTerminal_of_ne_top ht]
          change jumpProcess (X + A N) (Γ N ω).untopA ω =
            jumpProcess X (Γ N ω).untopA ω
          have hcoe : ((Γ N ω).untopA : WithTop ℝ≥0) = Γ N ω := by
            rw [WithTop.untopA_eq_untop ht, WithTop.coe_untop]
          have hz : jumpProcess (A N) (Γ N ω).untopA ω = 0 := by
            change jumpProcess (fun t v ↦ ∑ n ∈ Finset.range N,
              {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) v) (Γ N ω).untopA ω = 0
            rw [jumpProcess_finset_sum_indicator_lifetime_le]
            apply Finset.sum_eq_zero
            intro n hn
            apply indicator_of_notMem
            intro hj
            exact Set.disjoint_left.mp (hd (ne_of_lt (Finset.mem_range.mp hn)))
              (show ((Γ N ω).untopA, ω) ∈ stoppingTimeGraph (Γ n) from hj)
              (show ((Γ N ω).untopA, ω) ∈ stoppingTimeGraph (Γ N) from hcoe.symm)
          rw [hcω.jumpProcess_add (hAc N ω), hz, add_zero]
      have hCE := condExp_congr_ae (m := (hΓ N).1.measurableSpaceBefore) hJ
      have hnew := ih.sub_predictable_jump_condExp (hdc N).1 hF (hdc N).2 (hΓ N)
        (Eventually.of_forall (hp N))
      apply hnew.congr (hX.stronglyAdapted.add (hAa (N + 1)))
      intro t
      filter_upwards [hCE] with ω hω
      change X t ω + A N t ω - {v | Γ N v ≤ (t : WithTop ℝ≥0)}.indicator
        P[stoppedValueWithTerminal (jumpProcess (X + A N)) (fun _ ↦ (0 : ℝ)) (Γ N) |
          (hΓ N).1.measurableSpaceBefore] ω = X t ω + A (N + 1) t ω
      rw [hAsucc]
      simp only [Pi.add_apply, B, K, indicator_apply, mem_ofPred_eq, Pi.neg_apply]
      by_cases ht : Γ N ω ≤ (t : WithTop ℝ≥0) <;>
        simp only [ht, if_true, if_false, hω] <;> ring
  refine ⟨fun N ↦ ⟨hSM N, hdc N⟩, ?_, ?_⟩
  · intro N
    funext ω
    apply Finset.sum_eq_zero
    intro n _
    apply indicator_of_notMem
    exact not_le_of_gt (hp n ω)
  · intro N
    filter_upwards [ae_all_iff.mpr (fun n ↦ (hdata n).2.2.1)] with ω hnω
    intro s t hst
    apply Finset.sum_le_sum
    intro n _
    by_cases hs : Γ n ω ≤ (s : WithTop ℝ≥0)
    · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
      simp only [indicator_apply, mem_ofPred_eq, if_pos hs, if_pos ht, le_refl]
    · by_cases ht : Γ n ω ≤ (t : WithTop ℝ≥0)
      · have hkn : 0 ≤ K n ω := hnω n
        simpa only [indicator_apply, mem_ofPred_eq, if_neg hs, if_pos ht] using hkn
      · simp only [indicator_apply, mem_ofPred_eq, if_neg hs, if_neg ht, le_refl]

end MeasureTheory

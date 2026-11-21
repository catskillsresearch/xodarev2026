/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import StochLean.Probability.Martingale.Convergence.Regularization
public import StochLean.Probability.Process.Path.Algebra

/-! # Conditional variation and quasimartingales

Protter III.4 appends an artificial zero terminal value to a finite deterministic
partition. Here the last term is explicitly `|X T - 0|`: the process is never
evaluated at infinity, and an actual terminal limit is neither selected nor assumed.
The whole-half-line supremum is extended nonnegative real, not a totalized real supremum.

The existing `TimePartition` is the sole partition owner. It permits repeated
endpoints, whose conditional increments vanish. The strict-partition comparison
is proved in the downstream `Quasimartingale.StrictPartition` module. A finite conditional-variation
value alone does not assert coordinate integrability or path regularity; these
are independent fields of `IsQuasimartingale`.

The easy direction of Protter III.17 is proved by telescoping the conditional
decrements of two nonnegative supermartingales and retaining the terminal-zero
tail. No Rao decomposition, semimartingale decomposition, or selector is used.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Conditional variation along a finite partition, including the artificial terminal-zero tail. -/
noncomputable def conditionalVariationSum (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) {T : ℝ≥0} (π : TimePartition T) : Ω → ℝ :=
  fun ω ↦ (∑ i, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) + |X T ω - 0|

/-- Expected conditional variation of one finite partition with its terminal-zero tail. -/
noncomputable def eConditionalVariationOnPartition (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) {T : ℝ≥0} (π : TimePartition T) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (conditionalVariationSum X F P π ω) ∂P

/-- Conditional variation on the entire half-line, with the zero terminal convention. -/
noncomputable def eConditionalVariation (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : ℝ≥0∞ :=
  ⨆ T : ℝ≥0, ⨆ π : TimePartition T, eConditionalVariationOnPartition X F P π

/-- Finiteness of conditional variation, without implicit integrability or path assumptions. -/
def HasFiniteConditionalVariation (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  eConditionalVariation X F P ≠ ∞

/-- An adapted, almost surely cadlag process with integrable coordinates and finite
whole-half-line conditional variation. This is not a decomposition predicate. -/
structure IsQuasimartingale (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop where
  adapted : Adapted F X
  hasCadlagPaths : HasCadlagPaths X P
  integrable : ∀ t, Integrable (X t) P
  hasFiniteConditionalVariation : HasFiniteConditionalVariation X F P

variable {X Y : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {T : ℝ≥0}

theorem conditionalVariationSum_nonneg (π : TimePartition T) (ω : Ω) :
    0 ≤ conditionalVariationSum X F P π ω :=
  add_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (abs_nonneg _)

/-- A repeated endpoint contributes exactly zero, not merely an almost-everywhere zero. -/
theorem conditionalVariationSum_term_eq_zero (π : TimePartition T) (i : Fin π.size)
    (hi : π.left i = π.right i) :
    (fun ω ↦ |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) = 0 := by
  simp [hi, Pi.zero_def]

theorem integrable_conditionalVariationSum (hi : ∀ t, Integrable (X t) P)
    (π : TimePartition T) : Integrable (conditionalVariationSum X F P π) P := by
  change Integrable (fun ω ↦ (∑ i, |P[X (π.left i) - X (π.right i) |
    F (π.left i)] ω|) + |X T ω - 0|) P
  simpa only [Pi.add_def, sub_zero] using
    (integrable_finsetSum Finset.univ (fun i _ ↦
      (integrable_condExp (f := X (π.left i) - X (π.right i)) (m := F (π.left i))).abs)).add
      (hi T).abs

theorem eConditionalVariationOnPartition_eq_ofReal_integral
    (hi : ∀ t, Integrable (X t) P) (π : TimePartition T) :
    eConditionalVariationOnPartition X F P π =
      ENNReal.ofReal (∫ ω, conditionalVariationSum X F P π ω ∂P) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_conditionalVariationSum hi π)
    (Eventually.of_forall (conditionalVariationSum_nonneg π))).symm

theorem eConditionalVariationOnPartition_le (π : TimePartition T) :
    eConditionalVariationOnPartition X F P π ≤ eConditionalVariation X F P :=
  le_iSup_of_le T (le_iSup (fun π : TimePartition T ↦
    eConditionalVariationOnPartition X F P π) π)

/-- The zero-horizon partition still retains the initial-to-zero terminal contribution. -/
theorem conditionalVariationSum_empty :
    conditionalVariationSum X F P TimePartition.empty = fun ω ↦ |X 0 ω| := by
  funext ω
  simp [conditionalVariationSum, TimePartition.empty, TimePartition.left, TimePartition.right]

/-- Every finite-time first moment is dominated by the whole-half-line conditional variation. -/
theorem lintegral_abs_le_eConditionalVariation (t : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal |X t ω| ∂P) ≤ eConditionalVariation X F P := by
  apply le_trans ?_ (eConditionalVariationOnPartition_le (X := X) (F := F) (P := P)
    (TimePartition.single t))
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  change |X t ω| ≤ (∑ i, |P[X ((TimePartition.single t).left i) -
    X ((TimePartition.single t).right i) | F ((TimePartition.single t).left i)] ω|) +
      |X t ω - 0|
  rw [sub_zero]
  exact le_add_of_nonneg_left (sum_nonneg fun _ _ ↦ abs_nonneg _)

section FiniteMeasure

variable [IsFiniteMeasure P]

/-- The explicit tail is the source conditional increment from `T` to artificial zero. -/
theorem conditionalVariationSum_ae_eq_terminal_condExp (ha : Adapted F X)
    (hi : ∀ t, Integrable (X t) P) (π : TimePartition T) :
    conditionalVariationSum X F P π =ᵐ[P] fun ω ↦
      (∑ i, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) +
        |P[X T - 0 | F T] ω| := by
  have he := condExp_of_stronglyMeasurable (F.le T) (ha.stronglyAdapted T) (hi T)
  filter_upwards [] with ω
  change (∑ i, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) + |X T ω - 0| = _
  simp only [sub_zero, he]

private theorem integral_conditional_decrement (hX : Supermartingale X F P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, |P[X s - X t | F s] ω| ∂P) = (∫ ω, X s ω ∂P) - ∫ ω, X t ω ∂P := by
  have he : P[X s - X t | F s] =ᵐ[P] X s - P[X t | F s] := by
    simpa only [condExp_of_stronglyMeasurable (F.le s) (hX.stronglyMeasurable s)
      (hX.integrable s)] using condExp_sub (hX.integrable s) (hX.integrable t) (F s)
  have hn : 0 ≤ᵐ[P] P[X s - X t | F s] := by
    filter_upwards [he, hX.condExp_ae_le hst] with ω heω hω
    simpa only [heω, Pi.sub_apply, Pi.zero_apply] using sub_nonneg.mpr hω
  calc
    (∫ ω, |P[X s - X t | F s] ω| ∂P) = ∫ ω, P[X s - X t | F s] ω ∂P :=
      integral_congr_ae (hn.mono fun _ hω ↦ abs_of_nonneg hω)
    _ = ∫ ω, (X s - X t) ω ∂P := integral_condExp (F.le s)
    _ = (∫ ω, X s ω ∂P) - ∫ ω, X t ω ∂P :=
      integral_sub (hX.integrable s) (hX.integrable t)

private theorem integral_conditionalVariationSum_of_nonneg (hX : Supermartingale X F P)
    (hn : ∀ t, 0 ≤ᵐ[P] X t) (π : TimePartition T) :
    (∫ ω, conditionalVariationSum X F P π ω ∂P) = ∫ ω, X 0 ω ∂P := by
  have hsum := π.sum_increment (fun t ↦ ∫ ω, X t ω ∂P)
  have htail : (∫ ω, |X T ω - 0| ∂P) = ∫ ω, X T ω ∂P := by
    exact integral_congr_ae ((hn T).mono fun _ hω ↦ by simp [abs_of_nonneg hω])
  change (∫ ω, (∑ i, |P[X (π.left i) - X (π.right i) |
    F (π.left i)] ω|) + |X T ω - 0| ∂P) = _
  rw [integral_add
    (integrable_finsetSum Finset.univ (fun i _ ↦
      (integrable_condExp (f := X (π.left i) - X (π.right i))
        (m := F (π.left i))).abs)) (by simpa using (hX.integrable T).abs),
    integral_finsetSum _ (fun i _ ↦
      (integrable_condExp (f := X (π.left i) - X (π.right i))
        (m := F (π.left i))).abs), htail]
  simp_rw [integral_conditional_decrement hX (π.left_le_right _)]
  simp only [TimePartition.increment, sum_sub_distrib] at hsum ⊢
  linarith

/-- A nonnegative supermartingale has the same terminal-zero conditional variation
on every partition: its initial mean. -/
theorem _root_.MeasureTheory.Supermartingale.eConditionalVariationOnPartition_eq_of_nonneg
    (hX : Supermartingale X F P) (hn : ∀ t, 0 ≤ᵐ[P] X t) (π : TimePartition T) :
    eConditionalVariationOnPartition X F P π = ENNReal.ofReal (∫ ω, X 0 ω ∂P) := by
  rw [eConditionalVariationOnPartition_eq_ofReal_integral hX.integrable,
    integral_conditionalVariationSum_of_nonneg hX hn]

theorem _root_.MeasureTheory.Supermartingale.eConditionalVariation_eq_of_nonneg
    (hX : Supermartingale X F P) (hn : ∀ t, 0 ≤ᵐ[P] X t) :
    eConditionalVariation X F P = ENNReal.ofReal (∫ ω, X 0 ω ∂P) := by
  apply le_antisymm
  · exact iSup_le fun T ↦ iSup_le fun π ↦
      (hX.eConditionalVariationOnPartition_eq_of_nonneg hn π).le
  · rw [← hX.eConditionalVariationOnPartition_eq_of_nonneg hn TimePartition.empty]
    exact eConditionalVariationOnPartition_le _

omit [IsFiniteMeasure P] in
private theorem conditionalVariationSum_sub_le (hiX : ∀ t, Integrable (X t) P)
    (hiY : ∀ t, Integrable (Y t) P) (π : TimePartition T) :
    conditionalVariationSum (X - Y) F P π ≤ᵐ[P]
      conditionalVariationSum X F P π + conditionalVariationSum Y F P π := by
  have he (i : Fin π.size) :
      P[(X - Y) (π.left i) - (X - Y) (π.right i) | F (π.left i)] =ᵐ[P]
        P[X (π.left i) - X (π.right i) | F (π.left i)] -
          P[Y (π.left i) - Y (π.right i) | F (π.left i)] := by
    have hid : (X - Y) (π.left i) - (X - Y) (π.right i) =
        (X (π.left i) - X (π.right i)) - (Y (π.left i) - Y (π.right i)) := by
      ext ω
      simp only [Pi.sub_apply]
      ring
    rw [hid]
    exact condExp_sub ((hiX _).sub (hiX _)) ((hiY _).sub (hiY _)) _
  filter_upwards [ae_all_iff.mpr he] with ω heω
  simp only [conditionalVariationSum, Pi.add_apply, Pi.sub_apply, sub_zero]
  have hs : (∑ i, |P[(X - Y) (π.left i) - (X - Y) (π.right i) | F (π.left i)] ω|) ≤
      (∑ i, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) +
        ∑ i, |P[Y (π.left i) - Y (π.right i) | F (π.left i)] ω| := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro i _
    rw [heω i]
    exact abs_sub _ _
  have ht := abs_sub (X T ω) (Y T ω)
  simp only [Pi.sub_apply] at hs
  linarith

/-- The global bound includes the final term `E|X T - Y T|`, which cancels
the negative terminal means in the telescoping internal-increment estimate. -/
theorem _root_.MeasureTheory.Supermartingale.eConditionalVariation_sub_le_of_nonneg
    (hX : Supermartingale X F P) (hY : Supermartingale Y F P)
    (hnX : ∀ t, 0 ≤ᵐ[P] X t) (hnY : ∀ t, 0 ≤ᵐ[P] Y t) :
    eConditionalVariation (X - Y) F P ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + ∫ ω, Y 0 ω ∂P) := by
  apply iSup_le
  intro T
  apply iSup_le
  intro π
  rw [eConditionalVariationOnPartition_eq_ofReal_integral (X := X - Y)
    (fun t ↦ (hX.integrable t).sub (hY.integrable t))]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ ω, conditionalVariationSum (X - Y) F P π ω ∂P) ≤
        ∫ ω, conditionalVariationSum X F P π ω + conditionalVariationSum Y F P π ω ∂P :=
      integral_mono_ae
        (integrable_conditionalVariationSum (fun t ↦ (hX.integrable t).sub (hY.integrable t)) π)
        ((integrable_conditionalVariationSum hX.integrable π).add
          (integrable_conditionalVariationSum hY.integrable π))
        (conditionalVariationSum_sub_le hX.integrable hY.integrable π)
    _ = (∫ ω, X 0 ω ∂P) + ∫ ω, Y 0 ω ∂P := by
      rw [integral_add (integrable_conditionalVariationSum hX.integrable π)
        (integrable_conditionalVariationSum hY.integrable π),
        integral_conditionalVariationSum_of_nonneg hX hnX,
        integral_conditionalVariationSum_of_nonneg hY hnY]

theorem _root_.MeasureTheory.Supermartingale.hasFiniteConditionalVariation_sub_of_nonneg
    (hX : Supermartingale X F P) (hY : Supermartingale Y F P)
    (hnX : ∀ t, 0 ≤ᵐ[P] X t) (hnY : ∀ t, 0 ≤ᵐ[P] Y t) :
    HasFiniteConditionalVariation (X - Y) F P :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hX.eConditionalVariation_sub_le_of_nonneg hY hnX hnY)

/-- Protter III.17, easy direction: a difference of nonnegative right-continuous
supermartingales is a quasimartingale on the whole half-line. -/
theorem _root_.MeasureTheory.Supermartingale.isQuasimartingale_sub_of_nonneg
    (hX : Supermartingale X F P) (hY : Supermartingale Y F P) (hF : F.IsUsual P)
    (hrX : HasRightContinuousPaths X P) (hrY : HasRightContinuousPaths Y P)
    (hnX : ∀ t, 0 ≤ᵐ[P] X t) (hnY : ∀ t, 0 ≤ᵐ[P] Y t) :
    IsQuasimartingale (X - Y) F P := by
  refine ⟨(hX.stronglyAdapted.sub hY.stronglyAdapted).adapted, ?_,
    fun t ↦ (hX.integrable t).sub (hY.integrable t),
    hX.hasFiniteConditionalVariation_sub_of_nonneg hY hnX hnY⟩
  have hcX := hX.hasCadlagPaths_of_rightContinuous hF hrX
  have hcY := hY.hasCadlagPaths_of_rightContinuous hF hrY
  simpa only [sub_eq_add_neg, Pi.neg_def] using hcX.add (hcY.continuous_comp continuous_neg)

end FiniteMeasure

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Positive continuous linear functionals on real `L¹`

On a finite measure space, a positive continuous linear functional on real `L¹` is integration
against a finite measure dominated by the reference measure.  The representing measure is bounded
by the operator norm of the functional times the reference measure.  Consequently its
Radon--Nikodym density is essentially bounded by the same constant.

This is a small measure-theoretic interface intended for separation arguments such as Yan's
theorem.  The finite reference measure hypothesis includes the main probability-space use case.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Classical ENNReal NNReal MeasureTheory Topology symmDiff

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- Positivity of a real continuous linear functional on `L¹`: it maps nonnegative elements to
nonnegative real numbers. -/
def IsPositiveL1Functional (L : (α →₁[μ] ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f, 0 ≤ f → 0 ≤ L f

private lemma indicatorConstLp_one_nonneg {s : Set α} (hs : MeasurableSet s) :
    0 ≤ indicatorConstLp (μ := μ) 1 hs (measure_ne_top μ s) (1 : ℝ) := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hs)
    (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs]
  · simp [Set.indicator_of_notMem hxs]

/-- The value assigned by a positive `L¹` functional to a measurable set, obtained by applying
the functional to its indicator. -/
def positiveFunctionalSetValue (L : (α →₁[μ] ℝ) →L[ℝ] ℝ) (s : Set α)
    (hs : MeasurableSet s) : ℝ :=
  L (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))

lemma positiveFunctionalSetValue_nonneg {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) {s : Set α} (hs : MeasurableSet s) :
    0 ≤ positiveFunctionalSetValue L s hs :=
  hL _ (indicatorConstLp_one_nonneg hs)

private lemma positiveFunctionalSetValue_hasSum {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise fun i j ↦ Disjoint (f i) (f j)) :
    HasSum (fun i ↦ positiveFunctionalSetValue L (f i) (hf i))
      (positiveFunctionalSetValue L (⋃ i, f i) (MeasurableSet.iUnion hf)) := by
  let u : ℕ → Set α := fun n ↦ ⋃ i ∈ Finset.range n, f i
  have hu_meas : ∀ n, MeasurableSet (u n) := fun n ↦ by
    dsimp [u]
    measurability
  have hu_succ : ∀ n, u (n + 1) = u n ∪ f n := by
    intro n
    ext x
    simp only [u, Finset.mem_range, mem_iUnion, exists_prop, mem_union]
    constructor
    · rintro ⟨i, hi, hxi⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, hxi⟩
      · exact Or.inr hxi
    · rintro (⟨i, hi, hxi⟩ | hxn)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hxi⟩
      · exact ⟨n, Nat.lt_succ_self n, hxn⟩
  have hu_disj : ∀ n, Disjoint (u n) (f n) := by
    intro n
    rw [Set.disjoint_left]
    intro x hxu hxn
    simp only [u, Finset.mem_range, mem_iUnion, exists_prop] at hxu
    obtain ⟨i, hin, hxi⟩ := hxu
    exact (hdisj (Nat.ne_of_lt hin)).le_bot ⟨hxi, hxn⟩
  have hindicator : ∀ n,
      indicatorConstLp (μ := μ) 1 (hu_meas n) (measure_ne_top μ (u n)) (1 : ℝ) =
        ∑ i ∈ Finset.range n,
          indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℝ) := by
    intro n
    induction n with
    | zero =>
        simp [u, indicatorConstLp_empty]
    | succ n ih =>
        have heq :
            indicatorConstLp (μ := μ) 1 (hu_meas (n + 1))
                (measure_ne_top μ (u (n + 1))) (1 : ℝ) =
              indicatorConstLp 1 ((hu_meas n).union (hf n))
                (measure_ne_top μ (u n ∪ f n)) (1 : ℝ) := by
          apply (indicatorConstLp_inj (hu_meas (n + 1)) (measure_ne_top μ (u (n + 1)))
            ((hu_meas n).union (hf n)) (measure_ne_top μ (u n ∪ f n)) one_ne_zero).2
          filter_upwards [] with x
          rw [hu_succ]
        rw [heq, indicatorConstLp_disjoint_union (hu_meas n) (hf n)
          (measure_ne_top μ (u n)) (measure_ne_top μ (f n)) (hu_disj n),
          Finset.sum_range_succ, ih]
  have hu_subset_tail : ∀ n, u n ∆ (⋃ i, f i) ⊆ ⋃ i ≥ n, f i := by
    intro n x hx
    simp only [u, Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop] at hx ⊢
    rcases hx with ⟨hxu, hxU⟩ | ⟨hxU, hxu⟩
    · exact False.elim (hxU (by grind))
    · obtain ⟨i, hxi⟩ := hxU
      have hin : n ≤ i := by
        by_contra hni
        exact hxu ⟨i, Nat.lt_of_not_ge hni, hxi⟩
      exact ⟨i, hin, hxi⟩
  have htail : Tendsto (μ ∘ fun n ↦ ⋃ i ≥ n, f i) atTop (𝓝 0) :=
    tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (μ := μ) (fun i ↦ (hf i).nullMeasurableSet) hdisj
  have hsymm : Tendsto (fun n ↦ μ (u n ∆ (⋃ i, f i))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ ↦ bot_le) (fun n ↦ measure_mono (hu_subset_tail n))
  have hindicator_tendsto : Tendsto
      (fun n ↦ indicatorConstLp (μ := μ) 1 (hu_meas n) (measure_ne_top μ (u n)) (1 : ℝ))
      atTop
      (𝓝 (indicatorConstLp 1 (MeasurableSet.iUnion hf)
        (measure_ne_top μ (⋃ i, f i)) (1 : ℝ))) :=
    tendsto_indicatorConstLp_set ENNReal.one_ne_top hsymm
  have hvalue_tendsto : Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, positiveFunctionalSetValue L (f i) (hf i)) atTop
      (𝓝 (positiveFunctionalSetValue L (⋃ i, f i) (MeasurableSet.iUnion hf))) := by
    have h := L.continuous.continuousAt.tendsto.comp hindicator_tendsto
    convert h using 1
    · funext n
      simp only [Function.comp_apply, positiveFunctionalSetValue]
      rw [hindicator n, map_sum]
    · rfl
  exact (hasSum_iff_tendsto_nat_of_nonneg
    (fun i ↦ positiveFunctionalSetValue_nonneg hL (hf i)) _).2 hvalue_tendsto

/-- The signed measure obtained by applying a positive `L¹` functional to indicator functions. -/
def positiveFunctionalSignedMeasure (L : (α →₁[μ] ℝ) →L[ℝ] ℝ)
    (hL : IsPositiveL1Functional L) : SignedMeasure α where
  measureOf' s := if hs : MeasurableSet s then positiveFunctionalSetValue L s hs else 0
  empty' := by simp [positiveFunctionalSetValue, indicatorConstLp_empty]
  not_measurable' s hs := dif_neg hs
  m_iUnion' := by
    intro f hf hdisj
    simpa only [dif_pos (MeasurableSet.iUnion hf), dif_pos (hf _)] using
      positiveFunctionalSetValue_hasSum hL hf hdisj

@[simp]
lemma positiveFunctionalSignedMeasure_apply {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) {s : Set α} (hs : MeasurableSet s) :
    positiveFunctionalSignedMeasure L hL s =
      L (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) := by
  simp [positiveFunctionalSignedMeasure, positiveFunctionalSetValue, hs]

lemma positiveFunctionalSignedMeasure_nonneg {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) : 0 ≤ positiveFunctionalSignedMeasure L hL := by
  intro s hs
  rw [positiveFunctionalSignedMeasure_apply hL hs]
  exact hL _ (indicatorConstLp_one_nonneg hs)

/-- The finite positive measure representing a positive continuous linear functional on real
`L¹`. -/
def positiveFunctionalMeasure (L : (α →₁[μ] ℝ) →L[ℝ] ℝ)
    (hL : IsPositiveL1Functional L) : Measure α :=
  (positiveFunctionalSignedMeasure L hL).toMeasureOfZeroLE Set.univ MeasurableSet.univ
    ((VectorMeasure.le_restrict_univ_iff_le _ _).2 (positiveFunctionalSignedMeasure_nonneg hL))

instance positiveFunctionalMeasure_isFinite (L : (α →₁[μ] ℝ) →L[ℝ] ℝ)
    (hL : IsPositiveL1Functional L) : IsFiniteMeasure (positiveFunctionalMeasure L hL) := by
  unfold positiveFunctionalMeasure
  infer_instance

lemma positiveFunctionalMeasure_real_apply {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) {s : Set α} (hs : MeasurableSet s) :
    (positiveFunctionalMeasure L hL).real s =
      L (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) := by
  let hσ := (VectorMeasure.le_restrict_univ_iff_le _ _).2
    (positiveFunctionalSignedMeasure_nonneg hL)
  have hreal := SignedMeasure.toMeasureOfZeroLE_real_apply
    (positiveFunctionalSignedMeasure L hL) hσ MeasurableSet.univ hs
  rw [Set.univ_inter, positiveFunctionalSignedMeasure_apply hL hs] at hreal
  simpa [positiveFunctionalMeasure] using hreal

/-- The representing measure is bounded by the operator norm of the functional times the
reference measure. -/
theorem positiveFunctionalMeasure_le {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) :
    positiveFunctionalMeasure L hL ≤ ‖L‖₊ • μ := by
  rw [Measure.le_iff]
  intro s hs
  refine (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (measure_ne_top (‖L‖₊ • μ) s)).mp ?_
  rw [← measureReal_def, ← measureReal_def, positiveFunctionalMeasure_real_apply hL hs,
    measureReal_nnreal_smul_apply]
  calc
    L (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))
        ≤ ‖L (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ‖L‖ * ‖indicatorConstLp (μ := μ) 1 hs (measure_ne_top μ s) (1 : ℝ)‖ :=
      L.le_opNorm _
    _ = ‖L‖ * μ.real s := by
      rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
      simp
    _ = (‖L‖₊ : ℝ) * μ.real s := by simp

/-- The representing measure is absolutely continuous with respect to the reference measure. -/
theorem positiveFunctionalMeasure_absolutelyContinuous {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) : positiveFunctionalMeasure L hL ≪ μ :=
  Measure.absolutelyContinuous_of_le_smul (positiveFunctionalMeasure_le hL)

lemma positiveFunctionalDominated {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) :
    DominatedFinMeasAdditive μ
      (weightedSMul (positiveFunctionalMeasure L hL) : Set α → ℝ →L[ℝ] ℝ) ‖L‖ := by
  simpa using DominatedFinMeasAdditive.of_measure_le_smul (by simp)
    (positiveFunctionalMeasure_le hL)
    (dominatedFinMeasAdditive_weightedSMul (F := ℝ) (positiveFunctionalMeasure L hL))
    zero_le_one

omit [IsFiniteMeasure μ] in
private lemma indicatorConstLp_eq_smul_one {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : ℝ) :
    indicatorConstLp (μ := μ) 1 hs hμs c =
      c • indicatorConstLp 1 hs hμs (1 : ℝ) := by
  ext1
  grw [Lp.coeFn_smul, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  filter_upwards [] with x
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs]
  · simp [Set.indicator_of_notMem hxs]

/-- The `setToL1` extension associated with the representing measure is the original
functional. -/
theorem positiveFunctional_setToL1_eq {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (f : α →₁[μ] ℝ) :
    L1.setToL1 (positiveFunctionalDominated hL) f = L f := by
  induction f using Lp.induction (hp_ne_top := ENNReal.one_ne_top) with
  | @indicatorConst c s hs hμs =>
      rw [L1.setToL1_simpleFunc_indicatorConst (positiveFunctionalDominated hL) hs hμs,
        weightedSMul_apply, positiveFunctionalMeasure_real_apply hL hs]
      change L (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) • c =
        L (indicatorConstLp 1 hs hμs.ne c)
      rw [indicatorConstLp_eq_smul_one hs hμs.ne c, map_smul]
      simp [smul_eq_mul, mul_comm]
  | @add f g hf hg hfg hf_eq hg_eq =>
      rw [map_add, map_add, hf_eq, hg_eq]
  | isClosed =>
      exact isClosed_eq (L1.setToL1 (positiveFunctionalDominated hL)).continuous L.continuous

/-- Every `L¹(μ)` representative is integrable for the representing measure. -/
theorem integrable_positiveFunctionalMeasure {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (f : α →₁[μ] ℝ) :
    Integrable (fun x ↦ f x) (positiveFunctionalMeasure L hL) :=
  (L1.integrable_coeFn f).of_measure_le_smul (by simp) (positiveFunctionalMeasure_le hL)

/-- Integration of any real `L¹(μ)` element against the representing measure recovers the
functional. -/
theorem integral_positiveFunctionalMeasure {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (f : α →₁[μ] ℝ) :
    ∫ x, f x ∂(positiveFunctionalMeasure L hL) = L f := by
  let ν := positiveFunctionalMeasure L hL
  let hν : DominatedFinMeasAdditive ν (weightedSMul ν : Set α → ℝ →L[ℝ] ℝ) 1 :=
    dominatedFinMeasAdditive_weightedSMul ν
  calc
    ∫ x, f x ∂ν = setToFun ν (weightedSMul ν) hν f := integral_eq_setToFun _
    _ = setToFun μ (weightedSMul ν) (positiveFunctionalDominated hL) f := by
      symm
      exact setToFun_congr_measure_of_integrable (‖L‖₊ : ℝ≥0∞) (by simp)
        (positiveFunctionalMeasure_le hL) (positiveFunctionalDominated hL) hν f
        (L1.integrable_coeFn f)
    _ = L1.setToL1 (positiveFunctionalDominated hL) f :=
      L1.setToFun_eq_setToL1 (positiveFunctionalDominated hL) f
    _ = L f := positiveFunctional_setToL1_eq hL f

/-- A nonzero positive functional has a nonzero representing measure. -/
theorem positiveFunctionalMeasure_ne_zero {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (hL0 : L ≠ 0) :
    positiveFunctionalMeasure L hL ≠ 0 := by
  intro hν
  apply hL0
  ext f
  have h := integral_positiveFunctionalMeasure hL f
  rw [hν] at h
  simpa using h.symm

/-- The Radon--Nikodym density of the representing measure with respect to `μ`. -/
def positiveFunctionalDensity (L : (α →₁[μ] ℝ) →L[ℝ] ℝ)
    (hL : IsPositiveL1Functional L) (x : α) : ℝ :=
  ((positiveFunctionalMeasure L hL).rnDeriv μ x).toReal

lemma measurable_positiveFunctionalDensity {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) : Measurable (positiveFunctionalDensity L hL) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma positiveFunctionalDensity_nonneg {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (x : α) : 0 ≤ positiveFunctionalDensity L hL x :=
  ENNReal.toReal_nonneg

/-- The representing density is essentially bounded by the operator norm. -/
theorem positiveFunctionalDensity_le_norm {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) :
    positiveFunctionalDensity L hL ≤ᵐ[μ] fun _ ↦ ‖L‖ := by
  let ν := positiveFunctionalMeasure L hL
  have hrn : ν.rnDeriv μ ≤ᵐ[μ] fun _ ↦ (‖L‖₊ : ℝ≥0∞) := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
      fun s hs _ ↦ ?_
    rw [setLIntegral_const]
    exact (Measure.setLIntegral_rnDeriv_le s).trans <| by
      simpa [Measure.coe_nnreal_smul_apply] using positiveFunctionalMeasure_le hL s
  filter_upwards [hrn, Measure.rnDeriv_lt_top ν μ] with x hx hxtop
  exact (ENNReal.toReal_le_toReal hxtop.ne (by simp)).2 hx

/-- Density form of the representation theorem. -/
theorem integral_positiveFunctionalDensity {L : (α →₁[μ] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (f : α →₁[μ] ℝ) :
    ∫ x, positiveFunctionalDensity L hL x * f x ∂μ = L f := by
  change ∫ x, ((positiveFunctionalMeasure L hL).rnDeriv μ x).toReal * f x ∂μ = L f
  rw [integral_toReal_rnDeriv_mul (positiveFunctionalMeasure_absolutelyContinuous hL),
    integral_positiveFunctionalMeasure hL f]

end MeasureTheory

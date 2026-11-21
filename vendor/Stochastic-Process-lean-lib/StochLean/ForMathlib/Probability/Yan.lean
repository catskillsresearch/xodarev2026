/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import StochLean.ForMathlib.MeasureTheory.Function.PositiveFunctionalL1
public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.BoundedInProbability

/-!
# Yan separation on `L¹`

This file develops the geometric core of Yan's theorem.  The lower hull of a convex family of
integrable random variables is separated from positive indicators.  The resulting positive
continuous functionals are represented by bounded densities using
`PositiveFunctionalL1.lean`.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Classical ENNReal NNReal MeasureTheory Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

/-- Boundedness in probability for a set of `L¹` equivalence classes. -/
def IsBoundedInProbabilityL1 (K : Set (Ω →₁[Q] ℝ)) : Prop :=
  ∀ η : ℝ≥0∞, 0 < η → ∃ r : ℝ, 0 < r ∧
    ∀ f ∈ K, Q {ω | 1 ≤ ‖r * f ω‖} ≤ η

/-- The image in `L¹` of a family of integrable real random variables. -/
def integrableToL1Set (β : Set (Ω → ℝ))
    (hβint : ∀ f ∈ β, Integrable f Q) : Set (Ω →₁[Q] ℝ) :=
  {g | ∃ f, ∃ hf : f ∈ β, g = (hβint f hf).toL1 f}

lemma zero_mem_integrableToL1Set {β : Set (Ω → ℝ)}
    (hβint : ∀ f ∈ β, Integrable f Q) (hβ0 : (0 : Ω → ℝ) ∈ β) :
    (0 : Ω →₁[Q] ℝ) ∈ integrableToL1Set β hβint := by
  refine ⟨0, hβ0, ?_⟩
  exact (Integrable.toL1_zero (hβint 0 hβ0)).symm

lemma convex_integrableToL1Set {β : Set (Ω → ℝ)}
    (hβint : ∀ f ∈ β, Integrable f Q) (hβconv : Convex ℝ β) :
    Convex ℝ (integrableToL1Set β hβint) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hy
  have hmem : a • f + b • g ∈ β := hβconv hf hg ha hb hab
  refine ⟨a • f + b • g, hmem, ?_⟩
  rw [Integrable.toL1_add, Integrable.toL1_smul', Integrable.toL1_smul']
  · exact (hβint f hf).smul a
  · exact (hβint g hg).smul b

lemma isBoundedInProbabilityL1_integrableToL1Set {β : Set (Ω → ℝ)}
    (hβint : ∀ f ∈ β, Integrable f Q) (hβ : IsBoundedInProbability β Q) :
    IsBoundedInProbabilityL1 (integrableToL1Set β hβint) := by
  intro η hη
  obtain ⟨r, hr, htail⟩ := hβ η hη
  refine ⟨r, hr, ?_⟩
  intro g hg
  obtain ⟨f, hf, rfl⟩ := hg
  have hset : {ω | 1 ≤ ‖r * (hβint f hf).toL1 f ω‖} =ᵐ[Q]
      {ω | 1 ≤ ‖r * f ω‖} := by
    filter_upwards [(hβint f hf).coeFn_toL1] with ω hω
    change (1 ≤ ‖r * (hβint f hf).toL1 f ω‖) = (1 ≤ ‖r * f ω‖)
    rw [hω]
  rw [measure_congr hset]
  exact htail f hf

/-- The solid lower hull used in Yan's separation argument. -/
def yanLowerHull (K : Set (Ω →₁[Q] ℝ)) : Set (Ω →₁[Q] ℝ) :=
  {z | ∃ f ∈ K, ∃ g : Ω →₁[Q] ℝ, 0 ≤ g ∧ z = f - g}

lemma convex_yanLowerHull {K : Set (Ω →₁[Q] ℝ)} (hK : Convex ℝ K) :
    Convex ℝ (yanLowerHull K) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  obtain ⟨f, hf, g, hg, rfl⟩ := hx
  obtain ⟨f', hf', g', hg', rfl⟩ := hy
  refine ⟨a • f + b • f', hK hf hf' ha hb hab, a • g + b • g', ?_, ?_⟩
  · rw [← Lp.coeFn_nonneg]
    filter_upwards [Lp.coeFn_smul a g, Lp.coeFn_smul b g', Lp.coeFn_add (a • g) (b • g'),
      (Lp.coeFn_nonneg g).2 hg, (Lp.coeFn_nonneg g').2 hg'] with ω h₁ h₂ h₃ h₄ h₅
    rw [h₃]
    simp only [Pi.zero_apply, Pi.add_apply]
    rw [h₁, h₂]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha h₄) (mul_nonneg hb h₅)
  · module

lemma subset_yanLowerHull {K : Set (Ω →₁[Q] ℝ)} : K ⊆ yanLowerHull K := by
  intro f hf
  exact ⟨f, hf, 0, le_rfl, (sub_zero f).symm⟩

lemma yanLowerHull_sub_nonneg {K : Set (Ω →₁[Q] ℝ)} {f : Ω →₁[Q] ℝ}
    (hf : f ∈ yanLowerHull K) {g : Ω →₁[Q] ℝ} (hg : 0 ≤ g) :
    f - g ∈ yanLowerHull K := by
  obtain ⟨x, hx, y, hy, rfl⟩ := hf
  refine ⟨x, hx, y + g, add_nonneg hy hg, ?_⟩
  abel

/-- The quantitative heart of Yan separation: above every measurable set of positive measure
there is a positive indicator which stays a positive `L¹` distance away from the solid lower
hull. -/
lemma exists_pos_indicator_not_mem_closure_yanLowerHull [IsFiniteMeasure Q]
    {K : Set (Ω →₁[Q] ℝ)} (hK : IsBoundedInProbabilityL1 K)
    {A : Set Ω} (hA : MeasurableSet A) (hQA : 0 < Q A) :
    ∃ c : ℝ, 0 < c ∧
      c • indicatorConstLp (μ := Q) 1 hA (measure_ne_top Q A) (1 : ℝ) ∉
        closure (yanLowerHull K) := by
  let q : ℝ := Q.real A
  have hq : 0 < q := by
    exact ENNReal.toReal_pos hQA.ne' (measure_ne_top Q A)
  let η : ℝ≥0∞ := ENNReal.ofReal (q / 4)
  have hη : 0 < η := ENNReal.ofReal_pos.mpr (div_pos hq zero_lt_four)
  obtain ⟨r, hr, htail⟩ := hK η hη
  let c : ℝ := 2 / r
  let z : Ω →₁[Q] ℝ := c • indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)
  refine ⟨c, div_pos (by norm_num) hr, ?_⟩
  change z ∉ closure (yanLowerHull K)
  intro hz
  let δ : ℝ := q / (4 * r)
  have hδ : 0 < δ := div_pos hq (mul_pos zero_lt_four hr)
  obtain ⟨x, hx, hzx⟩ := Metric.mem_closure_iff.1 hz δ hδ
  obtain ⟨f, hf, y, hy, hxy⟩ := hx
  have hxf : x ≤ f := by
    rw [hxy]
    exact sub_le_self f hy
  let T : Set Ω := {ω | 1 ≤ ‖r * f ω‖}
  let D : Set Ω := {ω | 1 / r ≤ ‖(z - x) ω‖}
  have hcover : ∀ᵐ ω ∂Q, ω ∈ A → ω ∈ T ∪ D := by
    filter_upwards [indicatorConstLp_coeFn (μ := Q) (p := 1) (hs := hA)
        (hμs := measure_ne_top Q A) (c := (1 : ℝ)),
      Lp.coeFn_smul c (indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)),
      Lp.coeFn_sub z x, (Lp.coeFn_le x f).2 hxf] with ω hind hsmul hsub hle hωA
    by_cases hωT : ω ∈ T
    · exact Or.inl hωT
    · right
      have hrf : ‖r * f ω‖ < 1 := lt_of_not_ge hωT
      have hrf' : r * f ω < 1 := by
        exact (le_abs_self (r * f ω)).trans_lt (by simpa [Real.norm_eq_abs] using hrf)
      have hf_lt : f ω < 1 / r := by
        apply (lt_div_iff₀ hr).2
        simpa only [one_mul, mul_comm] using hrf'
      have hx_lt : x ω < 1 / r := hle.trans_lt hf_lt
      have hzω : z ω = 2 / r := by
        dsimp only [z, c]
        rw [hsmul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hind, Set.indicator_of_mem hωA]
        simp [c]
      have hdiff : 1 / r < z ω - x ω := by
        rw [hzω]
        rw [show 2 / r = 1 / r + 1 / r by ring]
        linarith
      dsimp only [D]
      change 1 / r ≤ ‖(z - x) ω‖
      rw [hsub]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        hdiff.le.trans (le_abs_self (z ω - x ω))
  have hQA_union : Q A ≤ Q (T ∪ D) :=
    measure_mono_ae (hcover.mono fun _ h ↦ h)
  have hq_union : q ≤ Q.real (T ∪ D) := by
    exact ENNReal.toReal_mono (measure_ne_top Q (T ∪ D)) hQA_union
  have hT : Q.real T ≤ q / 4 := by
    have h := htail f hf
    change Q T ≤ η at h
    have := ENNReal.toReal_mono (by simp [η]) h
    change (Q T).toReal ≤ q / 4
    simpa [η, ENNReal.toReal_ofReal (div_nonneg hq.le zero_le_four)] using this
  have hmarkov : (1 / r) * Q.real D ≤ ‖z - x‖ := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ := Q) (f := fun ω ↦ ‖(z - x) ω‖)
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (L1.integrable_coeFn (z - x)).norm (1 / r)
    change (1 / r) * Q.real D ≤ _ at h
    simpa only [← L1.norm_eq_integral_norm] using h
  have hnorm : ‖z - x‖ < (1 / r) * (q / 4) := by
    have : ‖z - x‖ < δ := by simpa only [dist_eq_norm] using hzx
    calc
      ‖z - x‖ < δ := this
      _ = (1 / r) * (q / 4) := by
        dsimp only [δ]
        field_simp
  have he : 0 < 1 / r := one_div_pos.mpr hr
  have hmul : (1 / r) * Q.real D < (1 / r) * (q / 4) := hmarkov.trans_lt hnorm
  have hD : Q.real D < q / 4 := by
    nlinarith
  have hunion : Q.real (T ∪ D) < q / 2 := by
    calc
      Q.real (T ∪ D) ≤ Q.real T + Q.real D := measureReal_union_le T D
      _ < q / 4 + q / 4 := add_lt_add_of_le_of_lt hT hD
      _ = q / 2 := by ring
  linarith

/-- A local Yan separator.  On every positive-measure set `A` there is a positive continuous
functional which is uniformly bounded above on `K` and whose representing measure charges `A`.
This is the ingredient needed by the maximal-support argument. -/
theorem exists_positiveFunctional_boundedOn_and_measure_pos [IsFiniteMeasure Q]
    {K : Set (Ω →₁[Q] ℝ)} (hKconv : Convex ℝ K) (hK0 : (0 : Ω →₁[Q] ℝ) ∈ K)
    (hKbip : IsBoundedInProbabilityL1 K) {A : Set Ω} (hA : MeasurableSet A)
    (hQA : 0 < Q A) :
    ∃ (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L) (C : ℝ),
      (∀ f ∈ K, L f ≤ C) ∧ 0 < positiveFunctionalMeasure L hL A := by
  obtain ⟨c, hc, hz⟩ :=
    exists_pos_indicator_not_mem_closure_yanLowerHull hKbip hA hQA
  let z : Ω →₁[Q] ℝ :=
    c • indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)
  change z ∉ closure (yanLowerHull K) at hz
  obtain ⟨L, u, hLu, huz⟩ := geometric_hahn_banach_closed_point
    (convex_yanLowerHull hKconv).closure isClosed_closure hz
  have hzeroC : (0 : Ω →₁[Q] ℝ) ∈ yanLowerHull K := subset_yanLowerHull hK0
  have hu : 0 < u := by
    have := hLu 0 (subset_closure hzeroC)
    simpa using this
  have hLpos : IsPositiveL1Functional L := by
    intro g hg
    by_contra hLg
    have hLg' : L g < 0 := lt_of_not_ge hLg
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (u / (-L g))
    have hng : 0 ≤ n • g := nsmul_nonneg hg n
    have hneg : -(n • g) ∈ yanLowerHull K := by
      simpa only [zero_sub] using yanLowerHull_sub_nonneg hzeroC hng
    have hsep := hLu (-(n • g)) (subset_closure hneg)
    have hden : 0 < -L g := neg_pos.mpr hLg'
    have hun : u < (n : ℝ) * (-L g) := by
      have := (div_lt_iff₀ hden).mp hn
      simpa only [Nat.cast_ofNat, mul_comm] using this
    have hvalue : L (-(n • g)) = (n : ℝ) * (-L g) := by
      simp [map_neg, map_nsmul, nsmul_eq_mul]
    rw [hvalue] at hsep
    exact (not_lt_of_ge hun.le) hsep
  refine ⟨L, hLpos, u, ?_, ?_⟩
  · intro f hf
    exact (hLu f (subset_closure (subset_yanLowerHull hf))).le
  · have hLz : 0 < L z := hu.trans huz
    have hLind : 0 < L (indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)) := by
      have hmul : 0 < c * L (indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)) := by
        simpa only [z, map_smul, smul_eq_mul] using hLz
      exact pos_of_mul_pos_right hmul hc.le
    have hreal := positiveFunctionalMeasure_real_apply hLpos hA
    have hνreal : 0 < (positiveFunctionalMeasure L hLpos).real A := by
      rwa [hreal]
    exact (ENNReal.toReal_pos_iff.mp hνreal).1

/-- Raw-function form of the local separator.  The representing finite measure has a bounded
density with respect to `Q`, charges the prescribed positive-measure set, and gives a uniform
one-sided integral bound on the original family. -/
theorem exists_dominatedMeasure_boundedOn_and_measure_pos [IsFiniteMeasure Q]
    {β : Set (Ω → ℝ)} (hβconv : Convex ℝ β) (hβ0 : (0 : Ω → ℝ) ∈ β)
    (hβint : ∀ f ∈ β, Integrable f Q) (hβbip : IsBoundedInProbability β Q)
    {A : Set Ω} (hA : MeasurableSet A) (hQA : 0 < Q A) :
    ∃ (ν : Measure Ω) (_ : IsFiniteMeasure ν) (D : ℝ≥0),
      ν ≤ D • Q ∧ 0 < ν A ∧
        ∃ C : ℝ, ∀ f ∈ β, Integrable f ν ∧ ∫ ω, f ω ∂ν ≤ C := by
  let K := integrableToL1Set β hβint
  obtain ⟨L, hL, C, hLC, hνA⟩ := exists_positiveFunctional_boundedOn_and_measure_pos
    (convex_integrableToL1Set hβint hβconv)
    (zero_mem_integrableToL1Set hβint hβ0)
    (isBoundedInProbabilityL1_integrableToL1Set hβint hβbip) hA hQA
  let ν := positiveFunctionalMeasure L hL
  refine ⟨ν, positiveFunctionalMeasure_isFinite L hL, ‖L‖₊,
    positiveFunctionalMeasure_le hL, hνA, C, ?_⟩
  intro f hf
  let f₁ : Ω →₁[Q] ℝ := (hβint f hf).toL1 f
  have hfK : f₁ ∈ K := ⟨f, hf, rfl⟩
  have hac : ν ≪ Q := positiveFunctionalMeasure_absolutelyContinuous hL
  have hae : (fun ω ↦ f₁ ω) =ᵐ[ν] f :=
    hac.ae_eq (hβint f hf).coeFn_toL1
  have hfint : Integrable f ν :=
    (integrable_positiveFunctionalMeasure hL f₁).congr hae
  refine ⟨hfint, ?_⟩
  calc
    ∫ ω, f ω ∂ν = ∫ ω, f₁ ω ∂ν := integral_congr_ae hae.symm
    _ = L f₁ := integral_positiveFunctionalMeasure hL f₁
    _ ≤ C := hLC f₁ hfK

/-- The measurable essential support of the measure represented by a positive `L¹` functional. -/
def positiveFunctionalSupport [IsFiniteMeasure Q]
    (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L) : Set Ω :=
  {ω | (positiveFunctionalMeasure L hL).rnDeriv Q ω ≠ 0}

lemma measurableSet_positiveFunctionalSupport [IsFiniteMeasure Q]
    (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L) :
    MeasurableSet (positiveFunctionalSupport L hL) := by
  rw [show positiveFunctionalSupport L hL =
      {ω | (positiveFunctionalMeasure L hL).rnDeriv Q ω = 0}ᶜ by
    ext ω
    simp [positiveFunctionalSupport]]
  exact ((Measure.measurable_rnDeriv (positiveFunctionalMeasure L hL) Q)
    (measurableSet_singleton 0)).compl

/-- Null sets for the representing measure are exactly those whose intersection with its
essential support is `Q`-null. -/
theorem positiveFunctionalMeasure_apply_eq_zero_iff [IsFiniteMeasure Q]
    (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L) (A : Set Ω) :
    positiveFunctionalMeasure L hL A = 0 ↔
      Q (positiveFunctionalSupport L hL ∩ A) = 0 := by
  rw [← Measure.withDensity_rnDeriv_eq (positiveFunctionalMeasure L hL) Q
    (positiveFunctionalMeasure_absolutelyContinuous hL)]
  exact withDensity_apply_eq_zero
    (Measure.measurable_rnDeriv (positiveFunctionalMeasure L hL) Q)

lemma positiveFunctionalMeasure_support_compl [IsFiniteMeasure Q]
    (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L) :
    positiveFunctionalMeasure L hL (positiveFunctionalSupport L hL)ᶜ = 0 := by
  rw [positiveFunctionalMeasure_apply_eq_zero_iff]
  simp

/-- Full `Q`-support is precisely the missing ingredient for equivalence of the representing
measure and `Q`. -/
theorem positiveFunctionalMeasure_equivalent_of_support_compl_null [IsFiniteMeasure Q]
    (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L)
    (hfull : Q (positiveFunctionalSupport L hL)ᶜ = 0) :
    positiveFunctionalMeasure L hL ≪ Q ∧ Q ≪ positiveFunctionalMeasure L hL := by
  refine ⟨positiveFunctionalMeasure_absolutelyContinuous hL, ?_⟩
  intro A hνA
  have hSA : Q (positiveFunctionalSupport L hL ∩ A) = 0 :=
    (positiveFunctionalMeasure_apply_eq_zero_iff L hL A).mp hνA
  apply measure_mono_null
    (show A ⊆ (positiveFunctionalSupport L hL ∩ A) ∪
        (positiveFunctionalSupport L hL)ᶜ by
      intro ω hω
      by_cases hωS : ω ∈ positiveFunctionalSupport L hL
      · exact Or.inl ⟨hωS, hω⟩
      · exact Or.inr hωS)
  exact measure_union_null hSA hfull

lemma positiveFunctionalSupport_sdiff_null_of_ac [IsFiniteMeasure Q]
    {L M : (Ω →₁[Q] ℝ) →L[ℝ] ℝ}
    {hL : IsPositiveL1Functional L} {hM : IsPositiveL1Functional M}
    (hac : positiveFunctionalMeasure L hL ≪ positiveFunctionalMeasure M hM) :
    Q (positiveFunctionalSupport L hL \ positiveFunctionalSupport M hM) = 0 := by
  have hν := hac (positiveFunctionalMeasure_support_compl M hM)
  have hQ := (positiveFunctionalMeasure_apply_eq_zero_iff L hL
    (positiveFunctionalSupport M hM)ᶜ).mp hν
  simpa only [sdiff_eq, inter_comm] using hQ

lemma positiveFunctionalSupport_measureReal_mono_of_ac [IsFiniteMeasure Q]
    {L M : (Ω →₁[Q] ℝ) →L[ℝ] ℝ}
    {hL : IsPositiveL1Functional L} {hM : IsPositiveL1Functional M}
    (hac : positiveFunctionalMeasure L hL ≪ positiveFunctionalMeasure M hM) :
    Q.real (positiveFunctionalSupport L hL) ≤
      Q.real (positiveFunctionalSupport M hM) := by
  let SL := positiveFunctionalSupport L hL
  let SM := positiveFunctionalSupport M hM
  have hnull : Q (SL \ SM) = 0 := positiveFunctionalSupport_sdiff_null_of_ac hac
  have hmeasure : Q SL ≤ Q SM := by
    calc
      Q SL ≤ Q (SM ∪ (SL \ SM)) := measure_mono (by
        intro ω hω
        by_cases hωM : ω ∈ SM
        · exact Or.inl hωM
        · exact Or.inr ⟨hω, hωM⟩)
      _ ≤ Q SM + Q (SL \ SM) := measure_union_le _ _
      _ = Q SM := by rw [hnull, add_zero]
  exact ENNReal.toReal_mono (measure_ne_top Q SM) hmeasure

/-- Adding a separator which charges the complement of the first separator's support strictly
increases support mass, provided both component measures are dominated by the new one. -/
lemma positiveFunctionalSupport_measureReal_lt_of_compl_charge [IsFiniteMeasure Q]
    {L M N : (Ω →₁[Q] ℝ) →L[ℝ] ℝ}
    {hL : IsPositiveL1Functional L} {hM : IsPositiveL1Functional M}
    {hN : IsPositiveL1Functional N}
    (hLN : positiveFunctionalMeasure L hL ≪ positiveFunctionalMeasure N hN)
    (hMN : positiveFunctionalMeasure M hM ≪ positiveFunctionalMeasure N hN)
    (hcharge : 0 < positiveFunctionalMeasure M hM
      (positiveFunctionalSupport L hL)ᶜ) :
    Q.real (positiveFunctionalSupport L hL) <
      Q.real (positiveFunctionalSupport N hN) := by
  let SL := positiveFunctionalSupport L hL
  let SM := positiveFunctionalSupport M hM
  let SN := positiveFunctionalSupport N hN
  have hMout : 0 < Q (SM ∩ SLᶜ) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have := (positiveFunctionalMeasure_apply_eq_zero_iff M hM SLᶜ).mpr hzero
    exact hcharge.ne' this
  have hMNnull : Q (SM \ SN) = 0 := positiveFunctionalSupport_sdiff_null_of_ac hMN
  have hNout : 0 < Q (SN \ SL) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hsub : SM ∩ SLᶜ ⊆ (SN \ SL) ∪ (SM \ SN) := by
      intro ω hω
      by_cases hωN : ω ∈ SN
      · exact Or.inl ⟨hωN, hω.2⟩
      · exact Or.inr ⟨hω.1, hωN⟩
    have : Q (SM ∩ SLᶜ) = 0 := measure_mono_null hsub (measure_union_null hzero hMNnull)
    exact hMout.ne' this
  have hLNnull : Q (SL \ SN) = 0 := positiveFunctionalSupport_sdiff_null_of_ac hLN
  have hLNreal : Q.real (SL \ SN) = 0 := by simp [measureReal_def, hLNnull]
  have hNoutreal : 0 < Q.real (SN \ SL) :=
    ENNReal.toReal_pos hNout.ne' (measure_ne_top Q (SN \ SL))
  have hsplitL := measureReal_inter_add_sdiff
    (μ := Q) (s := SL) (measurableSet_positiveFunctionalSupport N hN)
  have hsplitN := measureReal_inter_add_sdiff
    (μ := Q) (s := SN) (measurableSet_positiveFunctionalSupport L hL)
  dsimp only [SL, SN] at hLNreal hNoutreal hsplitL hsplitN ⊢
  rw [hLNreal, add_zero] at hsplitL
  rw [inter_comm (positiveFunctionalSupport N hN)] at hsplitN
  linarith

/-- A positive functional equipped with a finite one-sided bound on `K`. -/
structure YanSeparator (K : Set (Ω →₁[Q] ℝ)) where
  functional : (Ω →₁[Q] ℝ) →L[ℝ] ℝ
  positive : IsPositiveL1Functional functional
  boundConstant : ℝ
  le_bound : ∀ f ∈ K, functional f ≤ boundConstant

def YanSeparator.supportMass [IsFiniteMeasure Q] {K : Set (Ω →₁[Q] ℝ)}
    (S : YanSeparator K) : ℝ :=
  Q.real (positiveFunctionalSupport S.functional S.positive)

def YanSeparator.add {K : Set (Ω →₁[Q] ℝ)}
    (S T : YanSeparator K) : YanSeparator K where
  functional := S.functional + T.functional
  positive := by
    intro f hf
    exact add_nonneg (S.positive f hf) (T.positive f hf)
  boundConstant := S.boundConstant + T.boundConstant
  le_bound := by
    intro f hf
    exact add_le_add (S.le_bound f hf) (T.le_bound f hf)

lemma positiveFunctionalMeasure_ac_add_left [IsFiniteMeasure Q]
    {L M : (Ω →₁[Q] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (hM : IsPositiveL1Functional M) :
    positiveFunctionalMeasure L hL ≪
      positiveFunctionalMeasure (L + M) (fun f hf ↦ add_nonneg (hL f hf) (hM f hf)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hsum
  let e : Ω →₁[Q] ℝ := indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)
  have he : 0 ≤ e := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [indicatorConstLp_coeFn (μ := Q) (p := 1) (hs := hA)
      (hμs := measure_ne_top Q A) (c := (1 : ℝ))] with ω hω
    rw [hω]
    by_cases hωA : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hωA]
  let hadd : IsPositiveL1Functional (L + M) :=
    fun f hf ↦ add_nonneg (hL f hf) (hM f hf)
  have hsumreal : (L + M) e = 0 := by
    have hreal : (positiveFunctionalMeasure (L + M) hadd).real A = 0 := by
      simp [measureReal_def, hsum]
    rwa [positiveFunctionalMeasure_real_apply hadd hA] at hreal
  have hLe : L e = 0 := by
    change L e + M e = 0 at hsumreal
    linarith [hL e he, hM e he]
  have hreal : (positiveFunctionalMeasure L hL).real A = 0 := by
    rw [positiveFunctionalMeasure_real_apply hL hA]
    exact hLe
  exact ((positiveFunctionalMeasure L hL A).toReal_eq_zero_iff.mp hreal).resolve_right
    (measure_ne_top _ _)

lemma positiveFunctionalMeasure_ac_add_right [IsFiniteMeasure Q]
    {L M : (Ω →₁[Q] ℝ) →L[ℝ] ℝ}
    (hL : IsPositiveL1Functional L) (hM : IsPositiveL1Functional M) :
    positiveFunctionalMeasure M hM ≪
      positiveFunctionalMeasure (L + M) (fun f hf ↦ add_nonneg (hL f hf) (hM f hf)) := by
  simpa only [add_comm] using positiveFunctionalMeasure_ac_add_left hM hL

theorem exists_yanSeparator_charging [IsFiniteMeasure Q]
    {K : Set (Ω →₁[Q] ℝ)} (hKconv : Convex ℝ K) (hK0 : (0 : Ω →₁[Q] ℝ) ∈ K)
    (hKbip : IsBoundedInProbabilityL1 K) {A : Set Ω} (hA : MeasurableSet A)
    (hQA : 0 < Q A) :
    ∃ S : YanSeparator K, 0 < positiveFunctionalMeasure S.functional S.positive A := by
  obtain ⟨L, hL, C, hbound, hApos⟩ :=
    exists_positiveFunctional_boundedOn_and_measure_pos hKconv hK0 hKbip hA hQA
  exact ⟨⟨L, hL, C, hbound⟩, hApos⟩

/-- Countable positive mixtures preserve the one-sided bound.  Moreover every component
representing measure is absolutely continuous with respect to the mixture.  This is the analytic
engine in the countable maximal-support step of Yan's theorem. -/
theorem positiveFunctional_tsum [IsFiniteMeasure Q] {K : Set (Ω →₁[Q] ℝ)}
    (L : ℕ → (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : ∀ n, IsPositiveL1Functional (L n))
    (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hsum : Summable fun n ↦ w n • L n) (C : ℕ → ℝ)
    (hbound : ∀ n f, f ∈ K → L n f ≤ C n)
    (hCsum : Summable fun n ↦ w n * C n) :
    let Llim : (Ω →₁[Q] ℝ) →L[ℝ] ℝ := ∑' n, w n • L n
    ∃ hLlim : IsPositiveL1Functional Llim,
      (∀ f ∈ K, Llim f ≤ ∑' n, w n * C n) ∧
        ∀ n, positiveFunctionalMeasure (L n) (hL n) ≪
          positiveFunctionalMeasure Llim hLlim := by
  dsimp only
  let Llim : (Ω →₁[Q] ℝ) →L[ℝ] ℝ := ∑' n, w n • L n
  have heval (f : Ω →₁[Q] ℝ) : Llim f = ∑' n, w n * L n f := by
    dsimp only [Llim]
    change (ContinuousLinearMap.apply ℝ ℝ f) (∑' n, w n • L n) = _
    rw [(ContinuousLinearMap.apply ℝ ℝ f).map_tsum hsum]
    apply tsum_congr
    intro n
    simp [smul_eq_mul]
  have hLlim : IsPositiveL1Functional Llim := by
    intro f hf
    rw [heval]
    exact tsum_nonneg fun n ↦ mul_nonneg (hw n).le (hL n f hf)
  refine ⟨hLlim, ?_, ?_⟩
  · intro f hf
    rw [heval]
    have hevalsum : Summable fun n ↦ w n * L n f := by
      simpa only [ContinuousLinearMap.apply_apply, map_smul, smul_eq_mul] using
        (ContinuousLinearMap.apply ℝ ℝ f).summable hsum
    exact hevalsum.tsum_le_tsum
      (fun n ↦ mul_le_mul_of_nonneg_left (hbound n f hf) (hw n).le) hCsum
  · intro n
    apply Measure.AbsolutelyContinuous.mk
    intro A hA hmixA
    let e : Ω →₁[Q] ℝ := indicatorConstLp 1 hA (measure_ne_top Q A) (1 : ℝ)
    have he_nonneg : 0 ≤ e := by
      rw [← Lp.coeFn_nonneg]
      filter_upwards [indicatorConstLp_coeFn (μ := Q) (p := 1) (hs := hA)
        (hμs := measure_ne_top Q A) (c := (1 : ℝ))] with ω hω
      rw [hω]
      by_cases hωA : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hωA]
    have hmixreal : Llim e = 0 := by
      change positiveFunctionalMeasure Llim hLlim A = 0 at hmixA
      have hrealzero : (positiveFunctionalMeasure Llim hLlim).real A = 0 := by
        simp [measureReal_def, hmixA]
      rwa [positiveFunctionalMeasure_real_apply hLlim hA] at hrealzero
    have htermsum : ∑' k, w k * L k e = 0 := by
      rw [← heval]
      exact hmixreal
    have hterm_nonneg : ∀ k, 0 ≤ w k * L k e := fun k ↦
      mul_nonneg (hw k).le (hL k e he_nonneg)
    have hterms_summable : Summable fun k ↦ w k * L k e := by
      simpa only [ContinuousLinearMap.apply_apply, map_smul, smul_eq_mul] using
        (ContinuousLinearMap.apply ℝ ℝ e).summable hsum
    have hterm_le : w n * L n e ≤ ∑' k, w k * L k e := by
      simpa using hterms_summable.sum_le_tsum {n} (fun k _ ↦ hterm_nonneg k)
    have hLne : L n e = 0 := by
      have : w n * L n e = 0 := by
        rw [htermsum] at hterm_le
        exact le_antisymm hterm_le (hterm_nonneg n)
      exact (mul_eq_zero.mp this).resolve_left (hw n).ne'
    have hreal : (positiveFunctionalMeasure (L n) (hL n)).real A = 0 := by
      rw [positiveFunctionalMeasure_real_apply (hL n) hA]
      exact hLne
    exact ((positiveFunctionalMeasure (L n) (hL n) A).toReal_eq_zero_iff.mp hreal).resolve_right
      (measure_ne_top _ _)

/-- If a countable family of local separators detects every `Q`-positive set, its positive
summable mixture has representing measure equivalent to `Q`. -/
theorem positiveFunctional_tsum_equivalent [IsFiniteMeasure Q] {K : Set (Ω →₁[Q] ℝ)}
    (L : ℕ → (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : ∀ n, IsPositiveL1Functional (L n))
    (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hsum : Summable fun n ↦ w n • L n) (C : ℕ → ℝ)
    (hbound : ∀ n f, f ∈ K → L n f ≤ C n)
    (hCsum : Summable fun n ↦ w n * C n)
    (hdetect : ∀ A : Set Ω, MeasurableSet A → 0 < Q A →
      ∃ n, 0 < positiveFunctionalMeasure (L n) (hL n) A) :
    let Llim : (Ω →₁[Q] ℝ) →L[ℝ] ℝ := ∑' n, w n • L n
    ∃ hLlim : IsPositiveL1Functional Llim,
      (∀ f ∈ K, Llim f ≤ ∑' n, w n * C n) ∧
        positiveFunctionalMeasure Llim hLlim ≪ Q ∧
        Q ≪ positiveFunctionalMeasure Llim hLlim := by
  dsimp only
  obtain ⟨hLlim, hboundlim, hac⟩ :=
    positiveFunctional_tsum L hL w hw hsum C hbound hCsum
  refine ⟨hLlim, hboundlim, positiveFunctionalMeasure_absolutelyContinuous hLlim, ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hmixA
  by_contra hQA
  have hQApos : 0 < Q A := (pos_iff_ne_zero).2 hQA
  obtain ⟨n, hn⟩ := hdetect A hA hQApos
  have := hac n hmixA
  exact (not_lt_of_ge (by simp [this])) hn

/-- Yan's theorem on `L¹`: a convex family containing zero and bounded in probability admits a
positive continuous functional, uniformly bounded on the family, whose representing measure is
equivalent to the reference probability measure. -/
theorem exists_equivalent_positiveFunctional_boundedOn [IsProbabilityMeasure Q]
    {K : Set (Ω →₁[Q] ℝ)} (hKconv : Convex ℝ K) (hK0 : (0 : Ω →₁[Q] ℝ) ∈ K)
    (hKbip : IsBoundedInProbabilityL1 K) :
    ∃ (L : (Ω →₁[Q] ℝ) →L[ℝ] ℝ) (hL : IsPositiveL1Functional L) (C : ℝ),
      (∀ f ∈ K, L f ≤ C) ∧
        positiveFunctionalMeasure L hL ≪ Q ∧ Q ≪ positiveFunctionalMeasure L hL := by
  have hQuniv : 0 < Q (Set.univ : Set Ω) := by simp
  obtain ⟨S₀, _⟩ := exists_yanSeparator_charging hKconv hK0 hKbip MeasurableSet.univ hQuniv
  let masses : Set ℝ := Set.range (fun S : YanSeparator K ↦ S.supportMass)
  have hmasses_ne : masses.Nonempty := ⟨S₀.supportMass, ⟨S₀, rfl⟩⟩
  have hmasses_bdd : BddAbove masses := by
    refine ⟨Q.real Set.univ, ?_⟩
    rintro x ⟨S, rfl⟩
    exact measureReal_mono (subset_univ _) (measure_ne_top Q Set.univ)
  let s : ℝ := sSup masses
  have happ : ∀ n : ℕ, ∃ S : YanSeparator K,
      s - (1 : ℝ) / (n + 1) < S.supportMass := by
    intro n
    have htpos : 0 < (1 : ℝ) / (n + 1) := by positivity
    have hlt : s - (1 : ℝ) / (n + 1) < s := sub_lt_self s htpos
    obtain ⟨x, ⟨S, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hmasses_ne hlt
    exact ⟨S, hx⟩
  choose S hS using happ
  let g : ℕ → ℝ := fun n ↦ 1 / 2 / 2 ^ n
  let d : ℕ → ℝ := fun n ↦ 1 + ‖(S n).functional‖ + |(S n).boundConstant|
  let w : ℕ → ℝ := fun n ↦ g n / d n
  have hgpos : ∀ n, 0 < g n := fun n ↦ by
    dsimp only [g]
    positivity
  have hdpos : ∀ n, 0 < d n := fun n ↦ by
    dsimp only [d]
    positivity
  have hwpos : ∀ n, 0 < w n := fun n ↦ div_pos (hgpos n) (hdpos n)
  have hnorm_le : ∀ n, ‖w n • (S n).functional‖ ≤ g n := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos n)]
    dsimp only [w]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (hdpos n)).2
    have hg0 := (hgpos n).le
    have hnorm0 := norm_nonneg (S n).functional
    have habs0 := abs_nonneg (S n).boundConstant
    dsimp only [d]
    nlinarith [mul_nonneg hg0 hnorm0, mul_nonneg hg0 habs0]
  have hsum : Summable fun n ↦ w n • (S n).functional := by
    apply (summable_geometric_two' 1).of_norm_bounded
    intro n
    simpa only [g] using hnorm_le n
  have hCnorm_le : ∀ n, ‖w n * (S n).boundConstant‖ ≤ g n := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hwpos n)]
    dsimp only [w]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (hdpos n)).2
    have hg0 := (hgpos n).le
    have hnorm0 := norm_nonneg (S n).functional
    have habs0 := abs_nonneg (S n).boundConstant
    dsimp only [d]
    nlinarith [mul_nonneg hg0 hnorm0, mul_nonneg hg0 habs0]
  have hCsum : Summable fun n ↦ w n * (S n).boundConstant := by
    apply (summable_geometric_two' 1).of_norm_bounded
    intro n
    simpa only [g] using hCnorm_le n
  let Llim : (Ω →₁[Q] ℝ) →L[ℝ] ℝ := ∑' n, w n • (S n).functional
  obtain ⟨hLlim, hboundlim, haclim⟩ := positiveFunctional_tsum
    (fun n ↦ (S n).functional) (fun n ↦ (S n).positive) w hwpos hsum
    (fun n ↦ (S n).boundConstant) (fun n ↦ (S n).le_bound) hCsum
  let Clim : ℝ := ∑' n, w n * (S n).boundConstant
  let Slim : YanSeparator K := ⟨Llim, hLlim, Clim, hboundlim⟩
  have hmass_upper : Slim.supportMass ≤ s := by
    exact le_csSup hmasses_bdd ⟨Slim, rfl⟩
  have hmass_lower : s ≤ Slim.supportMass := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < ε :=
      (tendsto_order.1
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 ε hε
    obtain ⟨n, hn⟩ := hev.exists
    have hmono : (S n).supportMass ≤ Slim.supportMass :=
      positiveFunctionalSupport_measureReal_mono_of_ac (haclim n)
    linarith [hS n]
  have hmasseq : Slim.supportMass = s := le_antisymm hmass_upper hmass_lower
  have hfull : Q (positiveFunctionalSupport Llim hLlim)ᶜ = 0 := by
    by_contra hnull
    have hpos : 0 < Q (positiveFunctionalSupport Llim hLlim)ᶜ :=
      (pos_iff_ne_zero).2 hnull
    obtain ⟨T, hTcharge⟩ := exists_yanSeparator_charging hKconv hK0 hKbip
      (measurableSet_positiveFunctionalSupport Llim hLlim).compl hpos
    let U : YanSeparator K := Slim.add T
    have hleft : positiveFunctionalMeasure Slim.functional Slim.positive ≪
        positiveFunctionalMeasure U.functional U.positive := by
      exact positiveFunctionalMeasure_ac_add_left Slim.positive T.positive
    have hright : positiveFunctionalMeasure T.functional T.positive ≪
        positiveFunctionalMeasure U.functional U.positive := by
      exact positiveFunctionalMeasure_ac_add_right Slim.positive T.positive
    have hstrict : Slim.supportMass < U.supportMass :=
      positiveFunctionalSupport_measureReal_lt_of_compl_charge hleft hright hTcharge
    have hUle : U.supportMass ≤ s := le_csSup hmasses_bdd ⟨U, rfl⟩
    rw [hmasseq] at hstrict
    exact (not_lt_of_ge hUle) hstrict
  refine ⟨Llim, hLlim, Clim, hboundlim, ?_⟩
  exact positiveFunctionalMeasure_equivalent_of_support_compl_null Llim hLlim hfull

/-- **Yan's theorem**, in the form used by the Bichteler--Dellacherie argument.  The separating
probability measure is equivalent to `Q`, has a bounded density with respect to `Q`, and gives a
uniform one-sided integral bound on the original convex family. -/
theorem yan [Nonempty Ω] [IsProbabilityMeasure Q]
    {β : Set (Ω → ℝ)} (hβconv : Convex ℝ β) (hβ0 : (0 : Ω → ℝ) ∈ β)
    (hβint : ∀ f ∈ β, Integrable f Q) (hβbip : IsBoundedInProbability β Q) :
    ∃ (R : ProbabilityMeasure Ω) (D : ℝ≥0) (C : ℝ),
      (R : Measure Ω) ≪ Q ∧ Q ≪ (R : Measure Ω) ∧
        (R : Measure Ω) ≤ D • Q ∧
          ∀ f ∈ β, Integrable f (R : Measure Ω) ∧ ∫ ω, f ω ∂R ≤ C := by
  let K := integrableToL1Set β hβint
  obtain ⟨L, hL, C₀, hbound, hνQ, hQν⟩ :=
    exists_equivalent_positiveFunctional_boundedOn
      (convex_integrableToL1Set hβint hβconv)
      (zero_mem_integrableToL1Set hβint hβ0)
      (isBoundedInProbabilityL1_integrableToL1Set hβint hβbip)
  let ν : Measure Ω := positiveFunctionalMeasure L hL
  have hνne : ν ≠ 0 := by
    intro hzero
    have hQzero : Q (Set.univ : Set Ω) = 0 := hQν (s := Set.univ) (by simp [ν, hzero])
    have hQone : Q (Set.univ : Set Ω) = 1 := measure_univ
    rw [hQone] at hQzero
    exact one_ne_zero hQzero
  let νf : FiniteMeasure Ω := ⟨ν, positiveFunctionalMeasure_isFinite L hL⟩
  have hνfne : νf ≠ 0 := by
    intro hzero
    apply hνne
    exact congrArg FiniteMeasure.toMeasure hzero
  let R : ProbabilityMeasure Ω := νf.normalize
  have hmass : νf.mass ≠ 0 := νf.mass_nonzero_iff.mpr hνfne
  have hR_eq : (R : Measure Ω) = νf.mass⁻¹ • ν := by
    calc
      (R : Measure Ω) = νf.mass⁻¹ • (νf : Measure Ω) :=
        νf.toMeasure_normalize_eq_of_nonzero hνfne
      _ = νf.mass⁻¹ • ν := rfl
  have hRν : (R : Measure Ω) ≪ ν := by
    rw [hR_eq]
    exact Measure.smul_absolutelyContinuous
  have hνR : ν ≪ (R : Measure Ω) := by
    rw [hR_eq]
    exact Measure.absolutelyContinuous_smul
      (ENNReal.coe_ne_zero.mpr (inv_ne_zero hmass))
  let D : ℝ≥0 := νf.mass⁻¹ * ‖L‖₊
  have hRle : (R : Measure Ω) ≤ D • Q := by
    rw [Measure.le_iff]
    intro A hA
    rw [hR_eq, Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    dsimp only [D]
    rw [ENNReal.coe_mul, mul_assoc]
    have hνle : ν A ≤ (‖L‖₊ : ℝ≥0∞) * Q A := by
      simpa only [ν, Measure.coe_nnreal_smul_apply] using positiveFunctionalMeasure_le hL A
    exact mul_le_mul le_rfl hνle zero_le zero_le
  let C : ℝ := (νf.mass⁻¹ : ℝ) * C₀
  refine ⟨R, D, C, hRν.trans hνQ, hQν.trans hνR, hRle, ?_⟩
  intro f hf
  let f₁ : Ω →₁[Q] ℝ := (hβint f hf).toL1 f
  have hfK : f₁ ∈ K := ⟨f, hf, rfl⟩
  have hfνae : (fun ω ↦ f₁ ω) =ᵐ[ν] f :=
    hνQ.ae_eq (hβint f hf).coeFn_toL1
  have hfνint : Integrable f ν :=
    (integrable_positiveFunctionalMeasure hL f₁).congr hfνae
  have hfRint : Integrable f (R : Measure Ω) := by
    rw [hR_eq]
    exact hfνint.smul_measure_nnreal
  refine ⟨hfRint, ?_⟩
  rw [hR_eq, integral_smul_nnreal_measure]
  change (νf.mass⁻¹ : ℝ) * (∫ ω, f ω ∂ν) ≤ C
  rw [integral_congr_ae hfνae.symm, integral_positiveFunctionalMeasure hL f₁]
  exact mul_le_mul_of_nonneg_left (hbound f₁ hfK) (by positivity)

end ProbabilityTheory

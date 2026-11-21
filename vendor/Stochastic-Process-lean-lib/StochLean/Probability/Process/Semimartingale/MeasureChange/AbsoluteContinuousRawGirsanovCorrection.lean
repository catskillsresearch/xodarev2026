/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousKillingCompensator
public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousPredictableGirsanov
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.StieltjesRealization
public import StochLean.Probability.Process.FiniteVariation.CadlagIntegral
public import StochLean.Probability.Process.Path.Supremum

/-! # The raw-covariation correction under one-way absolute continuity

The Lenglart--Girsanov formula uses the right-value Stieltjes integral
`integral Z_s^{-1} d[M,Z]_s`.  We realize the already selected raw bracket by
an everywhere cadlag locally-FV version and the target-law reciprocal density
by an everywhere cadlag indistinguishable version.  The pathwise Stieltjes
integral then gives an adapted cadlag FV semimartingale under the target law.

Neither realization changes the underlying owners: both are tied back to the
canonical density and raw quadratic covariation by indistinguishability.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- The current-value reciprocal of the forward density.  Lean's totalized
inverse assigns zero at a density zero; under `Q` this branch is null at every
finite time on one common event. -/
noncomputable def absoluteContinuousInverseDensity
    (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ 1 / densityProcess Q P F t ω

theorem adapted_absoluteContinuousInverseDensity
    (hFP : F.IsUsual P) :
    Adapted F (absoluteContinuousInverseDensity Q P F) := by
  intro t
  unfold absoluteContinuousInverseDensity
  exact ((martingale_densityProcess (Q := Q) hFP).stronglyAdapted.adapted t).const_div 1

/-- The actual reciprocal density has target-almost surely cadlag paths. -/
theorem hasCadlagPaths_absoluteContinuousInverseDensity
    (hQP : Q ≪ P) (hFP : F.IsUsual P) :
    HasCadlagPaths (absoluteContinuousInverseDensity Q P F) Q := by
  filter_upwards
      [hQP.ae_le
        (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)),
        ae_forall_densityProcess_pos_of_absoluteContinuous hQP hFP,
        ae_forall_leftLimit_densityProcess_pos_of_absoluteContinuous hQP hFP]
    with ω hcad hpos hleftPos
  constructor
  · intro t
    unfold absoluteContinuousInverseDensity
    convert (hcad.1 t).inv₀ (hpos t).ne' using 1
    ext s
    simp only [one_div, Pi.inv_apply]
  · intro t ht
    refine ⟨1 / leftLimitProcess (densityProcess Q P F) t ω, ?_⟩
    have hlim := (hcad.tendsto_leftLimitProcess ht).inv₀
      (hleftPos t (pos_iff_ne_zero.mpr ht)).ne'
    simpa only [absoluteContinuousInverseDensity, one_div, Pi.inv_apply] using hlim

/-- An everywhere-cadlag adapted representative of the target reciprocal
density. -/
noncomputable def absoluteContinuousInverseDensityCadlagVersion
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    ℝ≥0 → Ω → ℝ :=
  (adapted_absoluteContinuousInverseDensity (Q := Q) hFP).stronglyAdapted
    |>.exists_cadlag_indistinguishable_of_usual hFQ
      (hasCadlagPaths_absoluteContinuousInverseDensity hQP hFP) |>.choose

theorem absoluteContinuousInverseDensityCadlagVersion_properties
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    let W := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
    Indistinguishable (absoluteContinuousInverseDensity Q P F) W Q ∧
      IsStronglyProgressive F W ∧
      ∀ ω, IsCadlagPath (W · ω) := by
  exact (adapted_absoluteContinuousInverseDensity (Q := Q) hFP).stronglyAdapted
    |>.exists_cadlag_indistinguishable_of_usual hFQ
      (hasCadlagPaths_absoluteContinuousInverseDensity hQP hFP) |>.choose_spec

/-- At each fixed time, multiplying the selected cadlag reciprocal-density
version by the density gives the zero/one selector under the source law.  The
only possible discrepancy from the literal reciprocal lies in a target-null
set; the density change-of-measure identity forces the density to vanish there
under the source law. -/
theorem density_mul_inverseVersion_ae
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) (t : ℝ≥0) :
    let V := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
    (fun ω ↦ densityProcess Q P F t ω * V t ω) =ᵐ[P]
      fun ω ↦ if densityProcess Q P F t ω = 0 then 0 else 1 := by
  intro V
  obtain ⟨heV, hpV, _⟩ :=
    absoluteContinuousInverseDensityCadlagVersion_properties hQP hFP hFQ
  let W := absoluteContinuousInverseDensity Q P F
  have haW : Adapted F W := adapted_absoluteContinuousInverseDensity hFP
  have haV : Adapted F V := hpV.stronglyAdapted.adapted
  let E : Set Ω := {ω | W t ω ≠ V t ω}
  have hEt : MeasurableSet[F t] E := by
    rw [show E = {ω | W t ω < V t ω} ∪ {ω | V t ω < W t ω} by
      ext ω
      simp only [E, mem_ofPred_eq, mem_union, ne_eq]
      constructor
      · exact lt_or_gt_of_ne
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h]
    exact (measurableSet_lt (haW t) (haV t)).union
      (measurableSet_lt (haV t) (haW t))
  have hE : MeasurableSet E := F.le t E hEt
  have hQE : Q E = 0 := by
    exact measure_eq_zero_iff_ae_notMem.mpr
      (heV.mono fun ω hω ↦ not_ne_iff.mpr (hω t))
  have hInt : (∫ ω in E, densityProcess Q P F t ω ∂P) = 0 := by
    rw [setIntegral_densityProcess hQP hFP t hEt]
    simp [Measure.real, hQE]
  have hnonneg : 0 ≤ᵐ[P] densityProcess Q P F t :=
    (ae_forall_densityProcess_nonneg (Q := Q) hFP).mono fun _ hω ↦ hω t
  have hzeroR : densityProcess Q P F t =ᵐ[P.restrict E] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hnonneg)
      ((martingale_densityProcess (Q := Q) hFP).integrable t).integrableOn).mp hInt
  have hzero : ∀ᵐ ω ∂P, ω ∈ E → densityProcess Q P F t ω = 0 :=
    (ae_restrict_iff' hE).mp hzeroR
  filter_upwards [hzero] with ω hω
  by_cases hz : densityProcess Q P F t ω = 0
  · simp [hz]
  · have hnotE : ω ∉ E := fun hmem ↦ hz (hω hmem)
    have heq : W t ω = V t ω := not_ne_iff.mp hnotE
    rw [← heq]
    simp [W, absoluteContinuousInverseDensity, hz]

/-- The density times its selected cadlag reciprocal version is
indistinguishable under the source law from the zero/one selector.  Fixed-time
identities are upgraded to one common event through a countable dense set and
right continuity. -/
theorem density_mul_inverseVersion_indistinguishable
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    let V := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
    Indistinguishable (densityProcess Q P F * V)
      (fun t ω ↦ if densityProcess Q P F t ω = 0 then 0 else 1) P := by
  intro V
  obtain ⟨_, _, hcV⟩ :=
    absoluteContinuousInverseDensityCadlagVersion_properties hQP hFP hFQ
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      densityProcess Q P F (TopologicalSpace.denseSeq ℝ≥0 n) ω *
          V (TopologicalSpace.denseSeq ℝ≥0 n) ω =
        if densityProcess Q P F (TopologicalSpace.denseSeq ℝ≥0 n) ω = 0
          then 0 else 1 := by
    rw [ae_all_iff]
    intro n
    exact density_mul_inverseVersion_ae hQP hFP hFQ _
  filter_upwards [hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F), hall]
    with ω hZ hallω
  intro t
  by_cases hzt : densityProcess Q P F t ω = 0
  · simp [hzt]
  · have hWrc : IsRightContinuousPath
        (fun s ↦ densityProcess Q P F s ω * V s ω) :=
      fun s ↦ (hZ.1 s).mul ((hcV ω).1 s)
    have hdense : Dense (Set.range (TopologicalSpace.denseSeq ℝ≥0)) :=
      TopologicalSpace.denseRange_denseSeq ℝ≥0
    obtain ⟨u, _, hu, hlim⟩ := hdense.exists_seq_strictAnti_tendsto t
    have hwithin : Tendsto u atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n ↦
        mem_Ici.mpr (hu n).1.le⟩
    have hlimZ : Tendsto (fun n ↦ densityProcess Q P F (u n) ω) atTop
        (𝓝 (densityProcess Q P F t ω)) :=
      (hZ.1 t).tendsto.comp hwithin
    have hzne : ∀ᶠ n in atTop, densityProcess Q P F (u n) ω ≠ 0 :=
      hlimZ.eventually (isOpen_compl_singleton.mem_nhds hzt)
    have hWone : ∀ᶠ n in atTop,
        densityProcess Q P F (u n) ω * V (u n) ω = 1 := by
      filter_upwards [hzne] with n hzn
      obtain ⟨k, hk⟩ := (hu n).2
      have hd := hallω k
      rw [hk] at hd
      simpa only [hzn, if_false] using hd
    have hlimW : Tendsto
        (fun n ↦ densityProcess Q P F (u n) ω * V (u n) ω) atTop
        (𝓝 (densityProcess Q P F t ω * V t ω)) :=
      (hWrc t).tendsto.comp hwithin
    have hone : Tendsto
        (fun n ↦ densityProcess Q P F (u n) ω * V (u n) ω) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (hWone.mono fun _ hn ↦ hn.symm)
    have heq : densityProcess Q P F t ω * V t ω = 1 :=
      tendsto_nhds_unique hlimW hone
    simpa only [Pi.mul_apply, hzt, if_false] using heq

/-- An everywhere cadlag locally-FV realization of the canonical raw bracket
`[Z,M]`. -/
noncomputable def absoluteContinuousRawCovariationRealization
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P) :
    SemimartingaleBracketRealization
      ((isLocalMartingale_densityProcess (Q := Q) hFP).isSemimartingale hFP)
      (hM.isSemimartingale hFP) hFP :=
  Classical.choice
    (IsSemimartingale.nonempty_bracketRealization
      ((isLocalMartingale_densityProcess (Q := Q) hFP).isSemimartingale hFP)
      (hM.isSemimartingale hFP) hFP)

/-- Protter III.42's literal right-value correction
`integral Z_s^{-1} d[M,Z]_s`, formed from the canonical raw bracket and
reciprocal density representatives. -/
noncomputable def absoluteContinuousRawGirsanovCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    ℝ≥0 → Ω → ℝ := by
  let D := absoluteContinuousRawCovariationRealization (Q := Q) hM hFP
  let W := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
  exact finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W

/-- The raw correction is an adapted cadlag finite-variation target-law
semimartingale. -/
theorem absoluteContinuousRawGirsanovCorrection_properties
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    let A := absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ
    Adapted F A ∧ HasCadlagPaths A Q ∧ HasFiniteVariationPaths A Q ∧
      IsSemimartingale A F Q := by
  let D := absoluteContinuousRawCovariationRealization (Q := Q) hM hFP
  let W := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
  obtain ⟨_, hpW, hcW⟩ :=
    absoluteContinuousInverseDensityCadlagVersion_properties hQP hFP hFQ
  have haW : Adapted F W := hpW.stronglyAdapted.adapted
  have hi (ω : Ω) (T : ℝ≥0) :
      IntegrableOn (W · ω) (Ioc 0 T)
        (totalVariationStieltjes (D.mixed · ω) (D.mixed_bv ω)
          (D.mixed_rc ω)).measure :=
    integrableOn_variationStieltjes_of_progressive_cadlag
      D.mixed D.mixed_bv D.mixed_rc hpW hcW T ω
  have haI : Adapted F
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) :=
    adapted_finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc
      D.mixed_adapted hpW
  have hcI : HasCadlagPaths
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) Q :=
    hasCadlagPaths_finiteVariationIntegral
      (Eventually.of_forall fun ω T ↦ hi ω T)
  have hvI : HasFiniteVariationPaths
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) Q :=
    hasFiniteVariationPaths_finiteVariationIntegral
      (Eventually.of_forall fun ω T ↦ hi ω T)
  have hsI : IsSemimartingale
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) F Q :=
    isSemimartingale_finiteVariationIntegral_of_cadlag
      D.mixed D.mixed_bv D.mixed_rc D.mixed_adapted hFQ haW hcW
  simpa only [absoluteContinuousRawGirsanovCorrection, D, W] using
    And.intro haI (And.intro hcI (And.intro hvI hsI))

/-- The same selected raw correction is an adapted cadlag finite-variation
semimartingale in the source environment.  The construction is pathwise; only
the usual-filtration semimartingale wrapper changes law. -/
theorem absoluteContinuousRawGirsanovCorrection_source_properties
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    let A := absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ
    Adapted F A ∧ HasCadlagPaths A P ∧ HasFiniteVariationPaths A P ∧
      IsSemimartingale A F P := by
  let D := absoluteContinuousRawCovariationRealization (Q := Q) hM hFP
  let W := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
  obtain ⟨_, hpW, hcW⟩ :=
    absoluteContinuousInverseDensityCadlagVersion_properties hQP hFP hFQ
  have haW : Adapted F W := hpW.stronglyAdapted.adapted
  have hi (ω : Ω) (T : ℝ≥0) :
      IntegrableOn (W · ω) (Ioc 0 T)
        (totalVariationStieltjes (D.mixed · ω) (D.mixed_bv ω)
          (D.mixed_rc ω)).measure :=
    integrableOn_variationStieltjes_of_progressive_cadlag
      D.mixed D.mixed_bv D.mixed_rc hpW hcW T ω
  have haI : Adapted F
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) :=
    adapted_finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc
      D.mixed_adapted hpW
  have hcI : HasCadlagPaths
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) P :=
    hasCadlagPaths_finiteVariationIntegral
      (Eventually.of_forall fun ω T ↦ hi ω T)
  have hvI : HasFiniteVariationPaths
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) P :=
    hasFiniteVariationPaths_finiteVariationIntegral
      (Eventually.of_forall fun ω T ↦ hi ω T)
  have hsI : IsSemimartingale
      (finiteVariationIntegral D.mixed D.mixed_bv D.mixed_rc W) F P :=
    isSemimartingale_finiteVariationIntegral_of_cadlag
      D.mixed D.mixed_bv D.mixed_rc D.mixed_adapted hFP haW hcW
  simpa only [absoluteContinuousRawGirsanovCorrection, D, W] using
    And.intro haI (And.intro hcI (And.intro hvI hsI))

/-- On one target-full-measure event, the selected process is exactly the
pathwise right-value Stieltjes integral against the canonical raw bracket.
This is the literal integral appearing in Protter III.42. -/
theorem absoluteContinuousRawGirsanovCorrection_eq_pathStieltjesIntegral_ae
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    let B := densityRawCovariation (Q := Q) hM hFP
    let W := absoluteContinuousInverseDensity Q P F
    ∀ᵐ ω ∂Q, ∃ hv : LocallyBoundedVariationOn (B · ω) univ,
      ∃ hr : IsRightContinuousPath (B · ω), ∀ t,
        absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ t ω =
          pathStieltjesIntegral (B · ω) hv hr (W · ω) t := by
  intro B W
  let D := absoluteContinuousRawCovariationRealization (Q := Q) hM hFP
  let V := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
  obtain ⟨heV, _, _⟩ :=
    absoluteContinuousInverseDensityCadlagVersion_properties hQP hFP hFQ
  filter_upwards [hQP.ae_le D.mixed_eq, heV] with ω heD heW
  have hDfun : (B · ω) = (D.mixed · ω) := funext heD
  have hWfun : (W · ω) = (V · ω) := funext heW
  have hvB : LocallyBoundedVariationOn (B · ω) univ := by
    rw [hDfun]
    exact D.mixed_bv ω
  have hrB : IsRightContinuousPath (B · ω) := by
    rw [hDfun]
    exact D.mixed_rc ω
  refine ⟨hvB, hrB, fun t ↦ ?_⟩
  rw [absoluteContinuousRawGirsanovCorrection]
  change pathStieltjesIntegral (D.mixed · ω) (D.mixed_bv ω)
      (D.mixed_rc ω) (V · ω) t =
    pathStieltjesIntegral (B · ω) hvB hrB (W · ω) t
  exact congrFun (pathStieltjesIntegral_congr
    (hx := D.mixed_bv ω) (hr := D.mixed_rc ω)
    (hy := hvB) (hyr := hrB) hDfun.symm hWfun.symm) t

end ProbabilityTheory

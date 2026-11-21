/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousMartingaleTransfer
public import StochLean.Probability.Process.Semimartingale.MeasureChange.PredictableGirsanov
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.StoppingIntervalLocality
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Associativity
public import StochLean.Probability.Process.Path.LeftRightReconstruction

/-! # Predictable Girsanov theorem under one-way absolute continuity

This file implements Protter III.41.  The reciprocal forward-density left
limit is constructed directly under the target law; no reverse density and no
equivalence assumption is introduced.  Source-law algebra is performed with
globally regular clipped reciprocals and only then localized at the geometric
lower-density exits.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- Reciprocal of the forward density left limit.  At time zero this is zero,
because the project's left-limit process is zero there. -/
noncomputable def absoluteContinuousInverseDensityLeft (Q P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ 1 / leftLimitProcess (densityProcess Q P F) t ω

/-- Under `Q ≪ P`, the canonical density is strictly positive at every
finite time on one target-full-measure event. -/
theorem ae_forall_densityProcess_pos_of_absoluteContinuous
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < densityProcess Q P F t ω := by
  filter_upwards [ae_tendsto_absoluteContinuousDensityExit hQP hF] with ω hω
  intro t
  obtain ⟨n, hn⟩ :=
    (hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
  have hlower := absoluteContinuousDensityThreshold_le_of_lt_exit
    (Q := Q) (P := P) (F := F) hn
  have hthresholdPos : (0 : ℝ) < (absoluteContinuousDensityThreshold n : ℝ) := by
    exact_mod_cast absoluteContinuousDensityThreshold_pos n
  exact hthresholdPos.trans_le hlower

/-- Positive-time density left limits are simultaneously strictly positive
under the target law. -/
theorem ae_forall_leftLimit_densityProcess_pos_of_absoluteContinuous
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t →
      0 < leftLimitProcess (densityProcess Q P F) t ω := by
  filter_upwards [ae_tendsto_absoluteContinuousDensityExit hQP hF,
      hQP.ae_le (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F))]
    with ω hω hcad
  intro t ht
  obtain ⟨n, hn⟩ :=
    (hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).exists
  have hlower := absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit
    (Q := Q) (P := P) (F := F) hcad ht hn.le
  have hthresholdPos : (0 : ℝ) < (absoluteContinuousDensityThreshold n : ℝ) := by
    exact_mod_cast absoluteContinuousDensityThreshold_pos n
  exact hthresholdPos.trans_le hlower

/-- The reciprocal density left limit is adapted.  This is a filtration-only
fact once the source-usual left-limit measurability theorem has been applied. -/
theorem adapted_absoluteContinuousInverseDensityLeft
    (hF : F.IsUsual P) :
    Adapted F (absoluteContinuousInverseDensityLeft Q P F) := by
  have haL := (martingale_densityProcess (Q := Q) hF).stronglyAdapted.adapted
    |>.leftLimitProcess_of_usual hF
      (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F))
  intro t
  unfold absoluteContinuousInverseDensityLeft
  convert (haL t).inv using 1
  ext ω
  simp only [one_div, Pi.inv_apply]

/-- Although reciprocal is discontinuous at zero as a scalar operation, the
actual reciprocal left-density process is càglàd under `Q`: positive-time
left limits never vanish, and the right limit at `t` is the reciprocal of the
strictly positive right-continuous density value `Z_t`. -/
theorem hasCagladPaths_absoluteContinuousInverseDensityLeft
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    HasCagladPaths (absoluteContinuousInverseDensityLeft Q P F) Q := by
  filter_upwards
      [hQP.ae_le (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)),
        ae_forall_densityProcess_pos_of_absoluteContinuous hQP hF,
        ae_forall_leftLimit_densityProcess_pos_of_absoluteContinuous hQP hF]
    with ω hcad hZpos hLpos
  have hL : IsCagladPath (leftLimitProcess (densityProcess Q P F) · ω) :=
    hcad.isCagladPath_leftLimitProcess
  unfold absoluteContinuousInverseDensityLeft
  constructor
  · intro t
    by_cases ht : t = 0
    · subst t
      simpa only [absoluteContinuousInverseDensityLeft,
          show Set.Iic (0 : ℝ≥0) = {0} from Set.Iic_bot] using
        (continuousWithinAt_singleton
          (f := fun s ↦ 1 / leftLimitProcess (densityProcess Q P F) s ω) (x := 0))
    · convert (hL.1 t).inv₀ (hLpos t (pos_iff_ne_zero.mpr ht)).ne' using 1
      ext s
      simp only [one_div, Pi.inv_apply]
  · intro t
    refine ⟨1 / densityProcess Q P F t ω, ?_⟩
    have hright : rightLimitProcess (leftLimitProcess (densityProcess Q P F)) t ω =
        densityProcess Q P F t ω := hcad.rightLimitProcess_leftLimitProcess t
    have hright_ne :
        rightLimitProcess (leftLimitProcess (densityProcess Q P F)) t ω ≠ 0 := by
      rw [hright]
      exact (hZpos t).ne'
    have hlim := (hL.tendsto_rightLimitProcess t).inv₀ hright_ne
    simpa only [one_div, Pi.inv_apply, hcad.rightLimitProcess_leftLimitProcess] using hlim

/-- A globally regular source-law reciprocal.  Clipping the density left
limit at the positive geometric threshold removes the pole at zero. -/
noncomputable def absoluteContinuousClippedInverseDensityLeft
    (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ 1 / max (leftLimitProcess (densityProcess Q P F) t ω)
    (absoluteContinuousDensityThreshold n : ℝ)

theorem adapted_absoluteContinuousClippedInverseDensityLeft
    (hF : F.IsUsual P) (n : ℕ) :
    Adapted F (absoluteContinuousClippedInverseDensityLeft Q P F n) := by
  have haL := (martingale_densityProcess (Q := Q) hF).stronglyAdapted.adapted
    |>.leftLimitProcess_of_usual hF
      (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F))
  intro t
  unfold absoluteContinuousClippedInverseDensityLeft
  exact ((haL t).max measurable_const).const_div 1

theorem hasCagladPaths_absoluteContinuousClippedInverseDensityLeft
    (n : ℕ) :
    HasCagladPaths (absoluteContinuousClippedInverseDensityLeft Q P F n) P := by
  have hthresholdPos : (0 : ℝ) < (absoluteContinuousDensityThreshold n : ℝ) := by
    exact_mod_cast absoluteContinuousDensityThreshold_pos n
  have hf : Continuous
      (fun x : ℝ ↦ 1 / max x (absoluteContinuousDensityThreshold n : ℝ)) := by
    have hinv := (continuous_id.max continuous_const).inv₀
      (fun x ↦ (hthresholdPos.trans_le (le_max_right x _)).ne')
    simpa only [one_div, Pi.inv_def, id_eq] using hinv
  exact (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)
    |>.hasCagladPaths_leftLimitProcess).continuous_comp hf

/-- Before the `n`-th lower-density exit, the clipped reciprocal equals the
actual reciprocal at every positive time. -/
theorem absoluteContinuousClippedInverseDensityLeft_eq_of_le_exit
    {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (hpath : IsCadlagPath (densityProcess Q P F · ω)) (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) ≤ absoluteContinuousDensityExit Q P F n ω) :
    absoluteContinuousClippedInverseDensityLeft Q P F n t ω =
      absoluteContinuousInverseDensityLeft Q P F t ω := by
  unfold absoluteContinuousClippedInverseDensityLeft
    absoluteContinuousInverseDensityLeft
  rw [max_eq_left
    (absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit hpath ht0 ht)]

/-- On the same stochastic interval, multiplying the clipped reciprocal by
the density left limit gives one. -/
theorem leftLimit_densityProcess_mul_clippedInverse_eq_one_of_le_exit
    {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (hpath : IsCadlagPath (densityProcess Q P F · ω)) (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) ≤ absoluteContinuousDensityExit Q P F n ω) :
    leftLimitProcess (densityProcess Q P F) t ω *
        absoluteContinuousClippedInverseDensityLeft Q P F n t ω = 1 := by
  rw [absoluteContinuousClippedInverseDensityLeft_eq_of_le_exit hpath ht0 ht]
  unfold absoluteContinuousInverseDensityLeft
  simpa only [one_div] using mul_inv_cancel₀
    ((absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit hpath ht0 ht |>
      (show (0 : ℝ) < (absoluteContinuousDensityThreshold n : ℝ) by
        exact_mod_cast absoluteContinuousDensityThreshold_pos n).trans_le).ne')

/-- Protter III.41 correction `∫ Z₋⁻¹ d⟨Z,M⟩`, constructed in the target
stochastic-integral environment. -/
noncomputable def absoluteContinuousPredictableGirsanovCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q)
    (hV : HasLocallyIntegrableVariation
      (densityRawCovariation (Q := Q) hM hFP) F P) :
    ℝ≥0 → Ω → ℝ := by
  let A := densityPredictableCovariation (Q := Q) hM hFP hV
  let hA := densityPredictableCovariation_properties (Q := Q) hM hFP hV
  let hAP : IsSemimartingale A F P :=
    hA.2.2.2.1.hasFiniteVariationPaths.isSemimartingale
      hA.1.stronglyAdapted.adapted hFP (Eventually.of_forall hA.2.1)
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hFP
  exact hAQ.stochasticIntegral hFQ
    (adapted_absoluteContinuousInverseDensityLeft (Q := Q) hFP)
    (hasCagladPaths_absoluteContinuousInverseDensityLeft hQP hFP)

/-- The one-way predictable correction is adapted and has càdlàg target-law
paths. -/
theorem absoluteContinuousPredictableGirsanovCorrection_adapted_cadlag
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q)
    (hV : HasLocallyIntegrableVariation
      (densityRawCovariation (Q := Q) hM hFP) F P) :
    Adapted F (absoluteContinuousPredictableGirsanovCorrection
      (Q := Q) hM hQP hFP hFQ hV) ∧
      HasCadlagPaths (absoluteContinuousPredictableGirsanovCorrection
        (Q := Q) hM hQP hFP hFQ hV) Q := by
  let A := densityPredictableCovariation (Q := Q) hM hFP hV
  let hA := densityPredictableCovariation_properties (Q := Q) hM hFP hV
  let hAP : IsSemimartingale A F P :=
    hA.2.2.2.1.hasFiniteVariationPaths.isSemimartingale
      hA.1.stronglyAdapted.adapted hFP (Eventually.of_forall hA.2.1)
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hFP
  let H := absoluteContinuousInverseDensityLeft Q P F
  let haH : Adapted F H := adapted_absoluteContinuousInverseDensityLeft hFP
  let hrH : HasCagladPaths H Q :=
    hasCagladPaths_absoluteContinuousInverseDensityLeft hQP hFP
  rw [absoluteContinuousPredictableGirsanovCorrection]
  exact ⟨hAQ.adapted_stochasticIntegral hFQ haH hrH,
    hAQ.hasCadlagPaths_stochasticIntegral hFQ haH hrH⟩

/-- Integrating the constant-one process against a zero-initial finite-
variation semimartingale recovers the integrator. -/
private theorem stochasticIntegral_one_indistinguishable
    {A : ℝ≥0 → Ω → ℝ} (hA : IsSemimartingale A F P)
    (hF : F.IsUsual P) (hvA : HasFiniteVariationPaths A P) :
    Indistinguishable
      (hA.stochasticIntegral hF (fun _ ↦ measurable_const)
        (ae_of_all P fun _ ↦ ⟨fun _ ↦ continuousWithinAt_const,
          fun _ ↦ ⟨1, tendsto_const_nhds⟩⟩))
      A P := by
  let haOne : Adapted F (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ (1 : ℝ)) :=
    fun _ ↦ measurable_const
  let hrOne : HasCagladPaths (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ (1 : ℝ)) P :=
    ae_of_all P fun _ ↦ ⟨fun _ ↦ continuousWithinAt_const,
      fun _ ↦ ⟨1, tendsto_const_nhds⟩⟩
  filter_upwards
      [hA.stochasticIntegral_eq_pathStieltjesIntegral_ae hF hvA haOne hrOne]
    with ω hω
  obtain ⟨hvω, hrω, hiω⟩ := hω
  intro t
  rw [hiω t, StochLean.pathStieltjesIntegral_const
    (x := (A · ω)) (hx := hvω) (hr := hrω.1) 1 t]
  simp only [one_mul]

/-- Source-law product algebra on a single lower-density window. -/
private theorem stopped_mul_sub_clippedCorrection_isLocalMartingale
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation
      (densityRawCovariation (Q := Q) hM hFP) F P) (n : ℕ) :
    let Z := densityProcess Q P F
    let A := densityPredictableCovariation (Q := Q) hM hFP hV
    let _Hn := absoluteContinuousClippedInverseDensityLeft Q P F n
    let hAP : IsSemimartingale A F P :=
      (densityPredictableCovariation_properties (Q := Q) hM hFP hV).2.2.2.1
        |>.hasFiniteVariationPaths.isSemimartingale
          (densityPredictableCovariation_properties
            (Q := Q) hM hFP hV).1.stronglyAdapted.adapted hFP
          (Eventually.of_forall
            (densityPredictableCovariation_properties (Q := Q) hM hFP hV).2.1)
    let Jn := hAP.stochasticIntegral hFP
      (adapted_absoluteContinuousClippedInverseDensityLeft (Q := Q) hFP n)
      (hasCagladPaths_absoluteContinuousClippedInverseDensityLeft
        (Q := Q) (F := F) n)
    IsLocalMartingale
      (MeasureTheory.stoppedProcess (Z * (M - Jn))
        (absoluteContinuousDensityExit Q P F n)) F P := by
  dsimp only
  let Z := densityProcess Q P F
  let A := densityPredictableCovariation (Q := Q) hM hFP hV
  obtain ⟨hpA, hcAall, hA0, hvA, _⟩ :=
    densityPredictableCovariation_properties (Q := Q) hM hFP hV
  let hcAP : HasCadlagPaths A P := Eventually.of_forall hcAall
  let hAP : IsSemimartingale A F P :=
    hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hFP hcAP
  let hZ : IsLocalMartingale Z F P := isLocalMartingale_densityProcess hFP
  let hZP : IsSemimartingale Z F P := hZ.isSemimartingale hFP
  let Hn := absoluteContinuousClippedInverseDensityLeft Q P F n
  let haHn : Adapted F Hn :=
    adapted_absoluteContinuousClippedInverseDensityLeft (Q := Q) hFP n
  let hrHn : HasCagladPaths Hn P :=
    hasCagladPaths_absoluteContinuousClippedInverseDensityLeft (Q := Q) (F := F) n
  let Jn := hAP.stochasticIntegral hFP haHn hrHn
  let hJnP : IsSemimartingale Jn F P :=
    hAP.isSemimartingale_stochasticIntegral hFP haHn hrHn
  let Zl := leftLimitProcess Z
  let haZl : Adapted F Zl :=
    hZ.1.leftLimitProcess_of_usual hFP hZ.2.1
  let hrZl : HasCagladPaths Zl P := hZ.2.1.hasCagladPaths_leftLimitProcess
  let Jl := leftLimitProcess Jn
  let haJl : Adapted F Jl :=
    hJnP.adapted.leftLimitProcess_of_usual hFP hJnP.hasCadlagPaths
  let hrJl : HasCagladPaths Jl P :=
    hJnP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let B := hAP.stochasticIntegral hFP
    (fun t ↦ (haZl t).mul (haHn t)) (hrZl.mul hrHn)
  let I := hZP.stochasticIntegral hFP haJl hrJl
  let qZA := hZP.quadraticCovariation hAP hFP
  let hqZAP : IsSemimartingale qZA F P :=
    hZP.isSemimartingale_quadraticCovariation hAP hFP
  let qZJ := hZP.quadraticCovariation hJnP hFP
  have hI : IsLocalMartingale I F P :=
    hZ.isLocalMartingale_stochasticIntegral hFP haJl hrJl
  have hqZA : IsLocalMartingale qZA F P := by
    simpa only [qZA, hZP, hAP] using
      hpA.isLocalMartingale_quadraticCovariation hFP hcAP
        hvA.hasFiniteVariationPaths hZ
  let qInt := hqZAP.stochasticIntegral hFP haHn hrHn
  have hqInt : IsLocalMartingale qInt F P :=
    hqZA.isLocalMartingale_stochasticIntegral hFP haHn hrHn
  have heqQ : Indistinguishable qZJ qInt P := by
    simpa only [qZJ, qInt, hqZAP, hJnP, Jn] using
      hZP.quadraticCovariation_stochasticIntegral_right hAP hFP haHn hrHn
  have hqZJ : IsLocalMartingale qZJ F P :=
    hqInt.congr hFP (hZP.adapted_quadraticCovariation hJnP hFP) heqQ.symm
  let JZ := hJnP.stochasticIntegral hFP haZl hrZl
  have hassoc : Indistinguishable JZ B P := by
    simpa only [JZ, B, hJnP, Jn] using
      hAP.stochasticIntegral_stochasticIntegral hFP haZl hrZl haHn hrHn
  have hparts := hZP.integrationByParts hJnP hFP
  have heParts : Indistinguishable (Z * Jn) (B + I + qZJ) P := by
    filter_upwards [hparts, hassoc] with ω hp hassocω t
    change Z t ω * Jn t ω = (B t ω + I t ω) + qZJ t ω
    have hp' := hp t
    change Z t ω * Jn t ω = (JZ t ω + I t ω) + qZJ t ω at hp'
    rw [hp', hassocω t]
  let One : ℝ≥0 → Ω → ℝ := fun _ _ ↦ 1
  let haOne : Adapted F One := fun _ ↦ measurable_const
  let hrOne : HasCagladPaths One P :=
    ae_of_all P fun _ ↦ ⟨fun _ ↦ continuousWithinAt_const,
      fun _ ↦ ⟨1, tendsto_const_nhds⟩⟩
  let O := hAP.stochasticIntegral hFP haOne hrOne
  have heOne : Indistinguishable O A P := by
    simpa only [O, haOne, hrOne, One] using
      stochasticIntegral_one_indistinguishable hAP hFP hvA.hasFiniteVariationPaths
  let R := absoluteContinuousDensityExit Q P F n
  let hR : IsStoppingTime F R := isStoppingTime_absoluteContinuousDensityExit hFP n
  let Zero : Ω → WithTop ℝ≥0 := fun _ ↦ 0
  let hZero : IsStoppingTime F Zero := isStoppingTime_const F 0
  have hloc := hAP.stochasticIntegral_congr_integrand_on_interval hFP
    (fun t ↦ (haZl t).mul (haHn t)) (hrZl.mul hrHn)
    haOne hrOne hZero hR
  have hB0 := hAP.stochasticIntegral_zero_ae hFP
    (fun t ↦ (haZl t).mul (haHn t)) (hrZl.mul hrHn)
  have hO0 := hAP.stochasticIntegral_zero_ae hFP haOne hrOne
  have hBA : Indistinguishable
      (MeasureTheory.stoppedProcess B R)
      (MeasureTheory.stoppedProcess A R) P := by
    filter_upwards [hloc, hZ.2.1, heOne.stoppedProcess R, hB0, hO0]
      with ω hlocω hZω hOneω hB0ω hO0ω
    intro t
    have hagree : ∀ u : ℝ≥0, Zero ω < (u : WithTop ℝ≥0) →
        (u : WithTop ℝ≥0) ≤ R ω → Zl u ω * Hn u ω = One u ω := by
      intro u hu0 huR
      change 0 < (u : WithTop ℝ≥0) at hu0
      change leftLimitProcess (densityProcess Q P F) u ω *
          absoluteContinuousClippedInverseDensityLeft Q P F n u ω = 1
      exact leftLimit_densityProcess_mul_clippedInverse_eq_one_of_le_exit
        hZω (WithTop.coe_pos.mp hu0) huR
    have h := hlocω (show Zero ω ≤ R ω from bot_le) hagree t
    have hA0ω : A 0 ω = 0 := congrFun hA0 ω
    have hB0ω' : B 0 ω = 0 := by
      change hAP.stochasticIntegral hFP
        (fun t ↦ (haZl t).mul (haHn t)) (hrZl.mul hrHn) 0 ω = 0
      simpa only [Pi.mul_apply, hA0ω, mul_zero] using hB0ω
    have hO0ω' : O 0 ω = 0 := by
      change hAP.stochasticIntegral hFP haOne hrOne 0 ω = 0
      simpa only [One, one_mul, hA0ω] using hO0ω
    change MeasureTheory.stoppedProcess B R t ω -
        MeasureTheory.stoppedProcess B Zero t ω =
      MeasureTheory.stoppedProcess O R t ω -
        MeasureTheory.stoppedProcess O Zero t ω at h
    have hBzero : MeasureTheory.stoppedProcess B Zero t ω = 0 := by
      change B (min (t : WithTop ℝ≥0) 0).untopA ω = 0
      have hmin : min (t : WithTop ℝ≥0) (0 : WithTop ℝ≥0) = 0 :=
        min_eq_right bot_le
      rw [hmin]
      exact hB0ω'
    have hOzero : MeasureTheory.stoppedProcess O Zero t ω = 0 := by
      change O (min (t : WithTop ℝ≥0) 0).untopA ω = 0
      have hmin : min (t : WithTop ℝ≥0) (0 : WithTop ℝ≥0) = 0 :=
        min_eq_right bot_le
      rw [hmin]
      exact hO0ω'
    rw [hBzero, hOzero, sub_zero, sub_zero] at h
    exact h.trans (hOneω t)
  have hIQ : IsLocalMartingale (I + qZJ) F P := hI.add hqZJ hFP
  have hD : IsLocalMartingale
      (MeasureTheory.stoppedProcess (Z * Jn - A) R) F P := by
    have hIQstop := hIQ.stoppedProcess hFP hR
    have heD : Indistinguishable
        (MeasureTheory.stoppedProcess (I + qZJ) R)
        (MeasureTheory.stoppedProcess (Z * Jn - A) R) P := by
      filter_upwards [heParts, hBA] with ω hp hba t
      simp only [MeasureTheory.stoppedProcess_add,
        MeasureTheory.stoppedProcess_sub, Pi.add_apply, Pi.sub_apply]
      let u := (min (t : WithTop ℝ≥0) (R ω)).untopA
      have hp' := hp u
      change (I + qZJ) (min (t : WithTop ℝ≥0) (R ω)).untopA ω =
        (Z * Jn - A) (min (t : WithTop ℝ≥0) (R ω)).untopA ω
      change Z u ω * Jn u ω = (B u ω + I u ω) + qZJ u ω at hp'
      have hba' := hba t
      change B u ω = A u ω at hba'
      change I u ω + qZJ u ω = Z u ω * Jn u ω - A u ω
      rw [hp', hba']
      ring
    have haD : Adapted F (Z * Jn - A) :=
      (hZ.1.mul hJnP.adapted).sub hAP.adapted
    have hcD : HasCadlagPaths (Z * Jn - A) P :=
      (hZ.2.1.mul hJnP.hasCadlagPaths).sub hcAP
    exact hIQstop.congr hFP
      (haD.stronglyAdapted.stoppedProcess_of_usual hFP
        hcD.hasRightContinuousPaths hR).adapted heD
  have hK : IsLocalMartingale (Z * M - A) F P := by
    simpa only [Z, A, densityPredictableCovariation] using
      hZ.isLocalMartingale_mul_sub_predictableQuadraticCovariation hM hFP hV
  have hKstop := hK.stoppedProcess hFP hR
  have hsum := hKstop.sub hD hFP
  have heq : MeasureTheory.stoppedProcess (Z * (M - Jn)) R =
      MeasureTheory.stoppedProcess (Z * M - A) R -
    MeasureTheory.stoppedProcess (Z * Jn - A) R := by
    ext t ω
    simp only [MeasureTheory.stoppedProcess, Pi.mul_apply, Pi.sub_apply]
    ring
  rw [heq]
  exact hsum

/-- Protter III.41.  Under one-way absolute continuity, subtracting the
predictable density-covariation correction produces a target-law local
martingale.  No reverse density or equivalence assumption is used. -/
theorem isLocalMartingale_sub_absoluteContinuousPredictableGirsanovCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q)
    (hV : HasLocallyIntegrableVariation
      (densityRawCovariation (Q := Q) hM hFP) F P) :
    IsLocalMartingale
      (M - absoluteContinuousPredictableGirsanovCorrection
        (Q := Q) hM hQP hFP hFQ hV) F Q := by
  let Z := densityProcess Q P F
  let A := densityPredictableCovariation (Q := Q) hM hFP hV
  obtain ⟨hpA, hcAall, hA0, hvA, _⟩ :=
    densityPredictableCovariation_properties (Q := Q) hM hFP hV
  let hcAP : HasCadlagPaths A P := Eventually.of_forall hcAall
  let hAP : IsSemimartingale A F P :=
    hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hFP hcAP
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hFP
  let H := absoluteContinuousInverseDensityLeft Q P F
  let haH : Adapted F H := adapted_absoluteContinuousInverseDensityLeft hFP
  let hrH : HasCagladPaths H Q :=
    hasCagladPaths_absoluteContinuousInverseDensityLeft hQP hFP
  let C := hAQ.stochasticIntegral hFQ haH hrH
  have hCdef : absoluteContinuousPredictableGirsanovCorrection
      (Q := Q) hM hQP hFP hFQ hV = C := by
    rw [absoluteContinuousPredictableGirsanovCorrection]
  have haC : Adapted F C := hAQ.adapted_stochasticIntegral hFQ haH hrH
  have hcC : HasCadlagPaths C Q := hAQ.hasCadlagPaths_stochasticIntegral hFQ haH hrH
  let R : ℕ → Ω → WithTop ℝ≥0 := absoluteContinuousDensityExit Q P F
  have hR : IsLocalizingSequence F R Q :=
    isLocalizingSequence_absoluteContinuousDensityExit hQP hFP
  let κ : ℕ → Ω → WithTop ℝ≥0 := fun n _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)
  have hκ : IsLocalizingSequence F κ Q := by
    refine ⟨⟨fun n ↦ isStoppingTime_const F n, ?_⟩, ?_⟩
    · exact ae_of_all _ fun _ ↦
        WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
    · exact ae_of_all _ fun _ n m hnm ↦
        WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm)
  let ρ : ℕ → Ω → WithTop ℝ≥0 := min R κ
  have hρ : IsLocalizingSequence F ρ Q := hR.min hκ
  have hcMQ : HasCadlagPaths M Q := hQP.ae_le hM.2.1
  have hcFinal : HasCadlagPaths (M - C) Q := hcMQ.sub hcC
  have hlocal : Locally (fun Y ↦ IsLocalMartingale Y F Q) F (M - C) Q := by
    refine ⟨ρ, hρ, fun n ↦ ?_⟩
    let Hn := absoluteContinuousClippedInverseDensityLeft Q P F n
    let haHn : Adapted F Hn :=
      adapted_absoluteContinuousClippedInverseDensityLeft (Q := Q) hFP n
    let hrHnP : HasCagladPaths Hn P :=
      hasCagladPaths_absoluteContinuousClippedInverseDensityLeft (Q := Q) (F := F) n
    let hrHnQ : HasCagladPaths Hn Q := hQP.ae_le hrHnP
    let JnP := hAP.stochasticIntegral hFP haHn hrHnP
    let JnQ := hAQ.stochasticIntegral hFQ haHn hrHnQ
    let hJnP : IsSemimartingale JnP F P :=
      hAP.isSemimartingale_stochasticIntegral hFP haHn hrHnP
    have heJn : Indistinguishable JnQ JnP Q := by
      simpa only [JnP, JnQ, hAQ, hrHnQ] using
        hAP.stochasticIntegral_absolutelyContinuous hQP hFP hFQ haHn hrHnP
    let Rn : Ω → WithTop ℝ≥0 := R n
    let hRn : IsStoppingTime F Rn := hR.isStoppingTime n
    let Zero : Ω → WithTop ℝ≥0 := fun _ ↦ 0
    let hZero : IsStoppingTime F Zero := isStoppingTime_const F 0
    have hloc := hAQ.stochasticIntegral_congr_integrand_on_interval hFQ
      haH hrH haHn hrHnQ hZero hRn
    have hC0 := hAQ.stochasticIntegral_zero_ae hFQ haH hrH
    have hJnQ0 := hAQ.stochasticIntegral_zero_ae hFQ haHn hrHnQ
    have hCJnQ : Indistinguishable
        (MeasureTheory.stoppedProcess C Rn)
        (MeasureTheory.stoppedProcess JnQ Rn) Q := by
      filter_upwards [hloc, hQP.ae_le
          (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)),
          hC0, hJnQ0]
        with ω hlocω hZω hC0ω hJnQ0ω
      intro t
      have hagree : ∀ u : ℝ≥0, Zero ω < (u : WithTop ℝ≥0) →
          (u : WithTop ℝ≥0) ≤ Rn ω → H u ω = Hn u ω := by
        intro u hu0 huR
        change 0 < (u : WithTop ℝ≥0) at hu0
        exact absoluteContinuousClippedInverseDensityLeft_eq_of_le_exit
          hZω (WithTop.coe_pos.mp hu0) huR |>.symm
      have h := hlocω (show Zero ω ≤ Rn ω from bot_le) hagree t
      have hA0ω : A 0 ω = 0 := congrFun hA0 ω
      have hC0ω' : C 0 ω = 0 := by
        change hAQ.stochasticIntegral hFQ haH hrH 0 ω = 0
        simpa only [hA0ω, mul_zero] using hC0ω
      have hJnQ0ω' : JnQ 0 ω = 0 := by
        change hAQ.stochasticIntegral hFQ haHn hrHnQ 0 ω = 0
        simpa only [hA0ω, mul_zero] using hJnQ0ω
      change MeasureTheory.stoppedProcess C Rn t ω -
          MeasureTheory.stoppedProcess C Zero t ω =
        MeasureTheory.stoppedProcess JnQ Rn t ω -
          MeasureTheory.stoppedProcess JnQ Zero t ω at h
      have hCzero : MeasureTheory.stoppedProcess C Zero t ω = 0 := by
        change C (min (t : WithTop ℝ≥0) 0).untopA ω = 0
        have hmin : min (t : WithTop ℝ≥0) (0 : WithTop ℝ≥0) = 0 :=
          min_eq_right bot_le
        rw [hmin]
        exact hC0ω'
      have hJnQzero : MeasureTheory.stoppedProcess JnQ Zero t ω = 0 := by
        change JnQ (min (t : WithTop ℝ≥0) 0).untopA ω = 0
        have hmin : min (t : WithTop ℝ≥0) (0 : WithTop ℝ≥0) = 0 :=
          min_eq_right bot_le
        rw [hmin]
        exact hJnQ0ω'
      rwa [hCzero, hJnQzero, sub_zero, sub_zero] at h
    have hCJnP : Indistinguishable
        (MeasureTheory.stoppedProcess C Rn)
        (MeasureTheory.stoppedProcess JnP Rn) Q :=
      hCJnQ.trans (heJn.stoppedProcess Rn)
    have hCJρ : Indistinguishable
        (MeasureTheory.stoppedProcess C (ρ n))
        (MeasureTheory.stoppedProcess JnP (ρ n)) Q := by
      have hs := hCJnP.stoppedProcess (κ n)
      simpa only [MeasureTheory.stoppedProcess_stoppedProcess, ρ, Rn,
        Pi.inf_apply, inf_comm] using hs
    have hsourceR := stopped_mul_sub_clippedCorrection_isLocalMartingale
      (Q := Q) hM hFP hV n
    have hsourceρ : IsLocalMartingale
        (MeasureTheory.stoppedProcess (Z * (M - JnP)) (ρ n)) F P := by
      have hs := hsourceR.stoppedProcess hFP (hκ.isStoppingTime n)
      simpa only [MeasureTheory.stoppedProcess_stoppedProcess, ρ, R, Rn,
        Pi.inf_apply, inf_comm, Z, JnP, Hn, haHn, hrHnP, hAP] using hs
    have haXn : Adapted F (M - JnP) := hM.1.sub hJnP.adapted
    have hcXnP : HasCadlagPaths (M - JnP) P := hM.2.1.sub hJnP.hasCadlagPaths
    have hρbound : ∀ ω, ρ n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := fun ω ↦
      min_le_right (R n ω) (κ n ω)
    have htargetJn :=
      hsourceρ.stoppedProcess_of_mul_densityProcess_absolutelyContinuous
        haXn hcXnP hQP hFP hFQ (hρ.isStoppingTime n) hρbound
    have heTarget : Indistinguishable
        (MeasureTheory.stoppedProcess (M - JnP) (ρ n))
        (MeasureTheory.stoppedProcess (M - C) (ρ n)) Q := by
      filter_upwards [hCJρ] with ω hω t
      simp only [MeasureTheory.stoppedProcess_sub, Pi.sub_apply]
      rw [← hω t]
    have haFinal : Adapted F (M - C) := hM.1.sub haC
    have hactual := htargetJn.congr hFQ
      (haFinal.stronglyAdapted.stoppedProcess_of_usual hFQ
        hcFinal.hasRightContinuousPaths (hρ.isStoppingTime n)).adapted heTarget
    have hE : MeasurableSet[F 0] {ω | 0 < ρ n ω} :=
      (hρ.isStoppingTime n).measurableSet_gt 0
    simpa only [stoppedProcess_indicator_comm', bot_eq_zero] using
      hactual.indicator_initial hE
  have hMC := isLocalMartingale_of_locally_localMartingale hFQ hcFinal hlocal
  rw [hCdef]
  exact hMC

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousRawGirsanovCorrection
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Jump
public import StochLean.Probability.Process.FiniteVariation.RightValueCompensator
public import StochLean.Analysis.PathVariation.StieltjesIntegralAssociativity
public import StochLean.Analysis.PathVariation.StieltjesIntegralStopping
public import StochLean.Probability.Process.Path.CagladBounded

/-! # Density-extinction residual for one-way Girsanov

The raw covariation is stopped when the density first vanishes.  Integrating
its reciprocal removes the pre-extinction part; the single killing-jump step
supplies the missing endpoint exactly when extinction occurs by a jump from a
positive left limit.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set Function
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

private theorem pathStieltjesIntegral_zero_integrator (H : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hv : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ (0 : ℝ)) univ)
    (hr : IsRightContinuousPath (fun _ : ℝ≥0 ↦ (0 : ℝ))) :
    pathStieltjesIntegral (fun _ : ℝ≥0 ↦ (0 : ℝ)) hv hr H t = 0 := by
  have htv (s : ℝ≥0) : pathTotalVariation (fun _ : ℝ≥0 ↦ (0 : ℝ)) s = 0 := by
    exact (variationOnFromTo.eq_zero_iff hv (mem_univ 0) (mem_univ s)).2
      (by simp)
  have hp : positiveVariationStieltjes (fun _ : ℝ≥0 ↦ (0 : ℝ)) hv hr = 0 := by
    apply StieltjesFunction.ext
    intro s
    simp [positiveVariationStieltjes, pathPositiveVariation, htv]
  have hn : negativeVariationStieltjes (fun _ : ℝ≥0 ↦ (0 : ℝ)) hv hr = 0 := by
    apply StieltjesFunction.ext
    intro s
    simp [negativeVariationStieltjes, pathNegativeVariation, htv]
  simp [pathStieltjesIntegral, pathStieltjesIncrementIntegral, hp, hn]

/-- The raw density covariation is already stopped at the raw density-extinction
time.  This is the bracket counterpart of density absorption at zero. -/
theorem indistinguishable_densityRawCovariation_stopped_extinctionTime
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P) :
    let B := densityRawCovariation (Q := Q) hM hFP
    let R := absoluteContinuousDensityExtinctionTime Q P F
    Indistinguishable B (MeasureTheory.stoppedProcess B R) P := by
  intro B R
  let Z := densityProcess Q P F
  let hZ : IsLocalMartingale Z F P :=
    (show IsUIMartingale Z F P from
      ⟨martingale_densityProcess hFP, uniformIntegrable_densityProcess hFP⟩)
        |>.isLocalMartingale hasCadlagPaths_densityProcess
  let hSZ : IsSemimartingale Z F P := hZ.isSemimartingale hFP
  let hSM : IsSemimartingale M F P := hM.isSemimartingale hFP
  let hR : IsStoppingTime F R :=
    isStoppingTime_absoluteContinuousDensityExtinctionTime (Q := Q) hFP
  have heZ : Indistinguishable Z (MeasureTheory.stoppedProcess Z R) P :=
    indistinguishable_densityProcess_stopped_extinctionTime (Q := Q) hFP
  have heB : Indistinguishable B
      ((hSZ.stoppedProcess hFP hR).quadraticCovariation hSM hFP) P := by
    simpa only [B, Z, hSZ, hSM, densityRawCovariation] using
      hSZ.quadraticCovariation_congr hSM (hSZ.stoppedProcess hFP hR) hSM hFP
        heZ (ae_of_all P fun _ _ ↦ rfl)
  exact heB.trans (hSZ.quadraticCovariation_stoppedProcess_left hSM hFP hR)

/-- The source-law residual behind the one-way Lenglart--Girsanov formula
vanishes indistinguishably.  The right-value raw correction removes the bracket
strictly before density extinction, while the killing-jump integral restores
the terminal jump exactly when the density dies from a positive left limit. -/
theorem indistinguishable_absoluteContinuousRawGirsanovResidual_zero
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    let Z := densityProcess Q P F
    let B := densityRawCovariation (Q := Q) hM hFP
    let A := absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ
    let U := absoluteContinuousKillingJump Q P F M
    let hZP : IsSemimartingale Z F P :=
      (show IsUIMartingale Z F P from
        ⟨martingale_densityProcess hFP, uniformIntegrable_densityProcess hFP⟩)
        |>.isLocalMartingale hasCadlagPaths_densityProcess |>.isSemimartingale hFP
    let hAP : IsSemimartingale A F P :=
      (absoluteContinuousRawGirsanovCorrection_source_properties
        hM hQP hFP hFQ).2.2.2
    let hUP : IsSemimartingale U F P :=
      (hasLocallyIntegrableVariation_absoluteContinuousKillingJump
        (Q := Q) hM hFP).hasFiniteVariationPaths.isSemimartingale
          (adapted_absoluteContinuousKillingJump (Q := Q) hM hFP) hFP
          (hasCadlagPaths_absoluteContinuousKillingJump
            (Q := Q) (P := P) (F := F) (M := M))
    let Zl := leftLimitProcess Z
    let haZl : Adapted F Zl :=
      hZP.adapted.leftLimitProcess_of_usual hFP hZP.hasCadlagPaths
    let hrZl : HasCagladPaths Zl P :=
      hZP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let JA := hAP.stochasticIntegral hFP haZl hrZl
    let qZA := hZP.quadraticCovariation hAP hFP
    let JU := hUP.stochasticIntegral hFP haZl hrZl
    Indistinguishable (B - (JA + qZA) + JU) 0 P := by
  dsimp only
  let Z := densityProcess Q P F
  let B := densityRawCovariation (Q := Q) hM hFP
  let D := absoluteContinuousRawCovariationRealization (Q := Q) hM hFP
  let V := absoluteContinuousInverseDensityCadlagVersion hQP hFP hFQ
  let A := absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ
  let U := absoluteContinuousKillingJump Q P F M
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let K := absoluteContinuousDensityKillingTime Q P F
  let hZ : IsLocalMartingale Z F P :=
    (show IsUIMartingale Z F P from
      ⟨martingale_densityProcess hFP, uniformIntegrable_densityProcess hFP⟩)
        |>.isLocalMartingale hasCadlagPaths_densityProcess
  let hZP : IsSemimartingale Z F P := hZ.isSemimartingale hFP
  obtain ⟨haA, hcA, hvA, hAP⟩ :=
    absoluteContinuousRawGirsanovCorrection_source_properties hM hQP hFP hFQ
  let hUliv := hasLocallyIntegrableVariation_absoluteContinuousKillingJump
    (Q := Q) hM hFP
  let haU := adapted_absoluteContinuousKillingJump (Q := Q) hM hFP
  let hcU := hasCadlagPaths_absoluteContinuousKillingJump
    (Q := Q) (P := P) (F := F) (M := M)
  let hUP : IsSemimartingale U F P :=
    hUliv.hasFiniteVariationPaths.isSemimartingale haU hFP hcU
  let Zl := leftLimitProcess Z
  let haZl : Adapted F Zl :=
    hZP.adapted.leftLimitProcess_of_usual hFP hZP.hasCadlagPaths
  let hrZl : HasCagladPaths Zl P :=
    hZP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let JA := hAP.stochasticIntegral hFP haZl hrZl
  let qZA := hZP.quadraticCovariation hAP hFP
  let JU := hUP.stochasticIntegral hFP haZl hrZl
  have hright :=
    hZP.stochasticIntegral_leftLimit_add_quadraticCovariation_eq_pathStieltjesIntegral_ae
      hAP hFP hvA
  have huint := hUP.stochasticIntegral_eq_pathStieltjesIntegral_ae
    hFP hUliv.hasFiniteVariationPaths haZl hrZl
  obtain ⟨_, _, hcV⟩ :=
    absoluteContinuousInverseDensityCadlagVersion_properties hQP hFP hFQ
  filter_upwards [hright, huint, D.mixed_eq,
      indistinguishable_densityRawCovariation_stopped_extinctionTime (Q := Q) hM hFP,
      hZP.jumpProcess_quadraticCovariation (hM.isSemimartingale hFP) hFP,
      density_mul_inverseVersion_indistinguishable hQP hFP hFQ,
      ae_densityProcess_ne_zero_iff_lt_extinctionTime (Q := Q) hFP,
      hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F),
      ae_forall_densityProcess_nonneg (Q := Q) hFP,
      ae_densityProcess_at_absoluteContinuousDensityExtinctionTime_eq_zero
        (Q := Q) hFP, hrZl]
    with ω hrightω huintω hDB hBstop hBjump hDV hsel hZcad hZnonneg hZzero hZlcag
  change ∀ s, B s ω = D.mixed s ω at hDB
  change ∀ s, B s ω = MeasureTheory.stoppedProcess B R s ω at hBstop
  change ∀ s, jumpProcess B s ω = jumpProcess Z s ω * jumpProcess M s ω at hBjump
  obtain ⟨hAv, hAr, hrightω⟩ := hrightω
  obtain ⟨hUv, hUr, huintω⟩ := huintω
  intro t
  change B t ω - (JA t ω + qZA t ω) + JU t ω = 0
  rw [hrightω t]
  change B t ω -
      pathStieltjesIntegral (A · ω) hAv hAr.1 (Z · ω) t +
        hUP.stochasticIntegral hFP haZl hrZl t ω = 0
  rw [huintω t]
  have hassoc : pathStieltjesIntegral (A · ω) hAv hAr.1 (Z · ω) t =
      pathStieltjesIntegral (D.mixed · ω) (D.mixed_bv ω) (D.mixed_rc ω)
        (fun u ↦ Z u ω * V u ω) t := by
    have hf (S : ℝ≥0) : IntegrableOn (V · ω) (Ioc 0 S)
        (totalVariationStieltjes (D.mixed · ω) (D.mixed_bv ω)
          (D.mixed_rc ω)).measure :=
      (integrableOn_variationStieltjes_cadlag_and_leftLim
        (D.mixed_bv ω) (D.mixed_rc ω) (hcV ω) S).1
    have hg : IntegrableOn (Z · ω) (Ioc 0 t)
        (totalVariationStieltjes (A · ω) hAv hAr.1).measure :=
      (integrableOn_variationStieltjes_cadlag_and_leftLim
        hAv hAr.1 hZcad t).1
    have hgf : IntegrableOn (fun u ↦ Z u ω * V u ω) (Ioc 0 t)
        (totalVariationStieltjes (D.mixed · ω) (D.mixed_bv ω)
          (D.mixed_rc ω)).measure :=
      (integrableOn_variationStieltjes_cadlag_and_leftLim
        (D.mixed_bv ω) (D.mixed_rc ω) (hZcad.mul (hcV ω)) t).1
    simpa only [A, absoluteContinuousRawGirsanovCorrection, D, V,
      finiteVariationIntegral] using
      pathStieltjesIntegral_associative
        (D.mixed · ω) (D.mixed_bv ω) (D.mixed_rc ω)
        (V · ω) (Z · ω) t (measurable_cadlag_and_leftLim (hcV ω)).1
        hf hAv hAr.1 hg hgf
  rw [hassoc]
  by_cases hRtop : R ω = ⊤
  · have hprod : (fun u ↦ Z u ω * V u ω) = (fun _ ↦ (1 : ℝ)) := by
      funext u
      have huR : (u : WithTop ℝ≥0) < R ω := by rw [hRtop]; exact WithTop.coe_lt_top u
      have hne : Z u ω ≠ 0 := (hsel u).2 huR
      have hdv := hDV u
      change Z u ω * V u ω = if Z u ω = 0 then 0 else 1 at hdv
      rw [hdv, if_neg hne]
    rw [hprod]
    have hconst : pathStieltjesIntegral (fun s ↦ D.mixed s ω) (D.mixed_bv ω)
        (D.mixed_rc ω) (fun _ ↦ (1 : ℝ)) t = D.mixed t ω := by
      simpa only [one_mul] using
        (pathStieltjesIntegral_const (x := fun s ↦ D.mixed s ω)
          (hx := D.mixed_bv ω) (hr := D.mixed_rc ω) (c := (1 : ℝ)) (t := t))
    rw [hconst]
    have hUzero : (U · ω) = (fun _ ↦ (0 : ℝ)) := by
      funext u
      simp only [U, absoluteContinuousKillingJump, stoppedJumpStep,
        indicator_apply, mem_ofPred_eq]
      rw [if_neg]
      intro hKu
      have hKfinite : K ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hKu
      have hKR := absoluteContinuousDensityKillingTime_eq_extinctionTime_of_ne_top
        (Q := Q) (P := P) (F := F) hKfinite
      exact hKfinite (hKR.trans hRtop)
    have hv0 : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ (0 : ℝ)) univ :=
      (monotone_const.monotoneOn univ).locallyBoundedVariationOn
    have hr0 : IsRightContinuousPath (fun _ : ℝ≥0 ↦ (0 : ℝ)) :=
      fun _ ↦ continuousWithinAt_const
    have huint0 : pathStieltjesIntegral (U · ω) hUv hUr.1 (Zl · ω) t = 0 := by
      have hc := pathStieltjesIntegral_congr (x := fun s ↦ U s ω) (hx := hUv)
        (hr := hUr.1) (f := fun s ↦ Zl s ω) (y := fun _ ↦ (0 : ℝ))
        (hy := hv0) (hyr := hr0) (g := fun s ↦ Zl s ω) hUzero rfl
      rw [congrFun hc t]
      exact pathStieltjesIntegral_zero_integrator (Zl · ω) t hv0 hr0
    rw [huint0, add_zero, ← hDB t, sub_self]
  · let r : ℝ≥0 := (R ω).untopA
    have hRcoe : (r : WithTop ℝ≥0) = R ω := by
      dsimp only [r]
      rw [WithTop.untopA_eq_untop hRtop, WithTop.coe_untop]
    have hZr : Z r ω = 0 := hZzero hRtop
    by_cases hrzero : r = 0
    · have hprod : (fun u ↦ Z u ω * V u ω) = (fun _ ↦ (0 : ℝ)) := by
        funext u
        have hnotlt : ¬(u : WithTop ℝ≥0) < R ω := by
          rw [← hRcoe, hrzero]
          exact not_lt_of_ge bot_le
        have hz : Z u ω = 0 := not_ne_iff.mp (fun hne ↦ hnotlt ((hsel u).1 hne))
        have hdv := hDV u
        change Z u ω * V u ω = if Z u ω = 0 then 0 else 1 at hdv
        simpa only [hz, if_true] using hdv
      rw [hprod]
      have hconst0 : pathStieltjesIntegral (fun s ↦ D.mixed s ω) (D.mixed_bv ω)
          (D.mixed_rc ω) (fun _ ↦ (0 : ℝ)) t = 0 := by
        simpa only [zero_mul] using
          (pathStieltjesIntegral_const (x := fun s ↦ D.mixed s ω)
            (hx := D.mixed_bv ω) (hr := D.mixed_rc ω) (c := (0 : ℝ)) (t := t))
      rw [hconst0, sub_zero]
      have hBzero : B 0 ω = 0 := by
        have hj := hBjump 0
        simp only [jumpProcess_zero] at hj
        rw [show Z 0 ω = 0 by simpa only [hrzero] using hZr, zero_mul] at hj
        exact hj
      have hBt : B t ω = 0 := by
        rw [hBstop t]
        rw [MeasureTheory.stoppedProcess_eq_of_ge]
        · change B r ω = 0
          simpa only [hrzero] using hBzero
        · rw [← hRcoe, hrzero]
          exact bot_le
      rw [hBt, zero_add]
      have hKtop : K ω = ⊤ := by
        by_contra hfinite
        have hKR := absoluteContinuousDensityKillingTime_eq_extinctionTime_of_ne_top
          (Q := Q) (P := P) (F := F) hfinite
        change K ω = R ω at hKR
        have hKzero : K ω = 0 := by
          calc
            K ω = R ω := hKR
            _ = 0 := by rw [← hRcoe, hrzero]; rfl
        exact (ne_of_gt (absoluteContinuousDensityKillingTime_pos
          (Q := Q) (P := P) (F := F) ω)) hKzero
      have hUzero : (U · ω) = (fun _ ↦ (0 : ℝ)) := by
        funext u
        have hKtop' : absoluteContinuousDensityKillingTime Q P F ω = ⊤ := hKtop
        simp only [U, absoluteContinuousKillingJump, stoppedJumpStep,
          indicator_apply, mem_ofPred_eq]
        rw [if_neg]
        intro hle
        rw [hKtop'] at hle
        exact (not_le_of_gt (WithTop.coe_lt_top u)) hle
      have hv0 : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ (0 : ℝ)) univ :=
        (monotone_const.monotoneOn univ).locallyBoundedVariationOn
      have hr0 : IsRightContinuousPath (fun _ : ℝ≥0 ↦ (0 : ℝ)) :=
        fun _ ↦ continuousWithinAt_const
      have hc := pathStieltjesIntegral_congr (x := fun s ↦ U s ω) (hx := hUv)
        (hr := hUr.1) (f := fun s ↦ Zl s ω) (y := fun _ ↦ (0 : ℝ))
        (hy := hv0) (hyr := hr0) (g := fun s ↦ Zl s ω) hUzero rfl
      rw [congrFun hc t]
      exact pathStieltjesIntegral_zero_integrator (Zl · ω) t hv0 hr0
    · have hrpos : 0 < r := pos_iff_ne_zero.mpr hrzero
      have hprod : (fun u ↦ Z u ω * V u ω) =
          (Iio r).indicator (fun _ ↦ (1 : ℝ)) := by
        funext u
        have hdv := hDV u
        change Z u ω * V u ω = if Z u ω = 0 then 0 else 1 at hdv
        by_cases hur : u < r
        · have hne : Z u ω ≠ 0 := (hsel u).2 (by
            change (u : WithTop ℝ≥0) < R ω
            rw [← hRcoe]
            exact WithTop.coe_lt_coe.mpr hur)
          rw [hdv, if_neg hne]
          simp [indicator_apply, hur]
        · have hz : Z u ω = 0 := not_ne_iff.mp fun hne ↦ hur <|
            WithTop.coe_lt_coe.mp <| hRcoe ▸ (hsel u).1 hne
          rw [hdv, if_pos hz]
          simp [indicator_apply, hur]
      rw [hprod]
      have hcut : pathStieltjesIntegral (fun s ↦ D.mixed s ω) (D.mixed_bv ω)
          (D.mixed_rc ω) ((Iio r).indicator fun _ ↦ (1 : ℝ)) t =
          if t < r then D.mixed t ω else Function.leftLim (D.mixed · ω) r := by
        exact pathStieltjesIntegral_indicator_Iio_one
          (x := fun s ↦ D.mixed s ω) (hx := D.mixed_bv ω)
            (hr := D.mixed_rc ω) (T := r) hrpos t
      rw [hcut]
      have hBD : (B · ω) = (D.mixed · ω) := funext hDB
      have hleftBD : Function.leftLim (B · ω) r =
          Function.leftLim (D.mixed · ω) r :=
        congrArg (fun f : ℝ≥0 → ℝ ↦ Function.leftLim f r) hBD
      have hZjump : jumpProcess Z r ω = -Zl r ω := by
        simp [jumpProcess, Zl, leftLimitProcess, hrzero, hZr]
      have hDjump : D.mixed r ω - Function.leftLim (D.mixed · ω) r =
          (-Zl r ω) * jumpProcess M r ω := by
        rw [← hDB r, ← hleftBD]
        have hj := hBjump r
        simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg hrzero] at hj
        rw [hZr] at hj
        simpa only [Zl, jumpProcess, Pi.sub_apply, leftLimitProcess,
          if_neg hrzero, zero_sub] using hj
      letI : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hrpos⟩
      have hleftnonneg : 0 ≤ Zl r ω := by
        apply ge_of_tendsto (hZcad.tendsto_leftLimitProcess hrzero)
        exact Eventually.of_forall hZnonneg
      have hExtLeft : absoluteContinuousDensityExtinctionLeft Q P F ω = Zl r ω := by
        simp only [absoluteContinuousDensityExtinctionLeft, stoppedValueWithTerminal_of_ne_top
          hRtop, stoppedValue, Zl, Z, R, r]
      by_cases hleftpos : 0 < Zl r ω
      · have hmem : ω ∈ {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} := by
          change 0 < absoluteContinuousDensityExtinctionLeft Q P F ω
          rw [hExtLeft]
          exact hleftpos
        have hKR : K ω = R ω := by
          change absoluteContinuousDensityKillingTime Q P F ω =
            absoluteContinuousDensityExtinctionTime Q P F ω
          rw [absoluteContinuousDensityKillingTime,
            restrictedStoppingTime_of_mem _ hmem]
        have hKcoe : K ω = (r : WithTop ℝ≥0) := hKR.trans hRcoe.symm
        obtain ⟨C, _, hC⟩ := hZlcag.exists_norm_bound_Icc t
        have hUformula : pathStieltjesIntegral (U · ω) hUv hUr.1 (Zl · ω) t =
            if r ≤ t then Zl r ω * jumpProcess M r ω else 0 := by
          simpa only [U, absoluteContinuousKillingJump] using
            (pathStieltjesIntegral_stoppedJumpStep_of_eq_coe M K ω hrpos hKcoe
              hUv hUr.1 (Zl · ω) hZlcag.measurable t
              (fun s hs ↦ hC s ⟨hs.1.le, hs.2⟩))
        by_cases htr : t < r
        · rw [if_pos htr, hUformula, if_neg (not_le_of_gt htr), add_zero]
          rw [hDB t, sub_self]
        · have hrt : r ≤ t := le_of_not_gt htr
          rw [if_neg htr, hUformula, if_pos hrt]
          have hBt : B t ω = B r ω := by
            have hRt : R ω ≤ (t : WithTop ℝ≥0) := by
              rw [← hRcoe]
              exact WithTop.coe_le_coe.mpr hrt
            rw [hBstop t, MeasureTheory.stoppedProcess_eq_of_ge hRt]
          rw [hBt, hDB r, hDjump]
          ring
      · have hleftzero : Zl r ω = 0 :=
          le_antisymm (le_of_not_gt hleftpos) hleftnonneg
        have hnotmem : ω ∉
            {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} := by
          intro hmem
          change 0 < absoluteContinuousDensityExtinctionLeft Q P F ω at hmem
          rw [hExtLeft, hleftzero] at hmem
          exact (lt_irrefl 0 hmem)
        have hKtop : K ω = ⊤ := by
          change absoluteContinuousDensityKillingTime Q P F ω = ⊤
          rw [absoluteContinuousDensityKillingTime,
            restrictedStoppingTime_of_notMem _ hnotmem]
        have hUzero : (U · ω) = (fun _ ↦ (0 : ℝ)) := by
          funext u
          have hKtop' : absoluteContinuousDensityKillingTime Q P F ω = ⊤ := hKtop
          simp only [U, absoluteContinuousKillingJump, stoppedJumpStep,
            indicator_apply, mem_ofPred_eq]
          rw [if_neg]
          intro hle
          rw [hKtop'] at hle
          exact (not_le_of_gt (WithTop.coe_lt_top u)) hle
        have hv0 : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ (0 : ℝ)) univ :=
          (monotone_const.monotoneOn univ).locallyBoundedVariationOn
        have hr0 : IsRightContinuousPath (fun _ : ℝ≥0 ↦ (0 : ℝ)) :=
          fun _ ↦ continuousWithinAt_const
        have hUintegral : pathStieltjesIntegral (U · ω) hUv hUr.1 (Zl · ω) t = 0 := by
          have hc := pathStieltjesIntegral_congr (x := fun s ↦ U s ω) (hx := hUv)
            (hr := hUr.1) (f := fun s ↦ Zl s ω) (y := fun _ ↦ (0 : ℝ))
            (hy := hv0) (hyr := hr0) (g := fun s ↦ Zl s ω) hUzero rfl
          rw [congrFun hc t]
          exact pathStieltjesIntegral_zero_integrator (Zl · ω) t hv0 hr0
        rw [hUintegral, add_zero]
        by_cases htr : t < r
        · rw [if_pos htr, hDB t, sub_self]
        · have hrt : r ≤ t := le_of_not_gt htr
          rw [if_neg htr]
          have hBt : B t ω = B r ω := by
            have hRt : R ω ≤ (t : WithTop ℝ≥0) := by
              rw [← hRcoe]
              exact WithTop.coe_le_coe.mpr hrt
            rw [hBstop t, MeasureTheory.stoppedProcess_eq_of_ge hRt]
          rw [hBt, hDB r]
          have hd := hDjump
          rw [hleftzero, neg_zero, zero_mul] at hd
          exact hd

end ProbabilityTheory

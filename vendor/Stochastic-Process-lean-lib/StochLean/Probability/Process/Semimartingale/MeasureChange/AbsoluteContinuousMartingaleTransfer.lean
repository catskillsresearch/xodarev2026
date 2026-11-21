/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousDensityLocalization
public import StochLean.Probability.Conditional.StoppingCommutation
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUniformIntegrable
public import StochLean.Probability.Process.LocalMartingale.Localization
public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import StochLean.Probability.Process.LocalMartingale.Reducing
public import StochLean.Probability.Process.Measurability.InitialMask
public import StochLean.Probability.Process.Stopping.InitialMask

/-! # Martingale transfer through a one-way density

This file supplies the stopping-time Bayes and integrability interfaces needed
to transfer a density-weighted local martingale from `P` to `Q` when only
`Q ≪ P` is available.  In particular, it never constructs a reverse density.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {Y : Ω → ℝ}

/-- For a variable measurable at a finite stopping time, integrability under
the target law is equivalent to integrability after multiplication by the
sampled density under the source law. -/
theorem integrable_densityProcess_sample_mul_iff
    (hQP : Q ≪ P) (hF : F.IsUsual P) (τ : FiniteStoppingTime F)
    (hY : StronglyMeasurable[τ.measurableSpace] Y) :
    Integrable (fun ω ↦ densityProcess Q P F (τ ω) ω * Y ω) P ↔
      Integrable Y Q := by
  let hm : τ.measurableSpace ≤ mΩ := τ.measurableSpace_le
  have hsampleMeas : StronglyMeasurable[τ.measurableSpace]
      (fun ω ↦ densityProcess Q P F (τ ω) ω) :=
    ((martingale_densityProcess (Q := Q) hF).stronglyAdapted
      |>.measurable_stoppedValue_of_usual hF
        (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)).hasRightContinuousPaths
        τ.isStoppingTime).stronglyMeasurable
  have hsampleTrim :
      (fun ω ↦ densityProcess Q P F (τ ω) ω) =ᵐ[P.trim hm]
        P[terminalDensity Q P | τ.measurableSpace] :=
    hsampleMeas.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
      (densityProcess_sample_ae_eq_condExp_terminalDensity (Q := Q) hF τ)
  have hderiv :
      (fun ω ↦ ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal) =ᵐ[P.trim hm]
        fun ω ↦ densityProcess Q P F (τ ω) ω :=
    (toReal_rnDeriv_trim hm hQP).trans hsampleTrim.symm
  have htrimQP : Q.trim hm ≪ P.trim hm := hQP.trim hm
  constructor
  · intro hprod
    have hprodTrim := hprod.trim hm (hsampleMeas.mul hY)
    have hderivProd : Integrable
        (fun ω ↦ ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal * Y ω)
        (P.trim hm) := by
      apply hprodTrim.congr
      filter_upwards [hderiv] with ω hω
      rw [hω]
    have hYtrim : Integrable Y (Q.trim hm) :=
      (integrable_toReal_rnDeriv_mul_iff htrimQP).mp hderivProd
    exact integrable_of_integrable_trim hm hYtrim
  · intro hYQ
    have hYtrim : Integrable Y (Q.trim hm) := hYQ.trim hm hY
    have hderivProd : Integrable
        (fun ω ↦ ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal * Y ω)
        (P.trim hm) :=
      (integrable_toReal_rnDeriv_mul_iff htrimQP).mpr hYtrim
    have hprodTrim : Integrable
        (fun ω ↦ densityProcess Q P F (τ ω) ω * Y ω) (P.trim hm) := by
      apply hderivProd.congr
      filter_upwards [hderiv] with ω hω
      rw [hω]
    exact integrable_of_integrable_trim hm hprodTrim

/-- Multiplication-form Bayes formula on the native sigma-field of an
everywhere-finite stopping time. -/
theorem densityProcess_sample_mul_condExp_ae_eq
    (hQP : Q ≪ P) (hF : F.IsUsual P) (τ : FiniteStoppingTime F)
    (hY : Integrable Y Q) :
    (fun ω ↦ densityProcess Q P F (τ ω) ω *
        Q[Y | τ.measurableSpace] ω) =ᵐ[P]
      P[fun ω ↦ terminalDensity Q P ω * Y ω | τ.measurableSpace] := by
  let V : Ω → ℝ := Q[Y | τ.measurableSpace]
  have hV : Integrable V Q := integrable_condExp
  have hDV : Integrable (fun ω ↦ terminalDensity Q P ω * V ω) P := by
    simpa only [terminalDensity] using
      (integrable_toReal_rnDeriv_mul_iff hQP).2 hV
  have hDY : Integrable (fun ω ↦ terminalDensity Q P ω * Y ω) P := by
    simpa only [terminalDensity] using
      (integrable_toReal_rnDeriv_mul_iff hQP).2 hY
  have hcondPair :
      P[fun ω ↦ terminalDensity Q P ω * V ω | τ.measurableSpace] =ᵐ[P]
        P[fun ω ↦ terminalDensity Q P ω * Y ω | τ.measurableSpace] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq τ.measurableSpace_le hDY
    · intro s hs _
      exact integrable_condExp.integrableOn
    · intro s hs _
      calc
        (∫ ω in s,
            P[fun x ↦ terminalDensity Q P x * V x | τ.measurableSpace] ω ∂P) =
            ∫ ω in s, terminalDensity Q P ω * V ω ∂P :=
          setIntegral_condExp τ.measurableSpace_le hDV hs
        _ = ∫ ω in s, V ω ∂Q := by
          simpa only [terminalDensity] using
            (setIntegral_toReal_rnDeriv_mul hQP
              (τ.measurableSpace_le s hs) (f := V))
        _ = ∫ ω in s, Y ω ∂Q :=
          setIntegral_condExp τ.measurableSpace_le hY hs
        _ = ∫ ω in s, terminalDensity Q P ω * Y ω ∂P := by
          simpa only [terminalDensity] using
            (setIntegral_toReal_rnDeriv_mul hQP
              (τ.measurableSpace_le s hs) (f := Y)).symm
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
  have hpull :
      P[fun ω ↦ terminalDensity Q P ω * V ω | τ.measurableSpace] =ᵐ[P]
        fun ω ↦ P[terminalDensity Q P | τ.measurableSpace] ω * V ω := by
    change P[terminalDensity Q P * V | τ.measurableSpace] =ᵐ[P]
      P[terminalDensity Q P | τ.measurableSpace] * V
    exact condExp_mul_of_stronglyMeasurable_right
      stronglyMeasurable_condExp hDV (integrable_terminalDensity Q P)
  filter_upwards
      [densityProcess_sample_ae_eq_condExp_terminalDensity (Q := Q) hF τ,
        hpull.symm.trans hcondPair]
    with ω hωDensity hωBayes
  rw [hωDensity]
  exact hωBayes

/-- Division-form Bayes formula at a finite stopping time.  Division is made
only on the target-full-measure positivity event. -/
theorem condExp_ae_eq_div_densityProcess_sample
    (hQP : Q ≪ P) (hF : F.IsUsual P) (τ : FiniteStoppingTime F)
    (hY : Integrable Y Q) :
    Q[Y | τ.measurableSpace] =ᵐ[Q] fun ω ↦
      P[fun x ↦ terminalDensity Q P x * Y x | τ.measurableSpace] ω /
        densityProcess Q P F (τ ω) ω := by
  filter_upwards
      [hQP.ae_le (densityProcess_sample_mul_condExp_ae_eq hQP hF τ hY),
        densityProcess_sample_pos_ae hQP hF τ]
    with ω hω hpos
  apply (eq_div_iff hpos.ne').2
  simpa only [mul_comm] using hω

/-- If a density-weighted process, stopped at an everywhere-finite bounded
time, is a uniformly integrable source-law martingale, then the unweighted
stopped process is a uniformly integrable target-law martingale.  This is the
one-way (`Q ≪ P`) finite-window transfer used below to localize away from
zeros of the density. -/
theorem IsUIMartingale.stoppedProcess_of_mul_densityProcess_finite
    {X : ℝ≥0 → Ω → ℝ} (τ : FiniteStoppingTime F) (hZX : IsUIMartingale
      (stoppedProcess (densityProcess Q P F * X) τ.withTop) F P)
    (hXadapt : Adapted F X) (hXcad : HasCadlagPaths X P)
    (hQP : Q ≪ P) (hFP : F.IsUsual P)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) :
    IsUIMartingale (stoppedProcess X τ.withTop) F Q := by
  let V : Ω → ℝ := fun ω ↦ X (τ ω) ω
  have hVmeas : StronglyMeasurable[τ.measurableSpace] V := by
    have hm := hXadapt.stronglyAdapted.measurable_stoppedValue_of_usual hFP
      hXcad.hasRightContinuousPaths τ.isStoppingTime
    change Measurable[τ.measurableSpace] (fun ω ↦ X (τ ω) ω) at hm
    exact hm.stronglyMeasurable
  have hZVint : Integrable
      (fun ω ↦ densityProcess Q P F (τ ω) ω * V ω) P := by
    have hi := hZX.1.integrable T
    apply hi.congr
    exact ae_of_all _ fun ω ↦ by
      rw [stoppedProcess_eq_of_ge
        (show τ.withTop ω ≤ (T : WithTop ℝ≥0) from WithTop.coe_le_coe.mpr (hτT ω))]
      rfl
  have hVint : Integrable V Q :=
    (integrable_densityProcess_sample_mul_iff hQP hFP τ hVmeas).1 hZVint
  have hcadZX : HasCadlagPaths (densityProcess Q P F * X) P :=
    hasCadlagPaths_densityProcess.mul hXcad
  have hclose : ∀ t : ℝ≥0,
      stoppedProcess X τ.withTop t =ᵐ[Q] Q[V | F t] := by
    intro t
    let ρ : FiniteStoppingTime F := FiniteStoppingTime.truncate τ.isStoppingTime t
    have hρτ : ρ.withTop ≤ τ.withTop := by
      intro ω
      rw [FiniteStoppingTime.withTop_truncate]
      exact min_le_right _ _
    have hbayesρ := densityProcess_sample_mul_condExp_ae_eq hQP hFP ρ hVint
    have hselfτ : Q[V | τ.measurableSpace] = V :=
      condExp_of_stronglyMeasurable τ.measurableSpace_le hVmeas hVint
    have hbayesτ := densityProcess_sample_mul_condExp_ae_eq hQP hFP τ hVint
    have hterminal :
        (fun ω ↦ densityProcess Q P F (τ ω) ω * V ω) =ᵐ[P]
          P[fun ω ↦ terminalDensity Q P ω * V ω | τ.measurableSpace] := by
      simpa only [hselfτ] using hbayesτ
    have htower :
        P[fun ω ↦ densityProcess Q P F (τ ω) ω * V ω |
            ρ.measurableSpace] =ᵐ[P]
          P[fun ω ↦ terminalDensity Q P ω * V ω | ρ.measurableSpace] := by
      exact (condExp_congr_ae hterminal).trans
        (condExp_condExp_of_le
          (ρ.isStoppingTime.measurableSpace_mono τ.isStoppingTime hρτ)
          τ.measurableSpace_le)
    have hoptional := hZX.1.stoppedValue_ae_eq_condExp_of_bounded_le_usual
      hFP (hcadZX.stoppedProcess τ.withTop).hasRightContinuousPaths
      ρ.isStoppingTime τ.isStoppingTime hρτ
      (fun ω ↦ WithTop.coe_le_coe.mpr (hτT ω))
    have hleft : stoppedValue
        (stoppedProcess (densityProcess Q P F * X) τ.withTop) ρ.withTop =
          fun ω ↦ densityProcess Q P F (ρ ω) ω * X (ρ ω) ω := by
      funext ω
      change stoppedProcess (densityProcess Q P F * X) τ.withTop (ρ ω) ω = _
      rw [stoppedProcess_eq_of_le (hρτ ω)]
      rfl
    have hright : stoppedValue
        (stoppedProcess (densityProcess Q P F * X) τ.withTop) τ.withTop =
          fun ω ↦ densityProcess Q P F (τ ω) ω * V ω := by
      funext ω
      change stoppedProcess (densityProcess Q P F * X) τ.withTop (τ ω) ω = _
      calc
        _ = (densityProcess Q P F * X) (τ ω) ω :=
          stoppedProcess_eq_of_le
            (show (τ ω : WithTop ℝ≥0) ≤ τ.withTop ω from le_rfl)
        _ = _ := rfl
    change stoppedValue (stoppedProcess (densityProcess Q P F * X) τ.withTop)
        ρ.withTop =ᵐ[P]
      P[stoppedValue (stoppedProcess (densityProcess Q P F * X) τ.withTop)
        τ.withTop | ρ.measurableSpace] at hoptional
    rw [hleft, hright] at hoptional
    have hcancel : Q[V | ρ.measurableSpace] =ᵐ[Q]
        fun ω ↦ X (ρ ω) ω := by
      filter_upwards [hQP.ae_le hbayesρ, hQP.ae_le htower.symm,
          hQP.ae_le hoptional,
          densityProcess_sample_pos_ae hQP hFP ρ]
        with ω hbayes htower' hopt hpos
      apply mul_left_cancel₀ hpos.ne'
      rw [hbayes, htower']
      exact hopt.symm
    have hcomm := condExp_stoppingTime_eq_min_of_stronglyMeasurable
      (P := Q) (isStoppingTime_const F t) τ.isStoppingTime hVint hVmeas
    have hcomm' : Q[V | F t] =ᵐ[Q] Q[V | ρ.measurableSpace] := by
      simpa only [IsStoppingTime.measurableSpace_const, ρ,
        FiniteStoppingTime.truncate, FiniteStoppingTime.measurableSpace_ofNotTop] using hcomm
    change stoppedProcess X (fun ω ↦ (τ ω : WithTop ℝ≥0)) t =ᵐ[Q] Q[V | F t]
    simpa only [ρ, FiniteStoppingTime.stoppedValue_truncate] using
      (hcomm'.trans hcancel).symm
  have hmart : Martingale (stoppedProcess X τ.withTop) F Q :=
    (martingale_condExp V F Q).congr
      (hXadapt.stronglyAdapted.stoppedProcess_of_usual hFP
        hXcad.hasRightContinuousPaths τ.isStoppingTime)
      (fun t ↦ (hclose t).symm)
  exact ⟨hmart, MeasureTheory.Martingale.uniformIntegrable_of_integrable_closing
    hVint hclose⟩

/-- One-way bounded stopping transfer in the native possibly-infinite stopping
time API.  Boundedness makes the time everywhere finite, after which the
finite-window theorem applies. -/
theorem IsUIMartingale.stoppedProcess_of_mul_densityProcess_absolutelyContinuous
    {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}
    (hZX : IsUIMartingale
      (stoppedProcess (densityProcess Q P F * X) σ) F P)
    (hXadapt : Adapted F X) (hXcad : HasCadlagPaths X P)
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hσ : IsStoppingTime F σ)
    {T : ℝ≥0} (hbound : ∀ ω, σ ω ≤ T) :
    IsUIMartingale (stoppedProcess X σ) F Q := by
  let τ : FiniteStoppingTime F := FiniteStoppingTime.truncate hσ T
  have hτσ : τ.withTop = σ := by
    funext ω
    rw [FiniteStoppingTime.withTop_truncate]
    exact min_eq_right (hbound ω)
  have hZXτ : IsUIMartingale
      (stoppedProcess (densityProcess Q P F * X) τ.withTop) F P := by
    simpa only [hτσ] using hZX
  have h := hZXτ.stoppedProcess_of_mul_densityProcess_finite τ hXadapt hXcad
    hQP hFP (FiniteStoppingTime.truncate_le hσ T)
  simpa only [hτσ] using h

/-- One-way density criterion for local martingales.  If `Z * X` is a local
martingale under `P`, then `X` is a local martingale under `Q ≪ P`.  The
proof intersects the source localizer with the geometric exits of `Z` and a
deterministic cap, so every transferred window is genuinely bounded. -/
theorem IsLocalMartingale.of_mul_densityProcess_absolutelyContinuous
    {X : ℝ≥0 → Ω → ℝ}
    (hZX : IsLocalMartingale (densityProcess Q P F * X) F P)
    (hXadapt : Adapted F X) (hXcad : HasCadlagPaths X P)
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    IsLocalMartingale X F Q := by
  obtain ⟨τ, hτ, hU⟩ := hZX.locally_cadlagUI
  have hτQ : IsLocalizingSequence F τ Q :=
    { isStoppingTime := hτ.isStoppingTime
      tendsto_top := hQP.ae_le hτ.tendsto_top
      mono := hQP.ae_le hτ.mono }
  let κ : ℕ → Ω → WithTop ℝ≥0 := fun n _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)
  have hκ : IsLocalizingSequence F κ Q := by
    refine ⟨⟨fun n ↦ isStoppingTime_const F n, ?_⟩, ?_⟩
    · exact ae_of_all _ fun _ ↦
        WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
    · exact ae_of_all _ fun _ n m hnm ↦
        WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm)
  let R : ℕ → Ω → WithTop ℝ≥0 := absoluteContinuousDensityExit Q P F
  have hR : IsLocalizingSequence F R Q :=
    isLocalizingSequence_absoluteContinuousDensityExit hQP hFP
  let η : ℕ → Ω → WithTop ℝ≥0 := min R κ
  have hη : IsLocalizingSequence F η Q := hR.min hκ
  let ρ : ℕ → Ω → WithTop ℝ≥0 := min τ η
  have hρ : IsLocalizingSequence F ρ Q := hτQ.min hη
  have hXcadQ : HasCadlagPaths X Q := hQP.ae_le hXcad
  apply isLocalMartingale_of_locally_cadlagUI hFQ hXcadQ
  refine ⟨ρ, hρ, fun n ↦ ?_⟩
  let Y : ℝ≥0 → Ω → ℝ :=
    MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ n ω}.indicator ((densityProcess Q P F * X) t))
      (τ n)
  have hY : IsUIMartingale Y F P ∧ HasCadlagPaths Y P := hU n
  have hmore := (isStable_cadlagUIMartingale hFP) Y hY (η n) (hη.isStoppingTime n)
  have hsource : IsUIMartingale
      (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < ρ n ω}.indicator ((densityProcess Q P F * X) t))
        (ρ n)) F P := by
    have hs := hmore.1
    change IsUIMartingale
      (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < η n ω}.indicator
          (MeasureTheory.stoppedProcess
            (fun u ↦ {ω | 0 < τ n ω}.indicator ((densityProcess Q P F * X) u))
            (τ n) t))
        (η n)) F P at hs
    rw [masked_stoppedProcess_masked_stoppedProcess] at hs
    simpa only [ρ, Pi.inf_apply, inf_comm] using hs
  have hρle ( ω : Ω) : ρ n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
    exact (min_le_right (τ n ω) (η n ω)).trans
      ((min_le_right (R n ω) (κ n ω)) |>.trans_eq rfl)
  let ρfin : FiniteStoppingTime F := FiniteStoppingTime.truncate (hρ.isStoppingTime n) n
  have hρfin : ρfin.withTop = ρ n := by
    funext ω
    rw [FiniteStoppingTime.withTop_truncate]
    exact min_eq_right (hρle ω)
  let Xn : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | 0 < ρ n ω}.indicator (X t)
  have hEn : MeasurableSet[F 0] {ω | 0 < ρ n ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using
      (hρ.isStoppingTime n 0).compl
  have hXnadapt : Adapted F Xn := hXadapt.indicator_initial hEn
  have hXncad : HasCadlagPaths Xn P := hXcad.indicator {ω | 0 < ρ n ω}
  have hweighted : densityProcess Q P F * Xn =
      fun t ↦ {ω | 0 < ρ n ω}.indicator ((densityProcess Q P F * X) t) := by
    ext t ω
    by_cases hω : 0 < ρ n ω <;> simp [Xn, hω]
  have hsourceFin : IsUIMartingale
      (MeasureTheory.stoppedProcess (densityProcess Q P F * Xn) ρfin.withTop) F P := by
    rw [hweighted, hρfin]
    exact hsource
  have htargetFin := hsourceFin.stoppedProcess_of_mul_densityProcess_finite
    ρfin hXnadapt hXncad hQP hFP
      (FiniteStoppingTime.truncate_le (hρ.isStoppingTime n) n)
  have htarget : IsUIMartingale (MeasureTheory.stoppedProcess Xn (ρ n)) F Q := by
    simpa only [hρfin] using htargetFin
  exact ⟨htarget, (hXcadQ.indicator {ω | 0 < ρ n ω}).stoppedProcess (ρ n)⟩

/-- Local-source version of bounded one-way transfer.  The native initial
mask is retained when the source fundamental sequence is intersected with the
possibly-zero stopping time. -/
theorem IsLocalMartingale.stoppedProcess_of_mul_densityProcess_absolutelyContinuous
    {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}
    (hZX : IsLocalMartingale
      (MeasureTheory.stoppedProcess (densityProcess Q P F * X) σ) F P)
    (hXadapt : Adapted F X) (hXcad : HasCadlagPaths X P)
    (hQP : Q ≪ P) (hFP : F.IsUsual P) (hFQ : F.IsUsual Q)
    (hσ : IsStoppingTime F σ)
    {T : ℝ≥0} (hbound : ∀ ω, σ ω ≤ T) :
    IsLocalMartingale (MeasureTheory.stoppedProcess X σ) F Q := by
  let Xpos : ℝ≥0 → Ω → ℝ :=
    fun t ↦ {ω | 0 < σ ω}.indicator (X t)
  have hσposMeas : MeasurableSet[F 0] {ω | 0 < σ ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using (hσ 0).compl
  have hXposAdapt : Adapted F Xpos := hXadapt.indicator_initial hσposMeas
  have hXposCad : HasCadlagPaths Xpos P := hXcad.indicator {ω | 0 < σ ω}
  have hweightedPos : densityProcess Q P F * Xpos =
      fun t ↦ {ω | 0 < σ ω}.indicator ((densityProcess Q P F * X) t) := by
    ext t ω
    by_cases hω : 0 < σ ω <;> simp [Xpos, hω]
  have hZXpos : IsLocalMartingale
      (MeasureTheory.stoppedProcess (densityProcess Q P F * Xpos) σ) F P := by
    have hs := hZX.indicator_initial hσposMeas
    rw [hweightedPos, stoppedProcess_indicator_comm']
    exact hs
  have hmain : IsLocalMartingale
      (MeasureTheory.stoppedProcess Xpos σ) F Q := by
    obtain ⟨τ, hτ, hU⟩ := hZXpos.locally_cadlagUI
    have hτQ : IsLocalizingSequence F τ Q :=
      { isStoppingTime := hτ.isStoppingTime
        tendsto_top := hQP.ae_le hτ.tendsto_top
        mono := hQP.ae_le hτ.mono }
    have hXposCadQ : HasCadlagPaths Xpos Q := hQP.ae_le hXposCad
    have hXstopCadQ : HasCadlagPaths (MeasureTheory.stoppedProcess Xpos σ) Q :=
      hXposCadQ.stoppedProcess σ
    apply isLocalMartingale_of_locally_cadlagUI hFQ hXstopCadQ
    refine ⟨τ, hτQ, fun n ↦ ?_⟩
    let ρ : Ω → WithTop ℝ≥0 := fun ω ↦ min (τ n ω) (σ ω)
    have hρ : IsStoppingTime F ρ := (hτ.isStoppingTime n).min hσ
    have hρbound : ∀ ω, ρ ω ≤ T := fun ω ↦
      (min_le_right (τ n ω) (σ ω)).trans (hbound ω)
    have hsource : IsUIMartingale
        (MeasureTheory.stoppedProcess
          (fun t ↦ {ω | 0 < ρ ω}.indicator
            ((densityProcess Q P F * Xpos) t)) ρ) F P := by
      have hs := (hU n).1
      change IsUIMartingale
        (MeasureTheory.stoppedProcess
          (fun t ↦ {ω | 0 < τ n ω}.indicator
            (MeasureTheory.stoppedProcess
              (densityProcess Q P F * Xpos) σ t)) (τ n)) F P at hs
      rw [hweightedPos, masked_stoppedProcess_masked_stoppedProcess] at hs
      have hρeq : τ n ⊓ σ = ρ := by
        ext ω
        rfl
      rw [hρeq] at hs
      convert hs using 1
      ext t ω
      rw [stoppedProcess_indicator_comm, stoppedProcess_indicator_comm]
      by_cases hρω : 0 < ρ ω
      · have hσω : 0 < σ ω := (lt_min_iff.mp hρω).2
        rw [Set.indicator_of_mem
          (show ω ∈ {ω | 0 < ρ ω} from hρω),
          Set.indicator_of_mem (show ω ∈ {ω | 0 < ρ ω} from hρω)]
        simp [MeasureTheory.stoppedProcess, Xpos, hσω]
      · rw [Set.indicator_of_notMem
          (show ω ∉ {ω | 0 < ρ ω} from hρω),
          Set.indicator_of_notMem (show ω ∉ {ω | 0 < ρ ω} from hρω)]
    let ρfin : FiniteStoppingTime F := FiniteStoppingTime.truncate hρ T
    have hρfin : ρfin.withTop = ρ := by
      funext ω
      rw [FiniteStoppingTime.withTop_truncate]
      exact min_eq_right (hρbound ω)
    let Xn : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | 0 < ρ ω}.indicator (Xpos t)
    have hEmeas : MeasurableSet[F 0] {ω | 0 < ρ ω} := by
      simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using (hρ 0).compl
    have hXnadapt : Adapted F Xn := hXposAdapt.indicator_initial hEmeas
    have hXncad : HasCadlagPaths Xn P := hXposCad.indicator {ω | 0 < ρ ω}
    have hweighted : densityProcess Q P F * Xn =
        fun t ↦ {ω | 0 < ρ ω}.indicator
          ((densityProcess Q P F * Xpos) t) := by
      ext t ω
      by_cases hω : 0 < ρ ω <;> simp [Xn, hω]
    have hsourceFin : IsUIMartingale
        (MeasureTheory.stoppedProcess (densityProcess Q P F * Xn) ρfin.withTop) F P := by
      rw [hweighted, hρfin]
      exact hsource
    have htargetFin := hsourceFin.stoppedProcess_of_mul_densityProcess_finite
      ρfin hXnadapt hXncad hQP hFP (FiniteStoppingTime.truncate_le hρ T)
    have htargetρ : IsUIMartingale
        (MeasureTheory.stoppedProcess Xn ρ) F Q := by
      simpa only [hρfin] using htargetFin
    have htarget : IsUIMartingale
        (MeasureTheory.stoppedProcess
          (fun t ↦ {ω | 0 < τ n ω}.indicator
            (MeasureTheory.stoppedProcess Xpos σ t)) (τ n)) F Q := by
      simp only [Xpos]
      rw [masked_stoppedProcess_masked_stoppedProcess]
      have hρeq : τ n ⊓ σ = ρ := by
        ext ω
        rfl
      rw [hρeq]
      convert htargetρ using 1
      ext t ω
      rw [stoppedProcess_indicator_comm, stoppedProcess_indicator_comm]
      by_cases hρω : 0 < ρ ω
      · have hσω : 0 < σ ω := (lt_min_iff.mp hρω).2
        rw [Set.indicator_of_mem
          (show ω ∈ {ω | 0 < ρ ω} from hρω),
          Set.indicator_of_mem (show ω ∈ {ω | 0 < ρ ω} from hρω)]
        simp [MeasureTheory.stoppedProcess, Xpos, hσω]
      · rw [Set.indicator_of_notMem
          (show ω ∉ {ω | 0 < ρ ω} from hρω),
          Set.indicator_of_notMem (show ω ∉ {ω | 0 < ρ ω} from hρω)]
    exact ⟨htarget,
      (hXstopCadQ.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)⟩
  have hσzeroMeas : MeasurableSet[F 0] {ω | σ ω = 0} := hσ.measurableSet_eq 0
  have hinit : IsLocalMartingale
      (fun _ : ℝ≥0 ↦ {ω | σ ω = 0}.indicator (X 0)) F Q :=
    (isContinuousLocalMartingale_const_initial
      ((hXadapt 0).indicator hσzeroMeas)).1
  rw [stoppedProcess_eq_masked_add_initial]
  exact hmain.add hinit hFQ

end ProbabilityTheory

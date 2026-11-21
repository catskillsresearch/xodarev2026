/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ClassDPredictableJump
public import StochLean.Probability.Martingale.Doob.CenteredSingleJump
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedUsual
public import StochLean.Probability.Process.Stopping.JumpExitIntegrability

/-! # Removing the conditional mean of an actual predictable jump

An announcing sequence clipped to a deterministic interval gives actual finite
stopping values. Bounded optional sampling bounds the mean drop between these
values by the original supermartingale drop. Class D gives uniform
integrability, so the genuine cadlag announcing limit passes this inequality
to the actual jump on the interval `(s,t]`.

First the original jump itself is removed. The existing centered single-jump
martingale then replaces it by its conditional mean before the predictable
lifetime. Neither a compensator nor a martingale or convergence certificate
is an assumption of the final theorem. The left endpoint is excluded, the
right endpoint is included, and an infinite lifetime contributes zero.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {γ : Ω → WithTop ℝ≥0}

private theorem setIntegral_finite_sample_le
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (S U : FiniteStoppingTime F)
    (hle : ∀ ω, S ω ≤ U ω) {T : ℝ≥0} (hb : ∀ ω, U ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[S.measurableSpace] A) :
    (∫ ω in A, X (U ω) ω ∂P) ≤ ∫ ω in A, X (S ω) ω ∂P := by
  have hcomp := hX.condExp_finiteStoppingTime_value_ae_le_of_le hF
    hc.hasRightContinuousPaths S U hle hb
  calc
    _ = ∫ ω in A, P[(fun ω ↦ X (U ω) ω) | S.measurableSpace] ω ∂P :=
      (setIntegral_condExp S.measurableSpace_le
        (hXD.integrable_finiteStoppingTime_value U) hA).symm
    _ ≤ _ := setIntegral_mono_ae integrable_condExp.integrableOn
      (hXD.integrable_finiteStoppingTime_value S).integrableOn hcomp

omit [IsFiniteMeasure P] in
private theorem tendsto_clipped_announcing_value {ω : Ω}
    (hc : IsCadlagPath (X · ω)) (s t : ℝ≥0) (hst : s ≤ t)
    (η : ℕ → WithTop ℝ≥0) (S : ℕ → ℝ≥0) (U : ℝ≥0)
    (hS : ∀ n, (S n : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (max (s : WithTop ℝ≥0) (η n)))
    (hU : (U : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (max (s : WithTop ℝ≥0) (γ ω)))
    (hle : ∀ n, η n ≤ γ ω) (hstrict : ∀ n, 0 < γ ω → η n < γ ω)
    (hlim : Tendsto η atTop (𝓝 (γ ω))) :
    Tendsto (fun n ↦ X (S n) ω) atTop
      (𝓝 (X U ω - {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ) ω)) := by
  classical
  by_cases hs : γ ω ≤ (s : WithTop ℝ≥0)
  · have hSn (n : ℕ) : S n = s := by
      apply WithTop.coe_injective
      rw [hS, max_eq_left ((hle n).trans hs), min_eq_right (WithTop.coe_le_coe.mpr hst)]
    have hUs : U = s := by
      apply WithTop.coe_injective
      rw [hU, max_eq_left hs, min_eq_right (WithTop.coe_le_coe.mpr hst)]
    have hnot : ω ∉ {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)} :=
      fun h ↦ (not_lt.mpr hs) h.1
    simp only [hSn, hUs, indicator_of_notMem hnot, sub_zero]
    exact tendsto_const_nhds
  · have hsg : (s : WithTop ℝ≥0) < γ ω := lt_of_not_ge hs
    by_cases ht : γ ω ≤ (t : WithTop ℝ≥0)
    · have hfinite : γ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ht
      obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hγu : γ ω = (u : WithTop ℝ≥0) := hu.symm
      have hsu : s < u := WithTop.coe_lt_coe.mp (hγu ▸ hsg)
      have hut : u ≤ t := WithTop.coe_le_coe.mp (hγu ▸ ht)
      have hUu : U = u := by
        apply WithTop.coe_injective
        rw [hU, hγu, max_eq_right (WithTop.coe_le_coe.mpr hsu.le),
          min_eq_right (WithTop.coe_le_coe.mpr hut)]
      have hcoelim :=
        (tendsto_const_nhds (x := (t : WithTop ℝ≥0))).min
          ((tendsto_const_nhds (x := (s : WithTop ℝ≥0))).max hlim)
      rw [← hU, hUu] at hcoelim
      have htime : Tendsto S atTop (𝓝 u) := by
        have hh := (WithTop.tendsto_untopA (a := (u : WithTop ℝ≥0))
          WithTop.coe_ne_top).comp hcoelim
        simpa only [← hS, Function.comp_def, WithTop.untopA, WithTop.untopD_coe] using hh
      have hlt (n : ℕ) : S n < u := by
        apply WithTop.coe_lt_coe.mp
        rw [hS, ← hγu]
        exact (min_le_right _ _).trans_lt
          (max_lt hsg (hstrict n (bot_le.trans_lt hsg)))
      have hleft := (hc.tendsto_leftLimitProcess (ne_of_gt (bot_le.trans_lt hsu))).comp
        (tendsto_nhdsWithin_iff.mpr ⟨htime, Eventually.of_forall hlt⟩)
      have he : X U ω -
          {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)}.indicator
            (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ) ω =
          leftLimitProcess X u ω := by
        rw [hUu, indicator_of_mem (show ω ∈
          {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)} from ⟨hsg, ht⟩),
          stoppedValueWithTerminal_jump_eq_of_eq_coe hγu]
        change X u ω - (X u ω - leftLimitProcess X u ω) = leftLimitProcess X u ω
        ring
      rw [he]
      exact hleft
    · have htg : (t : WithTop ℝ≥0) < γ ω := lt_of_not_ge ht
      have hUt : U = t := by
        apply WithTop.coe_injective
        rw [hU, min_eq_left (htg.le.trans (le_max_right _ _))]
      have hnot : ω ∉ {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)} :=
        fun h ↦ ht h.2
      rw [hUt, indicator_of_notMem hnot, sub_zero]
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually (Ioi_mem_nhds htg)] with n hn
      have he : S n = t := by
        apply WithTop.coe_injective
        rw [hS, min_eq_left ((show (t : WithTop ℝ≥0) < η n from hn).le.trans
          (le_max_right _ _))]
      exact congrArg (fun r ↦ X r ω) he.symm

private theorem setIntegral_drop_le_actual_predictable_jump
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hγ : IsPredictableStoppingTime F γ P)
    (hiJ : Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ) P)
    (s t : ℝ≥0) (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (∫ ω in A, X t ω ∂P) - (∫ ω in A, X s ω ∂P) ≤
      ∫ ω in A, {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ) ω ∂P := by
  classical
  obtain ⟨η, hη, hηle⟩ := hγ.exists_announcing_le
  let S : ℕ → FiniteStoppingTime F := fun n ↦
    FiniteStoppingTime.truncate ((isStoppingTime_const F s).max (hη.isStoppingTime n)) t
  let U : FiniteStoppingTime F :=
    FiniteStoppingTime.truncate ((isStoppingTime_const F s).max hγ.1) t
  have hS (n : ℕ) (ω : Ω) : (S n ω : WithTop ℝ≥0) =
      min (t : WithTop ℝ≥0) (max (s : WithTop ℝ≥0) (η n ω)) :=
    congrFun (FiniteStoppingTime.withTop_truncate _ t) ω
  have hU (ω : Ω) : (U ω : WithTop ℝ≥0) =
      min (t : WithTop ℝ≥0) (max (s : WithTop ℝ≥0) (γ ω)) :=
    congrFun (FiniteStoppingTime.withTop_truncate _ t) ω
  have hsS (n : ℕ) (ω : Ω) : s ≤ S n ω := by
    apply WithTop.coe_le_coe.mp
    rw [hS]
    exact le_min (WithTop.coe_le_coe.mpr hst) (le_max_left _ _)
  have hSt (n : ℕ) (ω : Ω) : S n ω ≤ t := FiniteStoppingTime.truncate_le _ _ _
  have hsU (ω : Ω) : s ≤ U ω := by
    apply WithTop.coe_le_coe.mp
    rw [hU]
    exact le_min (WithTop.coe_le_coe.mpr hst) (le_max_left _ _)
  have hUt (ω : Ω) : U ω ≤ t := FiniteStoppingTime.truncate_le _ _ _
  let E : Set Ω := {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)}
  let JJ := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ
  have hE : MeasurableSet E := (F.le s _ (hγ.1.measurableSet_gt s)).inter
    (F.le t _ (hγ.1 t))
  let L : Ω → ℝ := (fun ω ↦ X (U ω) ω) - E.indicator JJ
  have hiU := hXD.integrable_finiteStoppingTime_value U
  have hiL : Integrable L P := hiU.sub (hiJ.indicator hE)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (S n ω) ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hc, hη.tendsto] with ω hcω hlimω
    exact tendsto_clipped_announcing_value hcω s t hst (fun n ↦ η n ω)
      (fun n ↦ S n ω) (U ω) (fun n ↦ hS n ω) (hU ω)
      (fun n ↦ hηle n ω) (fun n ↦ hη.strict n ω) hlimω
  have hUI := hXD.uniformIntegrable_finiteStoppingTime S
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp) hUI.1
    (memLp_one_iff_integrable.mpr hiL) hUI.2.1 hlim
  have hlimInt := tendsto_setIntegral_of_L1' L hiL.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hXD.integrable_finiteStoppingTime_value (S n)) hL1 A
  have hAS : MeasurableSet[(FiniteStoppingTime.const F s).measurableSpace] A :=
    (isStoppingTime_const F s).le_measurableSpace_of_const_le (fun _ ↦ le_rfl) A hA
  have hAU : MeasurableSet[U.measurableSpace] A :=
    U.isStoppingTime.le_measurableSpace_of_const_le
      (fun ω ↦ WithTop.coe_le_coe.mpr (hsU ω)) A hA
  have hbound (n : ℕ) :
      (∫ ω in A, X (S n ω) ω ∂P) - (∫ ω in A, X (U ω) ω ∂P) ≤
        (∫ ω in A, X s ω ∂P) - ∫ ω in A, X t ω ∂P := by
    have hfirst := setIntegral_finite_sample_le hX hXD hF hc
      (FiniteStoppingTime.const F s) (S n) (hsS n) (hSt n) hAS
    have hlast := setIntegral_finite_sample_le hX hXD hF hc
      U (FiniteStoppingTime.const F t) hUt (fun _ ↦ le_rfl) hAU
    exact sub_le_sub hfirst hlast
  have hh := le_of_tendsto (hlimInt.sub tendsto_const_nhds)
    (Eventually.of_forall hbound)
  have he : (∫ ω in A, L ω ∂P) =
      (∫ ω in A, X (U ω) ω ∂P) - ∫ ω in A, E.indicator JJ ω ∂P :=
    integral_sub hiU.integrableOn (hiJ.indicator hE).integrableOn
  rw [he] at hh
  change (∫ ω in A, X t ω ∂P) - (∫ ω in A, X s ω ∂P) ≤
    ∫ ω in A, E.indicator JJ ω ∂P
  linarith

/-- Removing the actual before-conditional mean of a positive predictable
jump from a cadlag Class D supermartingale preserves supermartingality.
The jump coefficient is proved integrable, not supplied as an extra input. -/
theorem Supermartingale.sub_predictable_jump_condExp
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hγ : IsPredictableStoppingTime F γ P)
    (hpos : ∀ᵐ ω ∂P, 0 < γ ω) :
    Supermartingale (X - (fun t : ℝ≥0 ↦ {ω | γ ω ≤ (t : WithTop ℝ≥0)}.indicator
      P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ |
        hγ.1.measurableSpaceBefore])) F P := by
  classical
  let JJ := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) γ
  let J : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | γ ω ≤ (t : WithTop ℝ≥0)}.indicator JJ
  let K := P[JJ | hγ.1.measurableSpaceBefore]
  have hiJ : Integrable JJ P := hXD.integrable_stopped_jump_of_predictable hc hγ hpos
  have hmJ : StronglyMeasurable[hγ.1.measurableSpace] JJ :=
    hX.stronglyAdapted.adapted.stronglyMeasurable_stopped_jump_of_usual hF hc hγ.1
  have haJ : StronglyAdapted F J := fun t ↦ hmJ.indicator_stoppingTime_le hγ.1 t
  have hJD : IsClassD J F P := isClassD_indicator_stoppingTime_le hγ.1 hmJ hiJ
  let N : ℝ≥0 → Ω → ℝ := X - J
  have haN : StronglyAdapted F N := hX.stronglyAdapted.sub haJ
  have hND : IsClassD N F P := hXD.sub hJD
  have hsub : Submartingale (-N) F P := by
    apply submartingale_of_setIntegral_le haN.neg (fun t ↦ (hND.integrable t).neg)
    intro s t hst A hA
    let E : Set Ω := {v | (s : WithTop ℝ≥0) < γ v ∧ γ v ≤ (t : WithTop ℝ≥0)}
    have he : J t - J s = E.indicator JJ := by
      funext ω
      simp only [J, E, Pi.sub_apply, indicator_apply, mem_ofPred_eq]
      by_cases hs : γ ω ≤ (s : WithTop ℝ≥0)
      · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
        simp only [hs, ht, not_lt.mpr hs, if_true, if_false, false_and, sub_self]
      · have hsg : (s : WithTop ℝ≥0) < γ ω := lt_of_not_ge hs
        by_cases ht : γ ω ≤ (t : WithTop ℝ≥0) <;>
          simp only [hs, ht, hsg, if_true, if_false, true_and, sub_zero, sub_self]
    have hdrop := setIntegral_drop_le_actual_predictable_jump hX hXD hF hc hγ hiJ s t hst hA
    have heInt : (∫ ω in A, J t ω ∂P) - (∫ ω in A, J s ω ∂P) =
        ∫ ω in A, E.indicator JJ ω ∂P := by
      rw [← integral_sub (hJD.integrable t).integrableOn (hJD.integrable s).integrableOn]
      exact integral_congr_ae (ae_of_all _ fun ω ↦ congrFun he ω)
    change (∫ ω in A, -(X s ω - J s ω) ∂P) ≤
      ∫ ω in A, -(X t ω - J t ω) ∂P
    rw [integral_neg, integral_neg,
      integral_sub (hX.integrable s).integrableOn (hJD.integrable s).integrableOn,
      integral_sub (hX.integrable t).integrableOn (hJD.integrable t).integrableOn]
    change (∫ ω in A, X t ω ∂P) - (∫ ω in A, X s ω ∂P) ≤
      ∫ ω in A, E.indicator JJ ω ∂P at hdrop
    linarith
  have hN : Supermartingale N F P := by simpa only [neg_neg] using hsub.neg
  have hMc := (isUIMartingale_indicator_sub_condExp_before hγ.1 hmJ hiJ).1
  have he : N + (fun t : ℝ≥0 ↦ {ω | γ ω ≤ (t : WithTop ℝ≥0)}.indicator (JJ - K)) =
      X - (fun t : ℝ≥0 ↦ {ω | γ ω ≤ (t : WithTop ℝ≥0)}.indicator K) := by
    funext t ω
    simp only [N, J, Pi.sub_apply, Pi.add_apply, indicator_apply, mem_ofPred_eq]
    by_cases ht : γ ω ≤ (t : WithTop ℝ≥0) <;> simp only [ht, if_true, if_false] <;> ring
  rw [← he]
  exact hN.add_martingale hMc

end MeasureTheory

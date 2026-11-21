/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ClassDPredictableJump
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedStopping
public import StochLean.Probability.Martingale.OptionalSampling.AnnouncingBefore
public import StochLean.Probability.Process.Path.JumpStopping
public import StochLean.Probability.Process.Stopping.JumpCoefficients

/-! # Conditional predictable jump means of Class D supermartingales

The original zero-terminal jump is integrable before its conditional mean is
considered. For each deterministic cap `T`, minimum optional sampling has a
bounded upper endpoint but retains the announcing time's original stopped
field. Levy upward convergence then gives the before-field inequality.

The capped process has the actual terminal value `X T`. At an infinite
predictable lifetime, both stopped values in the difference use this same
terminal value; the announcing samples reach the constant part of the capped
path. No terminal limit for the original process is introduced.

The actual capped jump is the original jump multiplied by the before-measurable
event `{τ ≤ T}`. Integer caps cover every finite lifetime. On `{τ = ∞}`, a
separate before-field indicator identity proves that the conditional mean is
zero. This yields a nonpositive conditional mean, not an actual zero jump.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private theorem condExp_capped_jump_before_le_zero
    (hX : Supermartingale X F P) (hD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (T : ℝ≥0) :
    P[stoppedValueWithTerminal
        (jumpProcess (stoppedProcess X (fun _ ↦ (T : WithTop ℝ≥0))))
        (fun _ ↦ (0 : ℝ)) τ | hτ.1.measurableSpaceBefore] ≤ᵐ[P] 0 := by
  let Y := stoppedProcess X (fun _ ↦ (T : WithTop ℝ≥0))
  let Z := X T
  let U : Ω → WithTop ℝ≥0 := fun ω ↦ min (τ ω) (T : WithTop ℝ≥0)
  let V := stoppedValue X U
  let L := stoppedValueWithTerminal (leftLimitProcess Y) Z τ
  let J := stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) τ
  have hU : IsStoppingTime F U := hτ.1.min_const T
  have hUf (ω : Ω) : U ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  have hiV : Integrable V P :=
    hD.integrable_finiteStoppingTime_value (FiniteStoppingTime.ofNotTop hU hUf)
  have hcY : HasCadlagPaths Y P := hc.stoppedProcess _
  have hDY : IsClassD Y F P := hD.stoppedProcess (isStoppingTime_const F T)
  have hiJ : Integrable J P := hDY.integrable_stopped_jump_of_predictable hcY hτ hpos
  have hYa (t : ℝ≥0) (ω : Ω) : Y t ω = X (min t T) ω := by
    simp only [Y, stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
  have hYlim (ω : Ω) : Tendsto (fun t : ℝ≥0 ↦ Y t ω) atTop (𝓝 (Z ω)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    simp only [hYa, min_eq_right ht, Z]
  have he : V - L = J := by
    funext ω
    by_cases ht : τ ω = ⊤
    · simp only [V, U, L, J, Z, stoppedValueWithTerminal_of_top ht, Pi.sub_apply,
        stoppedValue, ht, min_eq_right le_top, WithTop.untopA, WithTop.untopD_coe, sub_self]
    · simp only [V, U, L, J, stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply,
        stoppedValue, jumpProcess, Y, stoppedProcess,
        WithTop.untopA_eq_untop ht, WithTop.coe_untop]
  have hiL : Integrable L P := (hiV.sub hiJ).congr (by
    filter_upwards with ω
    have hh : V ω - L ω = J ω := congrFun he ω
    change V ω - J ω = L ω
    linarith)
  obtain ⟨η, hη, hηle⟩ := hτ.exists_announcing_le
  have hmono : Monotone η := fun _ _ hnm ω ↦ hη.monotone ω hnm
  let G : Filtration ℕ mΩ := F.stoppingTimeReindex η hη.isStoppingTime hmono
  have heG : hτ.1.measurableSpaceBefore = ⨆ n, G n :=
    hη.measurableSpaceBefore_eq_iSup hτ.1 hF.complete_initial
  have hsample (n : ℕ) : P[V | G n] ≤ᵐ[P] stoppedValue Y (η n) := by
    have hs := hX.condExp_stoppedValue_min_ae_le_of_bounded hF hc.hasRightContinuousPaths
      (hη.isStoppingTime n) hU (fun _ ↦ min_le_right _ _)
    filter_upwards [hs, hpos] with ω hsω hpω
    have hf : η n ω ≠ ⊤ := ne_top_of_lt ((hη.strict n ω hpω).trans_le le_top)
    exact hsω.trans_eq (by
      change X (min (η n ω) (min (τ ω) (T : WithTop ℝ≥0))).untopA ω =
        X (min (((η n ω).untopA : ℝ≥0) : WithTop ℝ≥0) (T : WithTop ℝ≥0)).untopA ω
      rw [← min_assoc, min_eq_left (hηle n ω), WithTop.untopA_eq_untop hf,
        WithTop.coe_untop])
  have hCE : ∀ᵐ ω ∂P, Tendsto (fun n ↦ P[V | G n] ω) atTop
      (𝓝 (P[V | hτ.1.measurableSpaceBefore] ω)) := by
    rw [heG]
    exact tendsto_ae_condExp (ℱ := G) (μ := P) V
  have hbefore : P[V | hτ.1.measurableSpaceBefore] ≤ᵐ[P] L := by
    filter_upwards [hcY, hpos, hη.tendsto, ae_all_iff.mpr hsample, hCE]
      with ω hcω hpω hηω hsω hCEω
    have hfinite (n : ℕ) : η n ω ≠ ⊤ :=
      ne_top_of_lt ((hη.strict n ω hpω).trans_le le_top)
    have hleft : Tendsto (fun n ↦ stoppedValue Y (η n) ω) atTop (𝓝 (L ω)) := by
      by_cases ht : τ ω = ⊤
      · change Tendsto _ atTop
          (𝓝 (stoppedValueWithTerminal (leftLimitProcess Y) Z τ ω))
        rw [stoppedValueWithTerminal_of_top ht]
        have htop : Tendsto (fun n ↦ η n ω) atTop (𝓝 ⊤) := by
          simpa only [ht] using hηω
        have htime : Tendsto (fun n ↦ (η n ω).untopA) atTop atTop := by
          apply tendsto_atTop.mpr
          intro t
          filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp htop t] with n hn
          lift η n ω to ℝ≥0 using hfinite n with s hsval
          exact (WithTop.coe_lt_coe.mp hn).le
        exact (hYlim ω).comp htime
      · change Tendsto _ atTop
          (𝓝 (stoppedValueWithTerminal (leftLimitProcess Y) Z τ ω))
        rw [stoppedValueWithTerminal_of_ne_top ht]
        have hp : 0 < (τ ω).untopA := by
          have hh := hpω
          lift τ ω to ℝ≥0 using ht with t htval
          exact WithTop.coe_lt_coe.mp hh
        have hlt (n : ℕ) : (η n ω).untopA < (τ ω).untopA := by
          have hh := hη.strict n ω hpω
          lift η n ω to ℝ≥0 using hfinite n with s hsval
          lift τ ω to ℝ≥0 using ht with t htval
          exact WithTop.coe_lt_coe.mp hh
        have htime : Tendsto (fun n ↦ (η n ω).untopA) atTop (𝓝[<] (τ ω).untopA) :=
          tendsto_nhdsWithin_iff.mpr
            ⟨(WithTop.tendsto_untopA ht).comp hηω, Eventually.of_forall hlt⟩
        exact (hcω.tendsto_leftLimitProcess (ne_of_gt hp)).comp htime
    exact le_of_tendsto_of_tendsto' hCEω hleft hsω
  have hmonoCE := condExp_mono (m := hτ.1.measurableSpaceBefore)
    integrable_condExp hiL hbefore
  have htower := condExp_condExp_of_le (μ := P) (f := V)
    (show hτ.1.measurableSpaceBefore ≤ hτ.1.measurableSpaceBefore from le_rfl)
    hτ.1.measurableSpaceBefore_le_ambient
  change P[J | hτ.1.measurableSpaceBefore] ≤ᵐ[P] 0
  rw [← he]
  filter_upwards [condExp_sub hiV hiL hτ.1.measurableSpaceBefore, hmonoCE, htower]
    with ω hlin hle htw
  change _ ≤ (0 : ℝ)
  rw [hlin]
  change P[V | hτ.1.measurableSpaceBefore] ω -
    P[L | hτ.1.measurableSpaceBefore] ω ≤ 0
  exact sub_nonpos.mpr (htw ▸ hle)

/-- A cadlag Class D supermartingale has nonpositive conditional jump mean at
every positive predictable lifetime, including lifetimes that can be infinite.
The actual zero-terminal jump is proved integrable before conditional sampling. -/
theorem Supermartingale.condExp_stopped_jump_before_ae_le_zero_of_classD
    (hX : Supermartingale X F P) (hD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ |
      hτ.1.measurableSpaceBefore] ≤ᵐ[P] 0 := by
  classical
  let J := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ
  have hiJ : Integrable J P := hD.integrable_stopped_jump_of_predictable hc hτ hpos
  have hcap (T : ℝ≥0) :
      {ω | τ ω ≤ (T : WithTop ℝ≥0)}.indicator
        P[J | hτ.1.measurableSpaceBefore] ≤ᵐ[P] 0 := by
    let Y := stoppedProcess X (fun _ ↦ (T : WithTop ℝ≥0))
    have hm : MeasurableSet[hτ.1.measurableSpaceBefore]
        {ω | τ ω ≤ (T : WithTop ℝ≥0)} :=
      hτ.1.measurable_before measurableSet_Iic
    have he : stoppedValueWithTerminal (jumpProcess Y) (fun _ ↦ (0 : ℝ)) τ =ᵐ[P]
        {ω | τ ω ≤ (T : WithTop ℝ≥0)}.indicator J := by
      filter_upwards [hc] with ω hcω
      cases ht : τ ω with
      | top =>
        have hnot : ω ∉ {ω | τ ω ≤ (T : WithTop ℝ≥0)} := by
          simpa only [mem_ofPred_eq, ht] using (not_le_of_gt (WithTop.coe_lt_top T))
        rw [stoppedValueWithTerminal_jump_eq_zero_of_top ht, indicator_of_notMem hnot]
      | coe t =>
        rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
        change jumpProcess (stoppedProcess X (fun _ ↦ (T : WithTop ℝ≥0))) t ω = _
        rw [hcω.jumpProcess_stoppedProcess]
        simp only [J, indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe,
          stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
    have hCE := (condExp_congr_ae he).trans (condExp_indicator hiJ hm)
    exact hCE.symm.le.trans (condExp_capped_jump_before_le_zero hX hD hF hc hτ hpos T)
  have htopm : MeasurableSet[hτ.1.measurableSpaceBefore] {ω | τ ω = ⊤} :=
    hτ.1.measurable_before (measurableSet_singleton _)
  have heTop : {ω | τ ω = ⊤}.indicator J = 0 := by
    funext ω
    by_cases ht : τ ω = ⊤
    · have hmem : ω ∈ {ω | τ ω = ⊤} := ht
      simp only [indicator_of_mem hmem, J, stoppedValueWithTerminal_of_top ht, Pi.zero_apply]
    · have hnot : ω ∉ {ω | τ ω = ⊤} := ht
      simp only [indicator_of_notMem hnot, Pi.zero_apply]
  have hCEtop : {ω | τ ω = ⊤}.indicator P[J | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
    have hh := condExp_indicator hiJ htopm
    rw [heTop, condExp_zero] at hh
    exact hh.symm
  filter_upwards [ae_all_iff.mpr (fun n : ℕ ↦ hcap n), hCEtop] with ω hn htop
  change P[J | hτ.1.measurableSpaceBefore] ω ≤ 0
  by_cases ht : τ ω = ⊤
  · have hmem : ω ∈ {ω | τ ω = ⊤} := ht
    simpa only [indicator_of_mem hmem, Pi.zero_apply] using htop.le
  · lift τ ω to ℝ≥0 using ht with t htval
    obtain ⟨n, hnt⟩ := exists_nat_ge t
    have hmem : ω ∈ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
      change τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      rw [← htval]
      exact WithTop.coe_le_coe.mpr hnt
    simpa only [indicator_of_mem hmem, Pi.zero_apply] using hn n

end MeasureTheory

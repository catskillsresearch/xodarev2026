/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.KazamakiNovikov
public import StochLean.Probability.Martingale.Convergence.ContinuousL1Bounded
public import StochLean.Probability.Martingale.Convergence.ContinuousL1Limit

/-! # Kazamaki's criterion

This file closes Protter III.44.  The terminal proof uses the lower limit of
the half-exponential along integer times.  Thus no separate, unjustified
terminal value for the original local martingale is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure P] [SigmaFiniteFiltration P F]

/-- Fatou's terminal half-exponential supplied directly by the bounded
stopping-time Kazamaki hypothesis. -/
theorem HasKazamakiBound.liminf_half_exp_integer
    {C : ℝ≥0} (hK : HasKazamakiBound M F P C) (ha : Adapted F M) :
    let Y : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
      ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω))
    let H : Ω → ℝ≥0∞ := fun ω ↦ liminf (fun n ↦ Y n ω) atTop
    Measurable H ∧ (∫⁻ ω, H ω ∂P) ≤ C ∧
      (∀ᵐ ω ∂P, H ω ≠ ∞) ∧ Integrable (fun ω ↦ (H ω).toReal) P ∧
      integral P (fun ω ↦ (H ω).toReal) ≤ C := by
  dsimp only
  let Y : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω))
  let H : Ω → ℝ≥0∞ := fun ω ↦ liminf (fun n ↦ Y n ω) atTop
  have hmY (n : ℕ) : Measurable (Y n) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul ((ha (n : ℝ≥0)).mono (F.le _) le_rfl)))
  have hmH : Measurable H := Measurable.liminf hmY
  have hYi (n : ℕ) : Integrable
      (fun ω ↦ Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω)) P :=
    (hK (FiniteStoppingTime.const F (n : ℝ≥0)) (n : ℝ≥0)
      (fun _ ↦ le_rfl)).1
  have hYlin (n : ℕ) : (∫⁻ ω, Y n ω ∂P) =
      ENNReal.ofReal (integral P
        (fun ω ↦ Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω))) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hYi n)
      (ae_of_all P fun _ ↦ (Real.exp_pos _).le)]
  have hYbound (n : ℕ) : (∫⁻ ω, Y n ω ∂P) ≤ (C : ℝ≥0∞) := by
    rw [hYlin]
    exact ENNReal.ofReal_le_coe.mpr
      ((hK (FiniteStoppingTime.const F (n : ℝ≥0)) (n : ℝ≥0)
        (fun _ ↦ le_rfl)).2)
  have hHbound : (∫⁻ ω, H ω ∂P) ≤ (C : ℝ≥0∞) := by
    calc
      (∫⁻ ω, H ω ∂P) ≤ liminf (fun n ↦ ∫⁻ ω, Y n ω ∂P) atTop :=
        lintegral_liminf_le' fun n ↦ (hmY n).aemeasurable
      _ ≤ liminf (fun _ : ℕ ↦ (C : ℝ≥0∞)) atTop :=
        liminf_le_liminf (Eventually.of_forall hYbound)
      _ = (C : ℝ≥0∞) := liminf_const _
  have hHfin : (∫⁻ ω, H ω ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hHbound
  have hHae : ∀ᵐ ω ∂P, H ω ≠ ∞ :=
    (ae_lt_top hmH hHfin).mono fun _ hω ↦ hω.ne
  have hHint : Integrable (fun ω ↦ (H ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hmH.aemeasurable hHfin
  have hHreal : integral P (fun ω ↦ (H ω).toReal) ≤ (C : ℝ) := by
    rw [integral_toReal hmH.aemeasurable
      ((ae_lt_top hmH hHfin))]
    exact (ENNReal.toReal_le_toReal hHfin ENNReal.coe_ne_top).2 hHbound
  simpa only [H, Y] using And.intro hmH
    (And.intro hHbound (And.intro hHae (And.intro hHint hHreal)))

/-- The terminal factor inequality in Kazamaki's proof.  The half-exponential
factor is represented by its integer-time lower limit, which is finite almost
surely by the preceding Fatou estimate. -/
theorem IsContinuousLocalMartingale.kazamaki_terminal_factor
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hK : HasKazamakiBound M F P C)
    {Z : Ω → ℝ}
    (hZlim : ∀ᵐ ω ∂P, Tendsto
      (fun t ↦ (hM.isSemimartingale hF).stochasticExponential hF t ω)
      atTop (𝓝 (Z ω)))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    let Y : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
      ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω))
    let H : Ω → ℝ≥0∞ := fun ω ↦ liminf (fun n ↦ Y n ω) atTop
    ∃ Za : Ω → ℝ, Integrable Za P ∧ (integral P Za = 1) ∧
      (∀ᵐ ω ∂P, 0 ≤ Za ω) ∧ ∀ᵐ ω ∂P, ENNReal.ofReal (Za ω) ≤
        ENNReal.ofReal (Z ω) ^ (a ^ 2) * H ω ^ (2 * a * (1 - a)) := by
  dsimp only
  let Y : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω))
  let H : Ω → ℝ≥0∞ := fun ω ↦ liminf (fun n ↦ Y n ω) atTop
  let hMa := hM.const_mul a
  let Ea := (hMa.isSemimartingale hF).stochasticExponential hF
  have h0a : (fun t ω ↦ a * M t ω) 0 =ᵐ[P] 0 :=
    h0.mono fun _ hω ↦ by simp [hω]
  have hEaClm := hMa.isContinuousLocalMartingale_stochasticExponential hF
  have hEa := hM.isUIMartingale_stochasticExponential_const_mul hF h0 hK ha0 ha1
  obtain ⟨Za, hZai, hZalim, _, hZaclose⟩ :=
    hEa.1.exists_integrable_limit_of_uniformIntegrable
      hEaClm.2.hasRightContinuousPaths hEa.2
  have hZaMean : integral P Za = 1 := by
    have hzero := (hMa.isSemimartingale hF).stochasticExponential_zero_ae hF h0a
    calc
      integral P Za = integral P P[Za | F 0] := (integral_condExp (F.le 0)).symm
      _ = integral P (Ea 0) := integral_congr_ae (hZaclose 0).symm
      _ = integral P (fun _ ↦ (1 : ℝ)) := integral_congr_ae hzero
      _ = 1 := by rw [integral_const, probReal_univ, one_smul]
  have hZaNonneg : ∀ᵐ ω ∂P, 0 ≤ Za ω := by
    filter_upwards [hZalim,
      (hMa.isSemimartingale hF).stochasticExponential_pos_of_continuous hF hMa.2]
      with ω hlim hpos
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun t ↦ (hpos t).le)
  obtain ⟨_, _, hHfin, _, _⟩ := hK.liminf_half_exp_integer hM.1.1
  have hδ0 : 0 ≤ 2 * a * (1 - a) := by positivity
  have hfac : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ENNReal.ofReal (Ea (n : ℝ≥0) ω) =
        ENNReal.ofReal
            ((hM.isSemimartingale hF).stochasticExponential hF (n : ℝ≥0) ω) ^
          (a ^ 2) * Y n ω ^ (2 * a * (1 - a)) := by
    filter_upwards [hM.stochasticExponential_const_mul_formula hF a,
      (hM.isSemimartingale hF).stochasticExponential_of_continuous hF hM.2]
      with ω haω h1ω
    intro n
    have hEpos : 0 < (hM.isSemimartingale hF).stochasticExponential hF
        (n : ℝ≥0) ω := by
      rw [h1ω (n : ℝ≥0)]
      exact Real.exp_pos _
    have hreal : Ea (n : ℝ≥0) ω =
        ((hM.isSemimartingale hF).stochasticExponential hF (n : ℝ≥0) ω) ^
          (a ^ 2) * Real.exp (a * (1 - a) * M (n : ℝ≥0) ω) := by
      dsimp only [Ea, hMa]
      rw [haω (n : ℝ≥0), h1ω (n : ℝ≥0), ← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg hEpos.le _),
      ENNReal.ofReal_rpow_of_pos hEpos,
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
    congr 2
    rw [← Real.exp_mul]
    congr 1
    ring
  refine ⟨Za, hZai, hZaMean, hZaNonneg, ?_⟩
  filter_upwards [hZlim, hZalim, hHfin, hfac] with ω hEω hEaω hHω hfacω
  let u : ℕ → ℝ≥0∞ := fun n ↦
    ENNReal.ofReal ((hM.isSemimartingale hF).stochasticExponential hF
      (n : ℝ≥0) ω) ^ (a ^ 2)
  let v : ℕ → ℝ≥0∞ := fun n ↦ Y n ω ^ (2 * a * (1 - a))
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hu : Tendsto u atTop (𝓝 (ENNReal.ofReal (Z ω) ^ (a ^ 2))) := by
    exact (ENNReal.tendsto_ofReal (hEω.comp hnat)).ennrpow_const (a ^ 2)
  have hEaNat : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Ea (n : ℝ≥0) ω)) atTop
      (𝓝 (ENNReal.ofReal (Za ω))) :=
    ENNReal.tendsto_ofReal (hEaω.comp hnat)
  have hv : liminf v atTop = H ω ^ (2 * a * (1 - a)) := by
    have hmapped := (ENNReal.monotone_rpow_of_nonneg hδ0).map_liminf_of_continuousAt
      (F := (atTop : Filter ℕ)) (fun n : ℕ ↦ Y n ω)
        ENNReal.continuous_rpow_const.continuousAt
    change (liminf (fun n : ℕ ↦ Y n ω) atTop) ^ (2 * a * (1 - a)) =
      liminf (fun n : ℕ ↦ Y n ω ^ (2 * a * (1 - a))) atTop at hmapped
    exact hmapped.symm
  have hprod : liminf (u * v) atTop = ENNReal.ofReal (Za ω) := by
    calc
      liminf (u * v) atTop = liminf
          (fun n : ℕ ↦ ENNReal.ofReal (Ea (n : ℝ≥0) ω)) atTop :=
        liminf_congr (Eventually.of_forall fun n : ℕ ↦ by
          simpa only [u, v, Pi.mul_apply] using (hfacω n).symm)
      _ = ENNReal.ofReal (Za ω) := hEaNat.liminf_eq
  have huTop : limsup u atTop ≠ ∞ := by
    rw [hu.limsup_eq]
    exact ENNReal.rpow_ne_top_of_nonneg (sq_nonneg a) ENNReal.ofReal_ne_top
  have hvTop : liminf v atTop ≠ ∞ := by
    rw [hv]
    exact ENNReal.rpow_ne_top_of_nonneg hδ0 hHω
  have hmul := ENNReal.liminf_mul_le (u := u) (v := v)
    (Or.inr hvTop) (Or.inl huTop)
  rw [hprod, hu.limsup_eq, hv] at hmul
  exact hmul

/-- Protter III.44 (Kazamaki): a uniform half-exponential bound over bounded
stopping times makes the stochastic exponential a uniformly integrable
martingale. -/
theorem IsContinuousLocalMartingale.isUIMartingale_stochasticExponential_of_kazamaki
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hK : HasKazamakiBound M F P C) :
    IsUIMartingale ((hM.isSemimartingale hF).stochasticExponential hF) F P := by
  let E := (hM.isSemimartingale hF).stochasticExponential hF
  let Y : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * M (n : ℝ≥0) ω))
  let H : Ω → ℝ≥0∞ := fun ω ↦ liminf (fun n ↦ Y n ω) atTop
  let Hr : Ω → ℝ := fun ω ↦ (H ω).toReal
  have hEclm := hM.isContinuousLocalMartingale_stochasticExponential hF
  have hEsm := hM.supermartingale_stochasticExponential hF h0
  have hEpos : ∀ᵐ ω ∂P, ∀ t, 0 < E t ω := by
    simpa only [E] using
      (hM.isSemimartingale hF).stochasticExponential_pos_of_continuous hF hM.2
  have hEi (t : ℝ≥0) : Integrable (E t) P := hEsm.integrable t
  have hEmean (t : ℝ≥0) : integral P (E t) ≤ 1 := by
    simpa only [E, FiniteStoppingTime.const_apply] using
      hM.integral_stochasticExponential_stopped_le_one hF h0
        (FiniteStoppingTime.const F t) (T := t) (fun _ ↦ le_rfl)
  have hEnorm (t : ℝ≥0) : integral P (fun ω ↦ ‖E t ω‖) ≤ 1 := by
    rw [integral_congr_ae (hEpos.mono fun ω hω ↦ Real.norm_of_nonneg (hω t).le)]
    exact hEmean t
  obtain ⟨Z, hZi, hZlim⟩ := hEsm.exists_integrable_limit_of_L1_bounded
    hEclm.2.hasRightContinuousPaths hEnorm
  have hZnonneg : ∀ᵐ ω ∂P, 0 ≤ Z ω := by
    filter_upwards [hZlim, hEpos] with ω hlim hpos
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun t ↦ (hpos t).le)
  have hZmean : integral P Z ≤ 1 := by
    have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ≥0)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hlimNat : ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ E (n : ℝ≥0) ω) atTop (𝓝 (Z ω)) :=
      hZlim.mono fun _ hω ↦ hω.comp hnat
    exact (integrable_and_integral_le_of_nonneg_ae_tendsto
      (fun n ↦ hEi (n : ℝ≥0))
      (fun n ↦ hEpos.mono fun ω hω ↦ (hω (n : ℝ≥0)).le)
      hlimNat (by norm_num : (0 : ℝ) ≤ 1) (fun n ↦ hEmean (n : ℝ≥0))).2
  have hZmean0 : 0 ≤ integral P Z := integral_nonneg_of_ae hZnonneg
  obtain ⟨hmH, hHbound, hHfin, hHintegrable, hHrbound⟩ :=
    hK.liminf_half_exp_integer hM.1.1
  have hmHr : Measurable Hr := by
    exact ENNReal.measurable_toReal.comp hmH
  have hHrnonneg (ω : Ω) : 0 ≤ Hr ω := ENNReal.toReal_nonneg
  have hholderBound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
      1 ≤ (integral P Z) ^ (a ^ 2) * (1 + C : ℝ) ^ (1 - a ^ 2) := by
    obtain ⟨Za, hZai, hZaMean, hZaNonneg, hfactor⟩ :=
      hM.kazamaki_terminal_factor hF h0 hK hZlim ha0 ha1
    let p : ℝ := 1 / (a ^ 2)
    let s : ℝ := 1 / (1 - a ^ 2)
    let δ : ℝ := 2 * a * (1 - a)
    let β : ℝ := 2 * a / (1 + a)
    let f : Ω → ℝ := fun ω ↦ ‖Z ω‖ ^ (a ^ 2)
    let g : Ω → ℝ := fun ω ↦ Hr ω ^ δ
    have ha2pos : 0 < a ^ 2 := sq_pos_of_pos ha0
    have ha2lt : a ^ 2 < 1 := by nlinarith [sq_pos_of_pos (sub_pos.mpr ha1)]
    have hp : 1 < p := by
      dsimp only [p]
      exact one_lt_one_div ha2pos ha2lt
    have h1a2 : 0 < 1 - a ^ 2 := sub_pos.mpr ha2lt
    have hs : 1 < s := by
      dsimp only [s]
      exact one_lt_one_div h1a2 (by nlinarith [ha2pos])
    have hps : p.HolderConjugate s := by
      rw [Real.holderConjugate_iff]
      refine ⟨hp, ?_⟩
      dsimp only [p, s]
      field_simp [ha2pos.ne', h1a2.ne']
      ring
    have hδ0 : 0 ≤ δ := by dsimp only [δ]; positivity
    have hβ0 : 0 ≤ β := by dsimp only [β]; positivity
    have hβ1 : β ≤ 1 := by
      dsimp only [β]
      rw [div_le_iff₀ (by linarith : 0 < 1 + a)]
      linarith
    have hmf : AEStronglyMeasurable f P := by
      exact ((Real.continuous_rpow_const (sq_nonneg a)).measurable.comp_aemeasurable
        hZi.norm.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    have hfp : ∀ ω, f ω ^ p = ‖Z ω‖ := by
      intro ω
      dsimp only [f, p]
      rw [← Real.rpow_mul (norm_nonneg _)]
      have he : a ^ 2 * (1 / a ^ 2) = 1 := by field_simp
      rw [he, Real.rpow_one]
    have hfi : Integrable (fun ω ↦ ‖f ω‖ ^ p) P := by
      apply hZi.norm.congr
      exact ae_of_all P fun ω ↦ by
        change ‖Z ω‖ = ‖f ω‖ ^ p
        have hfn : ‖f ω‖ = f ω :=
          Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        rw [hfn, hfp]
    have hfLp : MemLp f (ENNReal.ofReal p) P :=
      memLp_of_integrable_norm_rpow (lt_trans zero_lt_one hp) hmf hfi
    have hmg : AEStronglyMeasurable g P := by
      exact ((Real.continuous_rpow_const hδ0).measurable.comp hmHr).aestronglyMeasurable
    have hgs (ω : Ω) : g ω ^ s = Hr ω ^ β := by
      dsimp only [g, s, δ, β]
      rw [← Real.rpow_mul (hHrnonneg ω)]
      congr 1
      field_simp [h1a2.ne']
      ring
    have hβdom (ω : Ω) : Hr ω ^ β ≤ 1 + Hr ω := by
      by_cases hx : Hr ω ≤ 1
      · exact (Real.rpow_le_one (hHrnonneg ω) hx hβ0).trans
          (by linarith [hHrnonneg ω])
      · have hx' : 1 ≤ Hr ω := le_of_not_ge hx
        exact (Real.rpow_le_rpow_of_exponent_le hx' hβ1).trans
          (by rw [Real.rpow_one]; linarith)
    have hgi : Integrable (fun ω ↦ ‖g ω‖ ^ s) P := by
      apply ((integrable_const (1 : ℝ)).add hHintegrable).mono'
      · have hmPow :=
          (Real.continuous_rpow_const (le_trans zero_lt_one.le hs.le)).measurable
        exact (hmPow.comp_aemeasurable hmg.norm.aemeasurable).aestronglyMeasurable
      · exact ae_of_all P fun ω ↦ by
          have hpow : 0 ≤ ‖g ω‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
          rw [Real.norm_of_nonneg hpow]
          have hgn : ‖g ω‖ = g ω :=
            Real.norm_of_nonneg (Real.rpow_nonneg (hHrnonneg ω) _)
          rw [hgn, hgs]
          exact hβdom ω
    have hgLp : MemLp g (ENNReal.ofReal s) P :=
      memLp_of_integrable_norm_rpow (lt_trans zero_lt_one hs) hmg hgi
    have hrealFactor : ∀ᵐ ω ∂P, Za ω ≤ f ω * g ω := by
      filter_upwards [hfactor, hZaNonneg, hZnonneg, hHfin] with ω hfac hZaω hZω hHω
      have hleft : ENNReal.ofReal (Za ω) ≠ ∞ := ENNReal.ofReal_ne_top
      have hright : ENNReal.ofReal (Z ω) ^ (a ^ 2) * H ω ^ δ ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (sq_nonneg a) ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hδ0 hHω)
      have hr := (ENNReal.toReal_le_toReal hleft hright).2 hfac
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal hZaω, ENNReal.toReal_ofReal hZω] at hr
      dsimp only [f, g]
      simpa only [Real.norm_of_nonneg hZω, Hr, δ] using hr
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g) hps
      (ae_of_all P fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (ae_of_all P fun ω ↦ Real.rpow_nonneg (hHrnonneg ω) _)
      hfLp hgLp
    letI : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal s) 1 := hps.ennrealOfReal
    have hZaProd : integral P Za ≤ integral P (f * g) :=
      integral_mono_ae hZai (hfLp.integrable_mul hgLp) hrealFactor
    have hFint : integral P (fun ω ↦ f ω ^ p) = integral P Z := by
      rw [integral_congr_ae (ae_of_all P hfp)]
      exact integral_congr_ae (hZnonneg.mono fun _ hω ↦ Real.norm_of_nonneg hω)
    have hgbeta_i : Integrable (fun ω ↦ Hr ω ^ β) P := by
      apply hgi.congr
      exact ae_of_all P fun ω ↦ by
        change ‖g ω‖ ^ s = Hr ω ^ β
        have hgn : ‖g ω‖ = g ω :=
          Real.norm_of_nonneg (Real.rpow_nonneg (hHrnonneg ω) _)
        rw [hgn, hgs]
    have hGint : integral P (fun ω ↦ g ω ^ s) ≤ 1 + C := by
      calc
        integral P (fun ω ↦ g ω ^ s) = integral P (fun ω ↦ Hr ω ^ β) :=
          integral_congr_ae (ae_of_all P hgs)
        _ ≤ integral P (fun ω ↦ 1 + Hr ω) :=
          integral_mono hgbeta_i ((integrable_const (1 : ℝ)).add hHintegrable) hβdom
        _ = 1 + integral P Hr := by
          rw [integral_add (integrable_const (1 : ℝ)) hHintegrable,
            integral_const, probReal_univ, one_smul]
        _ ≤ 1 + C := by linarith
    have hGnonneg : 0 ≤ integral P (fun ω ↦ g ω ^ s) :=
      integral_nonneg fun _ ↦ Real.rpow_nonneg (Real.rpow_nonneg (hHrnonneg _) _) _
    have hpowF : (integral P (fun ω ↦ f ω ^ p)) ^ (1 / p) =
        (integral P Z) ^ (a ^ 2) := by
      rw [hFint]
      congr 1
      dsimp only [p]
      field_simp [ha2pos.ne']
    have hpowG : (integral P (fun ω ↦ g ω ^ s)) ^ (1 / s) ≤
        (1 + C : ℝ) ^ (1 - a ^ 2) := by
      have he : 1 / s = 1 - a ^ 2 := by
        dsimp only [s]
        field_simp [h1a2.ne']
      rw [he]
      exact Real.rpow_le_rpow hGnonneg hGint h1a2.le
    calc
      1 = integral P Za := hZaMean.symm
      _ ≤ integral P (f * g) := hZaProd
      _ ≤ (integral P (fun ω ↦ f ω ^ p)) ^ (1 / p) *
          (integral P (fun ω ↦ g ω ^ s)) ^ (1 / s) := hholder
      _ ≤ (integral P Z) ^ (a ^ 2) * (1 + C : ℝ) ^ (1 - a ^ 2) := by
        rw [hpowF]
        exact mul_le_mul_of_nonneg_left hpowG (Real.rpow_nonneg hZmean0 _)
  have hZmeanOne : integral P Z = 1 := by
    apply le_antisymm hZmean
    by_contra hnot
    have hzlt : integral P Z < 1 := lt_of_not_ge hnot
    let Φ : ℝ → ℝ := fun a ↦
      (integral P Z) ^ (a ^ 2) * (1 + C : ℝ) ^ (1 - a ^ 2)
    have hΦlim : Tendsto Φ (𝓝[<] (1 : ℝ)) (𝓝 (integral P Z)) := by
      have ha2 : Tendsto (fun a : ℝ ↦ a ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
        simpa only [one_pow] using
          (continuousAt_pow (1 : ℝ) 2).tendsto.mono_left
            (show nhdsWithin (1 : ℝ) (Iio 1) ≤ nhds (1 : ℝ) from nhdsWithin_le_nhds)
      have hfirst : Tendsto (fun a : ℝ ↦ (integral P Z) ^ (a ^ 2))
          (𝓝[<] (1 : ℝ)) (𝓝 (integral P Z)) := by
        simpa only [Function.comp_def, Real.rpow_one] using
          (Real.continuousAt_const_rpow' one_ne_zero).tendsto.comp ha2
      have hsecond : Tendsto (fun a : ℝ ↦ (1 + C : ℝ) ^ (1 - a ^ 2))
          (𝓝[<] (1 : ℝ)) (𝓝 1) := by
        have he : Tendsto (fun a : ℝ ↦ 1 - a ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
          have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ))
              (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 1) := tendsto_const_nhds
          simpa only [sub_self] using (hone.sub ha2)
        simpa only [Function.comp_def, Real.rpow_zero] using
          (Real.continuousAt_const_rpow
            (by positivity : (1 + C : ℝ) ≠ 0)).tendsto.comp he
      simpa only [Φ, mul_one] using hfirst.mul hsecond
    have hev : ∀ᶠ a in 𝓝[<] (1 : ℝ), Φ a < 1 :=
      hΦlim.eventually (eventually_lt_nhds hzlt)
    have hinterval : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
      exact Ioo_mem_nhdsLT (by norm_num)
    obtain ⟨a, haI, haΦ⟩ := (hev.and (show ∀ᶠ a in 𝓝[<] (1 : ℝ), a ∈ Ioo 0 1 from hinterval)).exists
    exact (not_lt_of_ge (hholderBound haΦ.1 haΦ.2)) haI
  have hset (t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F t] A) :
      (∫ ω in A, Z ω ∂P) ≤ ∫ ω in A, E t ω ∂P := by
    obtain ⟨N, hN⟩ := exists_nat_ge t
    let e : ℕ → ℝ≥0 := fun n ↦ (n + N : ℕ)
    have hte (n : ℕ) : t ≤ e n := by
      exact hN.trans (Nat.cast_le.mpr (by omega))
    have hlim : ∀ᵐ ω ∂(P.restrict A),
        Tendsto (fun n ↦ E (e n) ω) atTop (nhds (Z ω)) := by
      apply ae_restrict_of_ae
      filter_upwards [hZlim] with ω hω
      simpa only [E, e, Function.comp_def] using
        hω.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N))
    have hC0 : 0 ≤ ∫ ω in A, E t ω ∂P :=
      integral_nonneg_of_ae (ae_restrict_of_ae (hEpos.mono fun ω hω ↦ (hω t).le))
    exact (integrable_and_integral_le_of_nonneg_ae_tendsto
      (P := P.restrict A) (fun n ↦ (hEi (e n)).integrableOn)
      (fun n ↦ ae_restrict_of_ae (hEpos.mono fun ω hω ↦ (hω (e n)).le))
      hlim hC0 (fun n ↦ hEsm.setIntegral_le (hte n) hA)).2
  have hEmeanOne (t : ℝ≥0) : integral P (E t) = 1 := by
    apply le_antisymm (hEmean t)
    calc
      1 = integral P Z := hZmeanOne.symm
      _ ≤ integral P (E t) := by
        simpa only [setIntegral_univ] using hset t Set.univ MeasurableSet.univ
  have hclose (t : ℝ≥0) : E t =ᵐ[P] P[Z | F t] := by
    have hneg : -E t ≤ᵐ[P] P[-Z | F t] := by
      apply ae_le_condExp_of_forall_setIntegral_le (F.le t) (hEi t).neg hZi.neg
        (hEsm.stronglyAdapted t).neg
      intro A hA
      simp only [Pi.neg_apply, integral_neg]
      exact neg_le_neg (hset t A hA)
    have hle : P[Z | F t] ≤ᵐ[P] E t := by
      filter_upwards [hneg, condExp_neg Z (F t)] with ω hω heq
      rw [heq] at hω
      exact neg_le_neg_iff.mp hω
    exact ((integral_eq_iff_of_ae_le integrable_condExp (hEi t) hle).mp (by
      rw [integral_condExp (F.le t), hZmeanOne, hEmeanOne t])).symm
  have hEmart : Martingale E F P :=
    (martingale_condExp Z F P).congr hEsm.stronglyAdapted (fun t ↦ (hclose t).symm)
  exact ⟨hEmart, Martingale.uniformIntegrable_of_integrable_closing hZi hclose⟩

end ProbabilityTheory

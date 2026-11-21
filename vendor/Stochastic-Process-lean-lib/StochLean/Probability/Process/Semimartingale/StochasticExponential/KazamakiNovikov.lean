/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Supermartingale
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartQuadraticAlgebra
public import StochLean.Probability.Process.LocalMartingale.ClassD
public import StochLean.Probability.Process.LocalMartingale.FiniteLinearCombination
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableRpow
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Kazamaki and Novikov criteria

The results in this file are Protter III.43--III.45.  They use the project's
single stochastic exponential and continuous quadratic-variation owners.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure P] [SigmaFiniteFiltration P F]

/-- The continuous stochastic exponential of a scalar multiple, expressed
using the original continuous quadratic variation. -/
theorem IsContinuousLocalMartingale.stochasticExponential_const_mul_formula
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P) (c : ℝ) :
    let hcM := hM.const_mul c
    Indistinguishable ((hcM.isSemimartingale hF).stochasticExponential hF)
      (fun t ω ↦ Real.exp (c * M t ω - (1 / 2 : ℝ) * c ^ 2 *
        (hM.isSemimartingale hF).continuousQuadraticVariation hF t ω)) P := by
  dsimp only
  let hS := hM.isSemimartingale hF
  let hcM := hM.const_mul c
  let hcS := hcM.isSemimartingale hF
  have he := hcS.stochasticExponential_of_continuous hF hcM.2
  have hq := hS.continuousQuadraticVariation_const_mul hF c
  filter_upwards [he, hq] with ω heω hqω t
  rw [heω t, hqω t]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring_nf

/-- Protter III.43: the half-exponential moment of a continuous local
martingale at a bounded stopping time is controlled by the half-exponential
moment of its quadratic variation. -/
theorem IsContinuousLocalMartingale.integrable_and_integral_exp_half_stopped_le_sqrt_integral_exp_half_quadraticVariation
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T)
    (hquad : Integrable (fun ω ↦ Real.exp ((1 / 2 : ℝ) *
      (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω)) P) :
    Integrable (fun ω ↦ Real.exp ((1 / 2 : ℝ) * M (τ ω) ω)) P ∧
      (∫ ω, Real.exp ((1 / 2 : ℝ) * M (τ ω) ω) ∂P) ≤
        Real.sqrt (∫ ω, Real.exp ((1 / 2 : ℝ) *
          (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω) ∂P) := by
  let hS := hM.isSemimartingale hF
  let E := hS.stochasticExponential hF
  let Q := hS.continuousQuadraticVariation hF
  let f : Ω → ℝ := fun ω ↦ Real.sqrt (E (τ ω) ω)
  let g : Ω → ℝ := fun ω ↦ Real.sqrt (Real.exp ((1 / 2 : ℝ) * Q (τ ω) ω))
  have hEclm := hM.isContinuousLocalMartingale_stochasticExponential hF
  have hEsm := hM.supermartingale_stochasticExponential hF h0
  have hiE : Integrable (fun ω ↦ E (τ ω) ω) P :=
    hEsm.integrable_finiteStoppingTime_value τ hb hEclm.2.hasRightContinuousPaths
  have hmE : Measurable (fun ω ↦ E (τ ω) ω) :=
    by
      rw [← FiniteStoppingTime.stoppedValue_eq E τ]
      exact (hEsm.stronglyAdapted.measurable_stoppedValue_of_usual hF
        hEclm.2.hasRightContinuousPaths τ.isStoppingTime).mono τ.measurableSpace_le le_rfl
  have hmf : AEStronglyMeasurable f P :=
    (Real.continuous_sqrt.measurable.comp hmE).aestronglyMeasurable
  have hfgsq : ∀ᵐ ω ∂P, f ω ^ 2 = E (τ ω) ω := by
    filter_upwards [hS.stochasticExponential_pos_of_continuous hF hM.2] with ω hω
    exact Real.sq_sqrt (hω (τ ω)).le
  have hf2 : MemLp f 2 P := by
    apply (memLp_two_iff_integrable_sq hmf).mpr
    apply hiE.congr
    filter_upwards [hfgsq] with ω hω
    exact hω.symm
  have hmQ : Measurable (fun ω ↦ Q (τ ω) ω) :=
    by
      rw [← FiniteStoppingTime.stoppedValue_eq Q τ]
      exact ((hS.adapted_continuousQuadraticVariation hF).stronglyAdapted
        |>.measurable_stoppedValue_of_usual hF
          (hS.hasContinuousPaths_continuousQuadraticVariation hF).hasRightContinuousPaths
          τ.isStoppingTime).mono τ.measurableSpace_le le_rfl
  have hmg : AEStronglyMeasurable g P :=
    (Real.continuous_sqrt.measurable.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul hmQ))).aestronglyMeasurable
  have hggsq : ∀ ω, g ω ^ 2 = Real.exp ((1 / 2 : ℝ) * Q (τ ω) ω) :=
    fun ω ↦ Real.sq_sqrt (Real.exp_pos _).le
  have hg2 : MemLp g 2 P := by
    apply (memLp_two_iff_integrable_sq hmg).mpr
    exact hquad.congr (ae_of_all P fun ω ↦ (hggsq ω).symm)
  have hformula : ∀ᵐ ω ∂P,
      Real.exp ((1 / 2 : ℝ) * M (τ ω) ω) = f ω * g ω := by
    filter_upwards [hS.stochasticExponential_of_continuous hF hM.2] with ω hω
    change Real.exp ((1 / 2 : ℝ) * M (τ ω) ω) =
      Real.sqrt (hS.stochasticExponential hF (τ ω) ω) *
        Real.sqrt (Real.exp ((1 / 2 : ℝ) *
          hS.continuousQuadraticVariation hF (τ ω) ω))
    rw [hω (τ ω)]
    rw [← Real.exp_half, ← Real.exp_half, ← Real.exp_add]
    congr 1
    ring
  have hiProd : Integrable (f * g) P := by
    letI : (2 : ℝ≥0∞).HolderTriple 2 1 := by
      simpa using Real.HolderConjugate.two_two.ennrealOfReal
    exact hf2.integrable_mul hg2
  have hiHalf : Integrable (fun ω ↦ Real.exp ((1 / 2 : ℝ) * M (τ ω) ω)) P :=
    hiProd.congr (hformula.mono fun ω hω ↦ by simpa only [Pi.mul_apply] using hω.symm)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g)
    Real.HolderConjugate.two_two
    (ae_of_all P fun _ ↦ Real.sqrt_nonneg _) (ae_of_all P fun _ ↦ Real.sqrt_nonneg _)
    (by simpa using hf2) (by simpa using hg2)
  rw [← integral_congr_ae hformula] at hcs
  have hEbound := hM.integral_stochasticExponential_stopped_le_one hF h0 τ hb
  have hqnonneg : 0 ≤ ∫ ω, Real.exp ((1 / 2 : ℝ) * Q (τ ω) ω) ∂P :=
    integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have hsqrtE : Real.sqrt (∫ ω, E (τ ω) ω ∂P) ≤ 1 := by
    exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith only [hEbound]⟩
  have hsqrtQ : 0 ≤ Real.sqrt (∫ ω, Real.exp ((1 / 2 : ℝ) * Q (τ ω) ω) ∂P) :=
    Real.sqrt_nonneg _
  have hcs' : (∫ ω, Real.exp ((1 / 2 : ℝ) * M (τ ω) ω) ∂P) ≤
      Real.sqrt (∫ ω, E (τ ω) ω ∂P) *
        Real.sqrt (∫ ω, Real.exp ((1 / 2 : ℝ) * Q (τ ω) ω) ∂P) := by
    simp only [Real.rpow_two] at hcs
    rw [integral_congr_ae hfgsq,
      integral_congr_ae (ae_of_all P hggsq)] at hcs
    simpa only [Real.sqrt_eq_rpow] using hcs
  exact ⟨hiHalf, hcs'.trans (by nlinarith)⟩

/-- Protter III.43, inequality-only form. -/
theorem IsContinuousLocalMartingale.integral_exp_half_stopped_le_sqrt_integral_exp_half_quadraticVariation
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T)
    (hquad : Integrable (fun ω ↦ Real.exp ((1 / 2 : ℝ) *
      (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω)) P) :
    (∫ ω, Real.exp ((1 / 2 : ℝ) * M (τ ω) ω) ∂P) ≤
      Real.sqrt (∫ ω, Real.exp ((1 / 2 : ℝ) *
        (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω) ∂P) :=
  (hM.integrable_and_integral_exp_half_stopped_le_sqrt_integral_exp_half_quadraticVariation
    hF h0 τ hb hquad).2

/-- Uniform Kazamaki half-exponential control over all bounded finite
stopping times. -/
def HasKazamakiBound (M : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (C : ℝ≥0) : Prop :=
  ∀ (τ : FiniteStoppingTime F) (T : ℝ≥0), (∀ ω, τ ω ≤ T) →
    Integrable (fun ω ↦ Real.exp ((1 / 2 : ℝ) * M (τ ω) ω)) P ∧
      (∫ ω, Real.exp ((1 / 2 : ℝ) * M (τ ω) ω) ∂P) ≤ C

/-- Uniform Novikov control of the continuous bracket over bounded stopping
times.  This is the stopping-time form of Protter III.45 and avoids assigning
a finite default value to the bracket at infinity. -/
def HasNovikovBound (hM : IsContinuousLocalMartingale M F P)
    (hF : F.IsUsual P) (C : ℝ≥0) : Prop :=
  ∀ (τ : FiniteStoppingTime F) (T : ℝ≥0), (∀ ω, τ ω ≤ T) →
    Integrable (fun ω ↦ Real.exp ((1 / 2 : ℝ) *
      (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω)) P ∧
      (∫ ω, Real.exp ((1 / 2 : ℝ) *
        (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω) ∂P) ≤ C

/-- Protter III.43 converts a Novikov bracket bound into the half-exponential
bound required by Kazamaki. -/
theorem HasNovikovBound.hasKazamakiBound
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hN : HasNovikovBound hM hF C) :
    let K : ℝ≥0 := ⟨Real.sqrt (C : ℝ), Real.sqrt_nonneg _⟩
    HasKazamakiBound M F P K := by
  dsimp only
  let K : ℝ≥0 := ⟨Real.sqrt (C : ℝ), Real.sqrt_nonneg _⟩
  intro τ T hb
  obtain ⟨hqi, hqb⟩ := hN τ T hb
  obtain ⟨hhi, hhalf⟩ :=
    hM.integrable_and_integral_exp_half_stopped_le_sqrt_integral_exp_half_quadraticVariation
      hF h0 τ hb hqi
  refine ⟨hhi, hhalf.trans ?_⟩
  change Real.sqrt (∫ ω, Real.exp ((1 / 2 : ℝ) *
      (hM.isSemimartingale hF).continuousQuadraticVariation hF (τ ω) ω) ∂P) ≤
    Real.sqrt (C : ℝ)
  exact Real.sqrt_le_sqrt hqb

/-- A Kazamaki half-exponential bound controls every smaller nonnegative
exponential coefficient. -/
theorem HasKazamakiBound.integrable_exp_mul_stopped
    {C : ℝ≥0} (hK : HasKazamakiBound M F P C)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω ↦ Real.exp (c * M (τ ω) ω)) P ∧
      (∫ ω, Real.exp (c * M (τ ω) ω) ∂P) ≤ 1 + C := by
  obtain ⟨hi, hbound⟩ := hK τ T hb
  let H : Ω → ℝ := fun ω ↦ Real.exp ((1 / 2 : ℝ) * M (τ ω) ω)
  let G : Ω → ℝ := fun ω ↦ Real.exp (c * M (τ ω) ω)
  have hdom (ω : Ω) : G ω ≤ 1 + H ω := by
    have hθ0 : 0 ≤ 2 * c := mul_nonneg (by norm_num) hc0
    have hθ1 : 2 * c ≤ 1 := by linarith
    have he : G ω = H ω ^ (2 * c) := by
      dsimp only [G, H]
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [he]
    by_cases hy : H ω ≤ 1
    · exact (Real.rpow_le_one (Real.exp_pos _).le hy hθ0).trans
        (by linarith [Real.exp_pos ((1 / 2 : ℝ) * M (τ ω) ω)])
    · have hy' : 1 ≤ H ω := le_of_not_ge hy
      have hh := Real.rpow_le_rpow_of_exponent_le hy' hθ1
      rw [Real.rpow_one] at hh
      exact hh.trans (by linarith [Real.exp_pos ((1 / 2 : ℝ) * M (τ ω) ω)])
  have hGm : AEStronglyMeasurable G P := by
    have heq : G = fun ω ↦ Real.exp ((2 * c) * Real.log (H ω)) := by
      funext ω
      dsimp only [G, H]
      rw [Real.log_exp]
      congr 1
      ring
    rw [heq]
    exact ((hi.aestronglyMeasurable.aemeasurable.log.const_mul (2 * c)).exp).aestronglyMeasurable
  have hGi : Integrable G P :=
    (integrable_const (1 : ℝ)).add hi |>.mono' hGm
      (ae_of_all P fun ω ↦ by simpa [G, H] using hdom ω)
  change Integrable G P ∧ (∫ ω, G ω ∂P) ≤ 1 + C
  refine ⟨hGi, ?_⟩
  calc
    (∫ ω, G ω ∂P) ≤ ∫ ω, (1 + H ω) ∂P :=
      integral_mono hGi ((integrable_const (1 : ℝ)).add hi) hdom
    _ = 1 + ∫ ω, H ω ∂P := by
      rw [integral_add (integrable_const (1 : ℝ)) hi, integral_const, probReal_univ,
        one_smul]
    _ ≤ 1 + C := by dsimp only [H]; linarith

/-- The quantitative `L^q` estimate used in Kazamaki's criterion.  The
explicit exponents are chosen so that the second Holder factor has coefficient
`(1+a)/4 < 1/2`. -/
theorem IsContinuousLocalMartingale.integrable_stochasticExponential_const_mul_rpow_stopped
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hK : HasKazamakiBound M F P C)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    let q := (1 + a) ^ 2 / (4 * a)
    let Ea := ((hM.const_mul a).isSemimartingale hF).stochasticExponential hF
    Integrable (fun ω ↦ Ea (τ ω) ω ^ q) P ∧
      (∫ ω, Ea (τ ω) ω ^ q ∂P) ≤ (1 + C : ℝ) ^ (1 - a) := by
  dsimp only
  let q : ℝ := (1 + a) ^ 2 / (4 * a)
  let r : ℝ := 1 / a
  let s : ℝ := 1 / (1 - a)
  let b : ℝ := (1 + a) / 2
  let d : ℝ := (1 - a ^ 2) / 4
  let c : ℝ := (1 + a) / 4
  let hMa := hM.const_mul a
  let hMb := hM.const_mul b
  let Ea := (hMa.isSemimartingale hF).stochasticExponential hF
  let Eb := (hMb.isSemimartingale hF).stochasticExponential hF
  let f : Ω → ℝ := fun ω ↦ Eb (τ ω) ω ^ a
  let g : Ω → ℝ := fun ω ↦ Real.exp (d * M (τ ω) ω)
  have ha0' : 0 ≤ a := ha0.le
  have h1a : 0 < 1 - a := sub_pos.mpr ha1
  have hr : 1 < r := by
    dsimp only [r]
    exact one_lt_one_div ha0 ha1
  have hs : 1 < s := by
    dsimp only [s]
    have hle : 1 - a < 1 := by linarith
    exact one_lt_one_div h1a hle
  have hq : 1 < q := by
    dsimp only [q]
    have ha : 0 < 4 * a := mul_pos (by norm_num) ha0
    rw [lt_div_iff₀ ha]
    nlinarith [sq_pos_of_pos (sub_pos.mpr ha1)]
  have hrs : r.HolderConjugate s := by
    rw [Real.holderConjugate_iff]
    refine ⟨hr, ?_⟩
    dsimp only [r, s]
    field_simp [ha0.ne', h1a.ne']
    ring
  have hb0 : 0 < b := by dsimp only [b]; linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  have hc0 : 0 ≤ c := by dsimp only [c]; linarith
  have hc1 : c ≤ 1 / 2 := by dsimp only [c]; linarith
  have h0a : (fun t ω ↦ a * M t ω) 0 =ᵐ[P] 0 :=
    h0.mono fun _ hω ↦ by simp [hω]
  have h0b : (fun t ω ↦ b * M t ω) 0 =ᵐ[P] 0 :=
    h0.mono fun _ hω ↦ by simp [hω]
  have hEbclm := hMb.isContinuousLocalMartingale_stochasticExponential hF
  have hEbsm := hMb.supermartingale_stochasticExponential hF h0b
  have hiEb : Integrable (fun ω ↦ Eb (τ ω) ω) P :=
    hEbsm.integrable_finiteStoppingTime_value τ hb hEbclm.2.hasRightContinuousPaths
  have hmEb : Measurable (fun ω ↦ Eb (τ ω) ω) := by
    rw [← FiniteStoppingTime.stoppedValue_eq Eb τ]
    exact (hEbsm.stronglyAdapted.measurable_stoppedValue_of_usual hF
      hEbclm.2.hasRightContinuousPaths τ.isStoppingTime).mono τ.measurableSpace_le le_rfl
  have hEbpos : ∀ᵐ ω ∂P, 0 < Eb (τ ω) ω := by
    filter_upwards [(hMb.isSemimartingale hF).stochasticExponential_pos_of_continuous
      hF hMb.2] with ω hω
    exact hω (τ ω)
  have hmf : AEStronglyMeasurable f P := by
    exact ((Real.continuous_rpow_const ha0').measurable.comp hmEb).aestronglyMeasurable
  have hfr : ∀ᵐ ω ∂P, f ω ^ r = Eb (τ ω) ω := by
    filter_upwards [hEbpos] with ω hω
    dsimp only [f, r]
    rw [← Real.rpow_mul hω.le]
    have har : a * (1 / a) = 1 := by field_simp
    rw [har, Real.rpow_one]
  have hfi : Integrable (fun ω ↦ ‖f ω‖ ^ r) P := by
    apply hiEb.congr
    filter_upwards [hfr, hEbpos] with ω hω hpos
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le a)]
    exact hω.symm
  have hfLp : MemLp f (ENNReal.ofReal r) P :=
    memLp_of_integrable_norm_rpow (lt_trans zero_lt_one hr) hmf hfi
  obtain ⟨hic, hcbound⟩ := hK.integrable_exp_mul_stopped hc0 hc1 τ T hb
  have hmg : AEStronglyMeasurable g P := by
    have heq : g = fun ω ↦ Real.exp ((4 * d) * Real.log
        (Real.exp ((1 / 4 : ℝ) * M (τ ω) ω))) := by
      funext ω
      dsimp only [g]
      rw [Real.log_exp]
      congr 1
      ring
    rw [heq]
    have hiQuarter := hK.integrable_exp_mul_stopped (c := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num) τ T hb |>.1
    have hmQuarter : AEMeasurable
        (fun ω ↦ Real.exp ((4 * d) * Real.log
          (Real.exp ((1 / 4 : ℝ) * M (τ ω) ω)))) P :=
      (hiQuarter.aestronglyMeasurable.aemeasurable.log.const_mul (4 * d)).exp
    exact hmQuarter.aestronglyMeasurable
  have hgs : ∀ ω, g ω ^ s = Real.exp (c * M (τ ω) ω) := by
    intro ω
    dsimp only [g, s, d, c]
    rw [← Real.exp_mul]
    congr 1
    field_simp [h1a.ne']
    ring
  have hgi : Integrable (fun ω ↦ ‖g ω‖ ^ s) P := by
    apply hic.congr
    exact ae_of_all P fun ω ↦ by
      calc
        Real.exp (c * M (τ ω) ω) = g ω ^ s := (hgs ω).symm
        _ = ‖g ω‖ ^ s := by
          rw [Real.norm_of_nonneg]
          dsimp only [g]
          exact (Real.exp_pos _).le
  have hgLp : MemLp g (ENNReal.ofReal s) P :=
    memLp_of_integrable_norm_rpow (lt_trans zero_lt_one hs) hmg hgi
  have hformula : ∀ᵐ ω ∂P, Ea (τ ω) ω ^ q = f ω * g ω := by
    filter_upwards [hM.stochasticExponential_const_mul_formula hF a,
      hM.stochasticExponential_const_mul_formula hF b] with ω haω hbω
    dsimp only [Ea, Eb, f, g]
    rw [haω (τ ω), hbω (τ ω), ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    dsimp only [q, b, d]
    field_simp [ha0.ne']
    ring
  have hiProd : Integrable (f * g) P := by
    letI : (ENNReal.ofReal r).HolderTriple (ENNReal.ofReal s) 1 := hrs.ennrealOfReal
    exact hfLp.integrable_mul hgLp
  have hiMoment : Integrable (fun ω ↦ Ea (τ ω) ω ^ q) P :=
    hiProd.congr (hformula.mono fun ω hω ↦ by simpa only [Pi.mul_apply] using hω.symm)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g) hrs
    (hEbpos.mono fun _ hpos ↦ Real.rpow_nonneg hpos.le _)
    (ae_of_all P fun _ ↦ (Real.exp_pos _).le)
    hfLp hgLp
  rw [← integral_congr_ae hformula] at hholder
  have hEbBound := hMb.integral_stochasticExponential_stopped_le_one hF h0b τ hb
  have hbase : 0 ≤ (1 + C : ℝ) := by positivity
  have hright :
      (∫ ω, f ω ^ r ∂P) ^ (1 / r) * (∫ ω, g ω ^ s ∂P) ^ (1 / s) ≤
        (1 + C : ℝ) ^ (1 - a) := by
    have hFint : (∫ ω, f ω ^ r ∂P) = ∫ ω, Eb (τ ω) ω ∂P :=
      integral_congr_ae hfr
    have hGint : (∫ ω, g ω ^ s ∂P) =
        ∫ ω, Real.exp (c * M (τ ω) ω) ∂P :=
      integral_congr_ae (ae_of_all P hgs)
    rw [hFint, hGint]
    have hEaNonneg : 0 ≤ ∫ ω, Eb (τ ω) ω ∂P :=
      integral_nonneg_of_ae (hEbpos.mono fun _ hpos ↦ hpos.le)
    have hEcNonneg : 0 ≤ ∫ ω, Real.exp (c * M (τ ω) ω) ∂P :=
      integral_nonneg fun _ ↦ (Real.exp_pos _).le
    have hpowF : (∫ ω, Eb (τ ω) ω ∂P) ^ (1 / r) ≤ 1 := by
      exact (Real.rpow_le_rpow hEaNonneg hEbBound (by positivity)).trans_eq (by simp)
    have hpowG : (∫ ω, Real.exp (c * M (τ ω) ω) ∂P) ^ (1 / s) ≤
        (1 + C : ℝ) ^ (1 - a) := by
      have he : 1 / s = 1 - a := by dsimp only [s]; field_simp [h1a.ne']
      rw [he]
      exact Real.rpow_le_rpow hEcNonneg hcbound h1a.le
    simpa using (mul_le_mul hpowF hpowG
      (Real.rpow_nonneg hEcNonneg _) (by positivity))
  simpa only [q, Ea, hMa] using And.intro hiMoment (hholder.trans hright)

/-- Under the Kazamaki bound, every strict contraction of the martingale has
a Class D stochastic exponential.  Arbitrary finite stopping times are reached
from their deterministic truncations inside the UI closure, rather than being
silently treated as bounded. -/
theorem IsContinuousLocalMartingale.isClassD_stochasticExponential_const_mul
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hK : HasKazamakiBound M F P C)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IsClassD (((hM.const_mul a).isSemimartingale hF).stochasticExponential hF) F P := by
  let q : ℝ := (1 + a) ^ 2 / (4 * a)
  let hMa := hM.const_mul a
  let E := (hMa.isSemimartingale hF).stochasticExponential hF
  let ρ : FiniteStoppingTime F × ℕ → FiniteStoppingTime F := fun z ↦
    z.1.min (FiniteStoppingTime.const F (z.2 : ℝ≥0))
  let V : FiniteStoppingTime F × ℕ → Ω → ℝ := fun z ω ↦ E (ρ z ω) ω
  let K : ℝ≥0 := ⟨(1 + C : ℝ) ^ (1 - a), Real.rpow_nonneg (by positivity) _⟩
  have hq : 1 < q := by
    dsimp only [q]
    have hden : 0 < 4 * a := mul_pos (by norm_num) ha0
    rw [lt_div_iff₀ hden]
    nlinarith [sq_pos_of_pos (sub_pos.mpr ha1)]
  have hρbound (z : FiniteStoppingTime F × ℕ) (ω : Ω) : ρ z ω ≤ (z.2 : ℝ≥0) := by
    simpa only [ρ, FiniteStoppingTime.min_apply, FiniteStoppingTime.const_apply] using
      (min_le_right (z.1 ω) (z.2 : ℝ≥0))
  have hmoment (z : FiniteStoppingTime F × ℕ) :
      Integrable (fun ω ↦ V z ω ^ q) P ∧
        integral P (fun ω ↦ V z ω ^ q) ≤ (K : ℝ) := by
    have h := hM.integrable_stochasticExponential_const_mul_rpow_stopped hF h0 hK
      ha0 ha1 (ρ z) (z.2 : ℝ≥0) (hρbound z)
    refine ⟨by simpa only [q, V, E, hMa] using h.1, ?_⟩
    change integral P (fun ω ↦ V z ω ^ q) ≤ (1 + C : ℝ) ^ (1 - a)
    simpa only [q, V, E, hMa] using h.2
  have hpos (z : FiniteStoppingTime F × ℕ) : ∀ᵐ ω ∂P, 0 < V z ω := by
    filter_upwards [(hMa.isSemimartingale hF).stochasticExponential_pos_of_continuous
      hF hMa.2] with ω hω
    exact hω (ρ z ω)
  have hiNorm (z : FiniteStoppingTime F × ℕ) :
      Integrable (fun ω ↦ ‖V z ω‖ ^ q) P := by
    exact (hmoment z).1.congr ((hpos z).mono fun _ hω ↦ by
      change V z _ ^ q = ‖V z _‖ ^ q
      rw [Real.norm_of_nonneg hω.le])
  have hbNorm (z : FiniteStoppingTime F × ℕ) :
      integral P (fun ω ↦ ‖V z ω‖ ^ q) ≤ (K : ℝ) := by
    have heq : (fun ω ↦ ‖V z ω‖ ^ q) =ᵐ[P] fun ω ↦ V z ω ^ q :=
      (hpos z).mono fun ω hω ↦ by
        change ‖V z ω‖ ^ q = V z ω ^ q
        rw [Real.norm_of_nonneg hω.le]
    rw [integral_congr_ae heq]
    exact (hmoment z).2
  have h0a : (fun t ω ↦ a * M t ω) 0 =ᵐ[P] 0 :=
    h0.mono fun _ hω ↦ by simp [hω]
  have hEclm := hMa.isContinuousLocalMartingale_stochasticExponential hF
  have hEsm := hMa.supermartingale_stochasticExponential hF h0a
  have hmV (z : FiniteStoppingTime F × ℕ) : Measurable (V z) := by
    change Measurable (fun ω ↦ E (ρ z ω) ω)
    rw [← FiniteStoppingTime.stoppedValue_eq E (ρ z)]
    exact (hEsm.stronglyAdapted.measurable_stoppedValue_of_usual hF
      hEclm.2.hasRightContinuousPaths (ρ z).isStoppingTime).mono
        (ρ z).measurableSpace_le le_rfl
  have hVui : UniformIntegrable V 1 P :=
    uniformIntegrable_of_bounded_integral_norm_rpow hq
      (fun z ↦ (hmV z).aestronglyMeasurable) hiNorm K hbNorm
  let L := {g : Ω → ℝ | ∃ e : ℕ → FiniteStoppingTime F × ℕ,
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ V (e n) ω) atTop (𝓝 (g ω))}
  have hL : UniformIntegrable (fun g : L ↦ g.1) 1 P :=
    hVui.uniformIntegrable_of_ae_tendsto atTop
  have hlim (τ : FiniteStoppingTime F) :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ V (τ, n) ω) atTop (𝓝 (E (τ ω) ω)) := by
    apply ae_of_all
    intro ω
    obtain ⟨N, hN⟩ := exists_nat_ge (τ ω)
    refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
    intro n hn
    change E (Min.min (τ ω) (n : ℝ≥0)) ω = E (τ ω) ω
    rw [min_eq_left]
    exact hN.trans (Nat.cast_le.mpr hn)
  let e : FiniteStoppingTime F → L := fun τ ↦
    ⟨fun ω ↦ E (τ ω) ω, fun n ↦ (τ, n), hlim τ⟩
  change UniformIntegrable (fun τ : FiniteStoppingTime F ↦ fun ω ↦ E (τ ω) ω) 1 P
  exact hL.reindex e

/-- Kazamaki's strict-contraction conclusion: the stochastic exponential of
`a M`, `0 < a < 1`, is a uniformly integrable martingale. -/
theorem IsContinuousLocalMartingale.isUIMartingale_stochasticExponential_const_mul
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hK : HasKazamakiBound M F P C)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IsUIMartingale (((hM.const_mul a).isSemimartingale hF).stochasticExponential hF) F P := by
  apply ((hM.const_mul a).isContinuousLocalMartingale_stochasticExponential hF).1
    |>.isUIMartingale_of_classD
  exact hM.isClassD_stochasticExponential_const_mul hF h0 hK ha0 ha1

end ProbabilityTheory

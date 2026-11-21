/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Equation
public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Product
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Integral
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralAlgebra
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Jump
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ConstantIntegrator
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Associativity
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts
public import StochLean.Analysis.PathVariation.CumulativeProductPureJump
public import StochLean.Analysis.PathVariation.CumulativeJumpSeries
public import StochLean.Analysis.PathVariation.CadlagCompositionBounds
public import StochLean.Analysis.PathVariation.CadlagC2JumpSeries

/-! # Protter II.37: uniqueness of the stochastic-exponential equation

The proof does not divide by the stochastic exponential of the original
integrator: that process can be killed by a jump of size `-1`.  Instead the
homogeneous equation is multiplied by the stochastic exponential driven by
`-X + [X]`.  Its jump multiplier is

`1 - ΔX + (ΔX)²`,

which is strictly positive.  Integration by parts and associativity reduce the
result to a left Stieltjes equation driven by the pure-jump finite-variation
process with jumps `(ΔX)³`.

The deterministic lemma below proves uniqueness for such a pure-jump equation.
Its weighted norm uses the cumulative product of `1 + |ΔA|`.  This treats
infinite jump activity and accumulation at zero directly; no first-jump
argument and no hidden local-finiteness assumption are used.
-/

@[expose] public section

open MeasureTheory Filter Set Function StochLean ProbabilityTheory
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 3000000

namespace StochLean

private theorem leftVolterra_improve_bound
    {a w G q b : ℝ≥0 → ℝ} (T : ℝ≥0) (B : ℝ)
    (heq : ∀ t : ℝ≥0, w t = ∑' s : Ioc 0 t, leftLim w s * a s)
    (hqPath : IsCadlagPath q)
    (hq_eq : ∀ t : ℝ≥0, q t = |w t| / G t)
    (hGpos : ∀ t : ℝ≥0, 0 < G t)
    (hGone : ∀ t : ℝ≥0, 1 ≤ G t)
    (hleftGpos : ∀ {s : ℝ≥0}, 0 < s → 0 < leftLim G s)
    (hleftq_eq : ∀ {s : ℝ≥0}, 0 < s →
      leftLim q s = |leftLim w s| / leftLim G s)
    (hbdef : ∀ s : ℝ≥0, b s = leftLim G s * |a s|)
    (hb0 : ∀ s : ℝ≥0, 0 ≤ b s)
    (hb : ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦ b s))
    (hGrep : ∀ t : ℝ≥0, G t - 1 = ∑' s : Ioc 0 t, b s)
    (hGmono : Monotone G) (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ≥0, t ≤ T → q t ≤ B) :
    ∀ t : ℝ≥0, t ≤ T → q t ≤ B * (1 - 1 / G T) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hempty : Ioc (0 : ℝ≥0) 0 = ∅ := by simp
    have hzero : (∑' s : Ioc (0 : ℝ≥0) 0, leftLim w s * a s) = 0 := by
      rw [hempty]
      simp
    rw [hq_eq 0, heq 0, hzero]
    simp only [abs_zero, zero_div]
    exact mul_nonneg hB0 (sub_nonneg.mpr ((div_le_one (hGpos T)).2 (hGone T)))
  have hleft (s : Ioc 0 t) : |leftLim w s| ≤ B * leftLim G s := by
    have hql : leftLim q s ≤ B := by
      let : (nhdsWithin (s : ℝ≥0) (Iio s)).NeBot :=
        nhdsLT_neBot_of_exists_lt ⟨0, s.2.1⟩
      apply le_of_tendsto (tendsto_leftLim_of_tendsto (hqPath.2 s s.2.1.ne'))
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hB u ((show u < s from hu).le.trans (s.2.2.trans ht))
    rw [hleftq_eq s.2.1] at hql
    exact (div_le_iff₀ (hleftGpos s.2.1)).mp hql
  have hsum : Summable (fun s : Ioc 0 t ↦ leftLim w s * a s) := by
    apply ((hb t).mul_left (max B 1)).of_norm_bounded
    intro s
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      |leftLim w s| * |a s| ≤ (B * leftLim G s) * |a s| :=
        mul_le_mul_of_nonneg_right (hleft s) (abs_nonneg _)
      _ = B * (leftLim G s * |a s|) := by ring
      _ = B * b s := by rw [hbdef s]
      _ ≤ (max B 1) * b s := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hb0 s)
  have hnorm : |w t| ≤ B * (G t - 1) := by
    rw [heq t]
    calc
      |∑' s : Ioc 0 t, leftLim w s * a s| ≤
          ∑' s : Ioc 0 t, |leftLim w s * a s| := by
            simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' s : Ioc 0 t, B * b s := by
        apply Summable.tsum_le_tsum
        · intro s
          simp only [abs_mul]
          calc
            |leftLim w s| * |a s| ≤ (B * leftLim G s) * |a s| :=
              mul_le_mul_of_nonneg_right (hleft s) (abs_nonneg _)
            _ = B * (leftLim G s * |a s|) := by ring
            _ = B * b s := by rw [hbdef s]
        · exact hsum.abs
        · exact (hb t).mul_left B
      _ = B * ∑' s : Ioc 0 t, b s := tsum_mul_left
      _ = B * (G t - 1) := by rw [← hGrep t]
  rw [hq_eq]
  have hratio : |w t| / G t ≤ B * (1 - 1 / G t) := by
    apply (div_le_iff₀ (hGpos t)).2
    calc
      |w t| ≤ B * (G t - 1) := hnorm
      _ = (B * (1 - 1 / G t)) * G t := by
        field_simp [(hGpos t).ne']
  apply hratio.trans
  apply mul_le_mul_of_nonneg_left _ hB0
  have hGt : G t ≤ G T := hGmono ht
  have hinv : 1 / G T ≤ 1 / G t := one_div_le_one_div_of_le (hGpos t) hGt
  linarith

private theorem leftVolterra_zero_at_of_weight
    {a w G q b : ℝ≥0 → ℝ} (T : ℝ≥0)
    (heq : ∀ t : ℝ≥0, w t = ∑' s : Ioc 0 t, leftLim w s * a s)
    (hqPath : IsCadlagPath q)
    (hq_eq : ∀ t : ℝ≥0, q t = |w t| / G t)
    (hq0 : ∀ t : ℝ≥0, 0 ≤ q t)
    (hGpos : ∀ t : ℝ≥0, 0 < G t)
    (hGone : ∀ t : ℝ≥0, 1 ≤ G t)
    (hleftGpos : ∀ {s : ℝ≥0}, 0 < s → 0 < leftLim G s)
    (hleftq_eq : ∀ {s : ℝ≥0}, 0 < s →
      leftLim q s = |leftLim w s| / leftLim G s)
    (hbdef : ∀ s : ℝ≥0, b s = leftLim G s * |a s|)
    (hb0 : ∀ s : ℝ≥0, 0 ≤ b s)
    (hb : ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦ b s))
    (hGrep : ∀ t : ℝ≥0, G t - 1 = ∑' s : Ioc 0 t, b s)
    (hGmono : Monotone G) : w T = 0 := by
  let ρ : ℝ := 1 - 1 / G T
  have hρ0 : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one (hGpos T)).2 (hGone T))
  have hρone : ρ < 1 := by
    dsimp only [ρ]
    have : 0 < 1 / G T := one_div_pos.mpr (hGpos T)
    linarith
  have habsρ : |ρ| < 1 := by
    rw [abs_of_nonneg hρ0]
    exact hρone
  obtain ⟨C, hC0, hC⟩ := hqPath.exists_norm_bound_Icc T
  have hCbound (t : ℝ≥0) (ht : t ≤ T) : q t ≤ C := by
    exact (le_abs_self (q t)).trans (by
      simpa only [Real.norm_eq_abs] using hC t ⟨bot_le, ht⟩)
  have hpow (n : ℕ) : ∀ t : ℝ≥0, t ≤ T → q t ≤ C * ρ ^ n := by
    induction n with
    | zero => simpa only [pow_zero, mul_one] using hCbound
    | succ n ih =>
        simpa only [ρ, pow_succ, mul_assoc] using
          leftVolterra_improve_bound T (C * ρ ^ n) heq hqPath hq_eq hGpos hGone
            hleftGpos hleftq_eq hbdef hb0 hb hGrep hGmono
            (mul_nonneg hC0 (pow_nonneg hρ0 n)) ih
  have hlim : Tendsto (fun n : ℕ ↦ C * ρ ^ n) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habsρ)
  have hqTzero : q T = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
        (fun n ↦ hpow n T le_rfl)
    · exact hq0 T
  rw [hq_eq T] at hqTzero
  exact abs_eq_zero.mp
    ((div_eq_zero_iff.mp hqTzero).resolve_right (hGpos T).ne')

private noncomputable def leftVolterraWeight (a : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∏' s : Ioc 0 t, (1 + |a s|)

private noncomputable def leftVolterraCoefficient (a : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  leftLim (leftVolterraWeight a) s * |a s|

private noncomputable def leftVolterraInvClip (x : ℝ) : ℝ := (max x 1)⁻¹

private noncomputable def leftVolterraNormalized
    (w G : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  |w t| * leftVolterraInvClip (G t)

private theorem leftVolterraWeight_deviation_summable {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    (t : ℝ≥0) : Summable (fun s : Ioc 0 t ↦ |(1 + |a s|) - 1|) := by
  simpa only [add_sub_cancel_left, abs_abs] using ha t

private theorem leftVolterraWeight_cadlag {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|)) :
    IsCadlagPath (leftVolterraWeight a) := by
  change IsCadlagPath (fun t : ℝ≥0 ↦
    ∏' s : Ioc 0 t, ((1 : ℝ) + |a s|))
  exact isCadlagPath_tprod_Ioc
    (f := fun s : ℝ≥0 ↦ (1 : ℝ) + |a s|)
    (leftVolterraWeight_deviation_summable ha)

private theorem leftVolterraWeight_one_le {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    (t : ℝ≥0) :
    1 ≤ leftVolterraWeight a t := by
  change 1 ≤ ∏' s : Ioc 0 t, ((1 : ℝ) + |a s|)
  have hm : Multipliable (fun s : Ioc 0 t ↦ (1 : ℝ) + |a s|) :=
    Real.multipliable_one_add_of_summable (ha t)
  exact le_hasProd_of_le_prod hm.hasProd fun u ↦
    Finset.one_le_prod fun i _ ↦ by nlinarith only [abs_nonneg (a i)]

private theorem leftVolterraWeight_left_one_le {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    {s : ℝ≥0} (hs : 0 < s) : 1 ≤ leftLim (leftVolterraWeight a) s := by
  let : (nhdsWithin s (Iio s)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  exact ge_of_tendsto'
    (tendsto_leftLim_of_tendsto ((leftVolterraWeight_cadlag ha).2 s hs.ne'))
    (fun u ↦ leftVolterraWeight_one_le ha u)

private theorem leftVolterraCoefficient_nonneg {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    (s : ℝ≥0) : 0 ≤ leftVolterraCoefficient a s := by
  by_cases hs : s = 0
  · subst s
    rw [leftVolterraCoefficient,
      leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
    exact mul_nonneg
      (zero_le_one.trans (leftVolterraWeight_one_le ha 0)) (abs_nonneg _)
  · exact mul_nonneg
      (le_trans zero_le_one
        (leftVolterraWeight_left_one_le ha (pos_iff_ne_zero.mpr hs)))
      (abs_nonneg _)

private theorem leftVolterraCoefficient_summable {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    (t : ℝ≥0) :
    Summable (fun s : Ioc 0 t ↦ leftVolterraCoefficient a s) := by
  obtain ⟨C, hC0, hC⟩ := exists_compact_pair_bound_of_cadlag
    (leftVolterraWeight_cadlag ha) t (Φ := fun x _ ↦ x) continuous_fst
  apply ((ha t).mul_left C).of_norm_bounded
  intro s
  simp only [leftVolterraCoefficient, Real.norm_eq_abs, abs_mul, abs_abs]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [Real.norm_eq_abs] using hC s ⟨s.2.1.le, s.2.2⟩) (abs_nonneg _)

private theorem leftVolterraWeight_representation {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    (t : ℝ≥0) :
    leftVolterraWeight a t - 1 =
      ∑' s : Ioc 0 t, leftVolterraCoefficient a s := by
  change (∏' s : Ioc 0 t, ((1 : ℝ) + |a s|)) - 1 =
    ∑' s : Ioc 0 t,
      leftLim (fun v : ℝ≥0 ↦
        ∏' u : Ioc 0 v, ((1 : ℝ) + |a u|)) s * |a s|
  simpa only [add_sub_cancel_left] using
    tprod_Ioc_sub_one_eq_tsum_left_mul_deviation
      (f := fun s : ℝ≥0 ↦ (1 : ℝ) + |a s|)
      (leftVolterraWeight_deviation_summable ha) t

private theorem leftVolterraWeight_monotone {a : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|)) :
    Monotone (leftVolterraWeight a) := by
  intro s t hst
  have hs : leftVolterraWeight a s =
      1 + ∑' u : Ioc 0 s, leftVolterraCoefficient a u := by
    linarith only [leftVolterraWeight_representation ha s]
  have ht : leftVolterraWeight a t =
      1 + ∑' u : Ioc 0 t, leftVolterraCoefficient a u := by
    linarith only [leftVolterraWeight_representation ha t]
  rw [hs, ht]
  simpa only [add_comm] using add_le_add_left
    (monotone_tsum_Ioc_of_nonneg
      (leftVolterraCoefficient_summable ha) (leftVolterraCoefficient_nonneg ha) hst) 1

private theorem continuous_leftVolterraInvClip :
    Continuous leftVolterraInvClip := by
  have hmax : Continuous (fun x : ℝ ↦ max x 1) :=
    continuous_id.max continuous_const
  have h := hmax.inv₀
    (fun x : ℝ ↦ (zero_lt_one.trans_le (le_max_right x 1)).ne')
  change Continuous (fun x : ℝ ↦ (max x 1)⁻¹)
  exact h

private theorem leftVolterraNormalized_cadlag {w G : ℝ≥0 → ℝ}
    (hw : IsCadlagPath w) (hG : IsCadlagPath G) :
    IsCadlagPath (leftVolterraNormalized w G) := by
  exact (hw.continuous_comp continuous_abs).mul
    (hG.continuous_comp continuous_leftVolterraInvClip)

private theorem leftVolterraNormalized_eq {w G : ℝ≥0 → ℝ}
    (hGone : ∀ t : ℝ≥0, 1 ≤ G t) (t : ℝ≥0) :
    leftVolterraNormalized w G t = |w t| / G t := by
  simp only [leftVolterraNormalized, leftVolterraInvClip,
    max_eq_left (hGone t), div_eq_mul_inv]

private theorem leftVolterraNormalized_nonneg {w G : ℝ≥0 → ℝ}
    (hGone : ∀ t : ℝ≥0, 1 ≤ G t) (t : ℝ≥0) :
    0 ≤ leftVolterraNormalized w G t := by
  rw [leftVolterraNormalized_eq hGone]
  exact div_nonneg (abs_nonneg _) (zero_lt_one.trans_le (hGone t)).le

private theorem leftVolterraNormalized_left_eq {w G : ℝ≥0 → ℝ}
    (hw : IsCadlagPath w) (hG : IsCadlagPath G)
    (hleftGone : ∀ {s : ℝ≥0}, 0 < s → 1 ≤ leftLim G s)
    {s : ℝ≥0} (hs : 0 < s) :
    leftLim (leftVolterraNormalized w G) s =
      |leftLim w s| / leftLim G s := by
  let : (nhdsWithin s (Iio s)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  apply leftLim_eq_of_tendsto
  change Tendsto (fun u ↦ |w u| * leftVolterraInvClip (G u))
    (nhdsWithin s (Iio s)) (nhds (|leftLim w s| / leftLim G s))
  have hwlim := tendsto_leftLim_of_tendsto (hw.2 s hs.ne')
  have hGlim := tendsto_leftLim_of_tendsto (hG.2 s hs.ne')
  have hmax : max (leftLim G s) 1 = leftLim G s := max_eq_left (hleftGone hs)
  simpa only [leftVolterraInvClip, hmax,
    div_eq_mul_inv] using hwlim.abs.mul
      ((hGlim.max tendsto_const_nhds).inv₀
        (show max (leftLim G s) 1 ≠ 0 by positivity))

/-- A homogeneous left Volterra equation driven by a locally absolutely
summable jump family has only the zero cadlag solution.

The proof uses the weight `G(t) = ∏_{s≤t}(1+|a_s|)`.  If `|w|/G` is
bounded by `B` on `[0,T]`, the equation and the product expansion improve the
bound to `B ρ`, where `ρ = 1 - 1/G(T) < 1`.  Iteration sends the bound to
zero. -/
theorem eq_zero_of_eq_tsum_leftLim_mul
    {a w : ℝ≥0 → ℝ}
    (ha : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |a s|))
    (hw : IsCadlagPath w)
    (heq : ∀ t : ℝ≥0, w t = ∑' s : Ioc 0 t, leftLim w s * a s) :
    w = 0 := by
  funext T
  let G := leftVolterraWeight a
  let b := leftVolterraCoefficient a
  have hG : IsCadlagPath G := leftVolterraWeight_cadlag ha
  have hGone (t : ℝ≥0) : 1 ≤ G t := leftVolterraWeight_one_le ha t
  have hleftGone {s : ℝ≥0} (hs : 0 < s) : 1 ≤ leftLim G s :=
    leftVolterraWeight_left_one_le ha hs
  have hGpos (t : ℝ≥0) : 0 < G t := zero_lt_one.trans_le (hGone t)
  have hleftGpos {s : ℝ≥0} (hs : 0 < s) : 0 < leftLim G s :=
    zero_lt_one.trans_le (hleftGone hs)
  have hbdef (s : ℝ≥0) : b s = leftLim G s * |a s| := rfl
  exact leftVolterra_zero_at_of_weight T heq
    (leftVolterraNormalized_cadlag hw hG) (leftVolterraNormalized_eq hGone)
    (leftVolterraNormalized_nonneg hGone) hGpos hGone hleftGpos
    (leftVolterraNormalized_left_eq hw hG hleftGone) hbdef
    (leftVolterraCoefficient_nonneg ha) (leftVolterraCoefficient_summable ha)
    (leftVolterraWeight_representation ha) (leftVolterraWeight_monotone ha)

end StochLean

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
  {X D Z : ℝ≥0 → Ω → ℝ}

/-- The integrating-factor driver used in the uniqueness proof. -/
private noncomputable def stochasticExponentialUniquenessDriver
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  (fun t ω ↦ (-1 : ℝ) * X t ω) + hX.quadraticVariation hF

omit [SigmaFiniteFiltration P F] in
/-- The auxiliary exponential never vanishes.  The argument is valid for
arbitrary jumps because `1-u+u²` has negative discriminant. -/
private theorem IsSemimartingale.stochasticExponential_uniquenessDriver_ne_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    let hQ := hX.isSemimartingale_quadraticVariation hF
    let hY := (hX.const_mul (-1)).add hQ
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, hY.stochasticExponential hF t ω ≠ 0 := by
  dsimp only
  let Q := hX.quadraticVariation hF
  let hQ := hX.isSemimartingale_quadraticVariation hF
  let Y := stochasticExponentialUniquenessDriver hX hF
  let hY : IsSemimartingale Y F P := (hX.const_mul (-1)).add hQ
  filter_upwards [hY.stochasticExponential_ne_zero_iff hF, hX.hasCadlagPaths,
    hQ.hasCadlagPaths, hX.jumpProcess_quadraticVariation hF] with ω hne hx hq hj t
  apply (hne t).2
  intro s
  let N : ℝ≥0 → Ω → ℝ := fun u v ↦ (-1 : ℝ) * X u v
  have hn : IsCadlagPath (N · ω) := by
    change IsCadlagPath (fun u ↦ (-1 : ℝ) * X u ω)
    exact hx.continuous_comp (continuous_const.mul continuous_id)
  have hjY := hn.jumpProcess_add hq s
  change jumpProcess Y s ω =
    jumpProcess N s ω + jumpProcess Q s ω at hjY
  have hjN := hx.jumpProcess_const_mul (-1) s
  change jumpProcess N s ω = (-1 : ℝ) * jumpProcess X s ω at hjN
  have hjQ := hj s
  change jumpProcess Q s ω = (jumpProcess X s ω) ^ 2 at hjQ
  rw [hjY, hjN, hjQ]
  intro hbad
  have hsq : 0 ≤ (jumpProcess X s ω - (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
  nlinarith

omit [SigmaFiniteFiltration P F] in
/-- The homogeneous stochastic equation

`D = D_- · X`

has only the zero adapted cadlag semimartingale solution.  This is the
full-jump statement: no condition is imposed on the jumps of `X`, and in
particular jumps of size `-1` are allowed. -/
theorem IsSemimartingale.indistinguishable_zero_of_eq_stochasticIntegral_leftLimit
    (hX : IsSemimartingale X F P) (hD : IsSemimartingale D F P)
    (hF : F.IsUsual P) (hX0 : X 0 =ᵐ[P] 0)
    (hDeq : Indistinguishable D
      (hX.stochasticIntegral hF
        (hD.adapted.leftLimitProcess_of_usual hF hD.hasCadlagPaths)
        hD.hasCadlagPaths.hasCagladPaths_leftLimitProcess) P) :
    Indistinguishable D 0 P := by
  let DL := leftLimitProcess D
  let haDL : Adapted F DL :=
    hD.adapted.leftLimitProcess_of_usual hF hD.hasCadlagPaths
  let hrDL : HasCagladPaths DL P :=
    hD.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let U := hX.stochasticIntegral hF haDL hrDL
  let hU : IsSemimartingale U F P :=
    hX.isSemimartingale_stochasticIntegral hF haDL hrDL
  let Q := hX.quadraticVariation hF
  let hQ : IsSemimartingale Q F P := hX.isSemimartingale_quadraticVariation hF
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ (-1 : ℝ) * X t ω
  let hN : IsSemimartingale N F P := hX.const_mul (-1)
  let Y := N + Q
  let hY : IsSemimartingale Y F P := hN.add hQ
  have hY0 : Y 0 =ᵐ[P] 0 := by
    filter_upwards [hX0, hX.quadraticVariation_zero_ae hF] with ω hx hq
    dsimp only [Y, N, Q]
    simp only [Pi.add_apply, hx, hq, Pi.zero_apply]
    ring
  let S := hY.stochasticExponential hF
  let hS : IsSemimartingale S F P := hY.isSemimartingale_stochasticExponential hF
  let SL := leftLimitProcess S
  let haSL : Adapted F SL :=
    hS.adapted.leftLimitProcess_of_usual hF hS.hasCadlagPaths
  let hrSL : HasCagladPaths SL P :=
    hS.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let V := hY.stochasticIntegral hF haSL hrSL
  let hV : IsSemimartingale V F P :=
    hY.isSemimartingale_stochasticIntegral hF haSL hrSL
  let C : ℝ≥0 → Ω → ℝ := fun _ _ ↦ 1
  let hC : IsSemimartingale C F P :=
    isSemimartingale_const_initial (F := F) (P := P) measurable_const
  let R := S - C
  let hR : IsSemimartingale R F P := hS.sub hC
  let RL := leftLimitProcess R
  let haRL : Adapted F RL :=
    hR.adapted.leftLimitProcess_of_usual hF hR.hasCadlagPaths
  let hrRL : HasCagladPaths RL P :=
    hR.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let H := DL * SL
  let haH : Adapted F H := fun t ↦ (haDL t).mul (haSL t)
  let hrH : HasCagladPaths H P := hrDL.mul hrSL
  let B := hX.quadraticCovariation (hN.add hQ) hF
  let hB : IsSemimartingale B F P :=
    hX.isSemimartingale_quadraticCovariation (hN.add hQ) hF
  let K := X + Y + B
  let hK : IsSemimartingale K F P := (hX.add hY).add hB
  let W := D * S
  let hW : IsSemimartingale W F P := hD.mul hS hF
  let WL := leftLimitProcess W
  let haWL : Adapted F WL :=
    hW.adapted.leftLimitProcess_of_usual hF hW.hasCadlagPaths
  let hrWL : HasCagladPaths WL P :=
    hW.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have heR : Indistinguishable R V P := by
    filter_upwards [hY.stochasticExponential_sub_initial_eq_integral hF, hY0]
      with ω he hy t
    change S t ω - C t ω = V t ω
    simpa only [C, hy, Pi.zero_apply, Real.exp_zero] using he t
  have heH : Indistinguishable (DL + RL * DL) H P := by
    filter_upwards [hS.hasCadlagPaths] with ω hs t
    by_cases ht : t = 0
    · subst t
      simp only [DL, RL, SL, H, leftLimitProcess_zero, Pi.zero_apply,
        Pi.add_apply, Pi.mul_apply, zero_mul, add_zero]
    · have hcCont : IsContinuousPath (C · ω) := continuous_const
      have hc : IsCadlagPath (C · ω) := hcCont.isCadlagPath
      have hr := hs.leftLimitProcess_sub hc t
      change leftLimitProcess R t ω =
        leftLimitProcess S t ω - leftLimitProcess C t ω at hr
      change leftLimitProcess D t ω +
          leftLimitProcess R t ω * leftLimitProcess D t ω =
        leftLimitProcess D t ω * leftLimitProcess S t ω
      rw [hr, hcCont.leftLimitProcess_eq ht]
      simp only [C]
      ring
  let JR := hR.stochasticIntegral hF haDL hrDL
  let JD := hD.stochasticIntegral hF haRL hrRL
  let BR := hD.quadraticCovariation hR hF
  let IY := hY.stochasticIntegral hF haH hrH
  let JX := hX.stochasticIntegral hF
    (fun t ↦ (haRL t).mul (haDL t)) (hrRL.mul hrDL)
  let IX := hX.stochasticIntegral hF haH hrH
  let IB := hB.stochasticIntegral hF haH hrH
  let IXY := (hX.add hY).stochasticIntegral hF haH hrH
  let IK := hK.stochasticIntegral hF haH hrH
  have heJR : Indistinguishable JR IY P :=
    (hR.stochasticIntegral_congr_integrator hV hF haDL hrDL heR).trans
      (hY.stochasticIntegral_stochasticIntegral hF haDL hrDL haSL hrSL)
  have heJD : Indistinguishable JD JX P :=
    (hD.stochasticIntegral_congr_integrator hU hF haRL hrRL hDeq).trans
      (hX.stochasticIntegral_stochasticIntegral hF haRL hrRL haDL hrDL)
  have heBR : Indistinguishable BR IB P :=
    (hD.quadraticCovariation_congr hR hU hV hF hDeq heR).trans
      (hX.quadraticCovariation_stochasticIntegral_both hY hF
        haDL hrDL haSL hrSL)
  have heX : Indistinguishable (U + JX) IX P :=
    (hX.stochasticIntegral_add hF haDL hrDL
      (fun t ↦ (haRL t).mul (haDL t)) (hrRL.mul hrDL)).symm.trans
        (hX.stochasticIntegral_congr_integrand hF
          (fun t ↦ (haDL t).add ((haRL t).mul (haDL t)))
          (hrDL.add (hrRL.mul hrDL)) haH hrH heH)
  have heK : Indistinguishable (IX + IY + IB) IK P := by
    have hXY : Indistinguishable IXY (IX + IY) P :=
      hX.stochasticIntegral_add_integrator hY hF haH hrH
    have hKB : Indistinguishable IK (IXY + IB) P :=
      (hX.add hY).stochasticIntegral_add_integrator hB hF haH hrH
    filter_upwards [hXY, hKB] with ω hxy hkb t
    calc
      (IX + IY + IB) t ω = (IX t ω + IY t ω) + IB t ω := by rfl
      _ = IXY t ω + IB t ω := congrArg (fun z ↦ z + IB t ω) (hxy t).symm
      _ = IK t ω := (hkb t).symm
  have heW : Indistinguishable W IK P := by
    filter_upwards [hDeq, hD.integrationByParts hR hF, heJR, heJD, heBR, heX, heK]
      with ω hd hp hyr hyd hbr hx hk t
    change ∀ u, D u ω = U u ω at hd
    change ∀ u, D u ω * R u ω = JR u ω + JD u ω + BR u ω at hp
    change ∀ u, JR u ω = IY u ω at hyr
    change ∀ u, JD u ω = JX u ω at hyd
    change ∀ u, BR u ω = IB u ω at hbr
    change ∀ u, U u ω + JX u ω = IX u ω at hx
    change ∀ u, IX u ω + IY u ω + IB u ω = IK u ω at hk
    change D t ω * S t ω = IK t ω
    calc
      D t ω * S t ω = D t ω + D t ω * R t ω := by
        dsimp only [R, C]
        simp only [Pi.sub_apply]
        ring
      _ = U t ω + (JR t ω + JD t ω + BR t ω) := by rw [hp t, hd t]
      _ = (U t ω + JX t ω) + IY t ω + IB t ω := by
        rw [hyr t, hyd t, hbr t]
        ring
      _ = IX t ω + IY t ω + IB t ω := by rw [hx t]
      _ = IK t ω := hk t
  let A := hX.quadraticCovariation hQ hF
  have heKA : Indistinguishable K A P := by
    filter_upwards [hX.quadraticCovariation_add_right hN hQ hF,
      hX.quadraticCovariation_const_mul_right hX hF (-1),
      hX.quadraticCovariation_self hF] with ω hadd hneg hself t
    have hadd' : B t ω = hX.quadraticCovariation hN hF t ω + A t ω := by
      simpa only [B, A, Pi.add_apply] using hadd t
    have hneg' : hX.quadraticCovariation hN hF t ω =
        (-1 : ℝ) * hX.quadraticCovariation hX hF t ω := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hneg t
    have hself' : hX.quadraticCovariation hX hF t ω = Q t ω := by
      simpa only [Q] using hself t
    change X t ω + Y t ω + B t ω = A t ω
    rw [hadd', hneg', hself']
    dsimp only [Y, N]
    simp only [Pi.add_apply]
    ring
  have hvQ := hX.hasFiniteVariationPaths_quadraticVariation hF
  have hvA := hX.hasFiniteVariationPaths_quadraticCovariation hQ hF
  have hvK : HasFiniteVariationPaths K P := HasFiniteVariationPaths.congr heKA.symm hvA
  have hpureA := hX.quadraticCovariation_of_finiteVariation_right hQ hF hvQ
  have hjQ := hX.jumpProcess_quadraticVariation hF
  have hpureK : Indistinguishable K
      (fun t ω ↦ ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 3) P := by
    filter_upwards [heKA, hpureA, hjQ, hX0] with ω hka ha hj hz t
    have ha' : A t ω = X 0 ω * Q 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Q s ω := by
      simpa only [A, Q] using ha t
    have hj' (s : ℝ≥0) : jumpProcess Q s ω = (jumpProcess X s ω) ^ 2 := by
      simpa only [Q] using hj s
    calc
      K t ω = A t ω := hka t
      _ = X 0 ω * Q 0 ω +
          ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Q s ω := ha'
      _ = ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 3 := by
        simp only [hz, Pi.zero_apply, zero_mul, zero_add]
        apply tsum_congr
        intro s
        rw [hj' s]
        ring
  have habs : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Ioc 0 T ↦ |(jumpProcess X s ω) ^ 3|) := by
    filter_upwards [hX.hasCadlagPaths, hX.summable_sq_jumps hF] with ω hx hs T
    have hcont : Continuous
        (fun p : ℝ × ℝ ↦ (fun a b : ℝ ↦ b - a) p.1 p.2) :=
      continuous_snd.sub continuous_fst
    have hs' : Summable
        (fun s : Ioc 0 T ↦ (X s ω - leftLim (X · ω) s) ^ 2) := by
      apply (hs T).congr
      intro s
      simp only [jumpProcess, Pi.sub_apply, leftLimitProcess,
        if_neg (ne_of_gt s.2.1)]
    have hsum0 := summable_abs_pair_weighted_sq_jumps hx hs'
      (Φ := fun a b : ℝ ↦ b - a) hcont
    apply hsum0.congr
    intro s
    have hj : X s ω - leftLim (X · ω) s = jumpProcess X s ω := by
      change X s ω - leftLim (X · ω) s = X s ω - leftLimitProcess X s ω
      rw [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
    rw [hj]
    ring_nf
  have hjumpK : Indistinguishable (jumpProcess K)
      (fun t ω ↦ (jumpProcess X t ω) ^ 3) P := by
    filter_upwards [heKA.jumpProcess,
      hX.jumpProcess_quadraticCovariation hQ hF,
      hX.jumpProcess_quadraticVariation hF] with ω hk ha hq t
    have hk' : jumpProcess K t ω = jumpProcess A t ω := hk t
    have ha' : jumpProcess A t ω =
        jumpProcess X t ω * jumpProcess Q t ω := by
      simpa only [A, Q] using ha t
    have hq' : jumpProcess Q t ω = (jumpProcess X t ω) ^ 2 := hq t
    calc
      jumpProcess K t ω = jumpProcess A t ω := hk'
      _ = jumpProcess X t ω * jumpProcess Q t ω := ha'
      _ = (jumpProcess X t ω) ^ 3 := by rw [hq']; ring
  have hK0 : K 0 =ᵐ[P] 0 := by
    filter_upwards [hpureK] with ω hp
    change K 0 ω = (0 : ℝ)
    simpa using hp 0
  have hpureJumpK : ∀ᵐ ω ∂P, ∀ t,
      K t ω - K 0 ω = ∑' s : Ioc 0 t, jumpProcess K s ω := by
    filter_upwards [hpureK, hK0, hjumpK] with ω hp hk hj t
    change K 0 ω = (0 : ℝ) at hk
    calc
      K t ω - K 0 ω =
          (∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 3) - 0 := by rw [hp t, hk]
      _ = ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 3 := sub_zero _
      _ = ∑' s : Ioc 0 t, jumpProcess K s ω := by
        apply tsum_congr
        intro s
        exact (hj s).symm
  have heHL : Indistinguishable H WL P := by
    change Indistinguishable (leftLimitProcess D * leftLimitProcess S)
      (leftLimitProcess (D * S)) P
    exact (hD.hasCadlagPaths.leftLimitProcess_mul hS.hasCadlagPaths).symm
  have heWWL : Indistinguishable W (hK.stochasticIntegral hF haWL hrWL) P :=
    heW.trans (hK.stochasticIntegral_congr_integrand hF
      haH hrH haWL hrWL heHL)
  have hIpure := hK.stochasticIntegral_of_pureJump_finiteVariation
    hF hvK hpureJumpK haWL hrWL
  have hWzero : Indistinguishable W 0 P := by
    filter_upwards [heWWL, hIpure, hjumpK, hW.hasCadlagPaths, habs]
      with ω hwi hip hj hw hs
    have heq (t : ℝ≥0) : W t ω =
        ∑' s : Ioc 0 t, Function.leftLim (W · ω) s * (jumpProcess X s ω) ^ 3 := by
      rw [hwi t, hip t]
      simp only [WL, leftLimitProcess_zero, Pi.zero_apply, zero_mul, zero_add]
      apply tsum_congr
      intro s
      rw [hj s]
      simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
    have hz := StochLean.eq_zero_of_eq_tsum_leftLim_mul
      (a := fun s ↦ (jumpProcess X s ω) ^ 3) hs hw heq
    intro t
    exact congrFun hz t
  have hSne := hX.stochasticExponential_uniquenessDriver_ne_zero hF
  change ∀ᵐ ω ∂P, ∀ t, S t ω ≠ 0 at hSne
  filter_upwards [hWzero, hSne] with ω hw hs t
  have hm : D t ω * S t ω = 0 := by
    have hwt := hw t
    change D t ω * S t ω = (0 : ℝ) at hwt
    exact hwt
  exact (mul_eq_zero.mp hm).resolve_right (hs t)

omit [SigmaFiniteFiltration P F] in
/-- Protter II.37, uniqueness part.  An adapted cadlag semimartingale satisfying
the unit-initial left-integrand equation is indistinguishable from the
product-defined stochastic exponential.

The explicit initial-value hypothesis records the usual formulation of the
theorem.  With the source convention `Z_(0-) = 0`, it also follows from the
displayed equation and `X₀ = 0`. -/
theorem IsSemimartingale.stochasticExponential_unique
    (hX : IsSemimartingale X F P) (hZ : IsSemimartingale Z F P)
    (hF : F.IsUsual P) (hX0 : X 0 =ᵐ[P] 0) (hZ0 : Z 0 =ᵐ[P] 1)
    (hZeq : Indistinguishable Z
      (fun t ω ↦ 1 + hX.stochasticIntegral hF
        (hZ.adapted.leftLimitProcess_of_usual hF hZ.hasCadlagPaths)
        hZ.hasCadlagPaths.hasCagladPaths_leftLimitProcess t ω) P) :
    Indistinguishable Z (hX.stochasticExponential hF) P := by
  let E := hX.stochasticExponential hF
  let hE : IsSemimartingale E F P := hX.isSemimartingale_stochasticExponential hF
  let ZL := leftLimitProcess Z
  let haZL : Adapted F ZL :=
    hZ.adapted.leftLimitProcess_of_usual hF hZ.hasCadlagPaths
  let hrZL : HasCagladPaths ZL P :=
    hZ.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let EL := leftLimitProcess E
  let haEL : Adapted F EL :=
    hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths
  let hrEL : HasCagladPaths EL P :=
    hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let IZ := hX.stochasticIntegral hF haZL hrZL
  let IE := hX.stochasticIntegral hF haEL hrEL
  let D := Z - E
  let hD : IsSemimartingale D F P := hZ.sub hE
  let DL := leftLimitProcess D
  let haDL : Adapted F DL :=
    hD.adapted.leftLimitProcess_of_usual hF hD.hasCadlagPaths
  let hrDL : HasCagladPaths DL P :=
    hD.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let ZmEL := ZL - EL
  let haZmEL : Adapted F ZmEL := fun t ↦ (haZL t).sub (haEL t)
  let hrZmEL : HasCagladPaths ZmEL P := hrZL.sub hrEL
  have hleft : Indistinguishable DL ZmEL P := by
    filter_upwards [hZ.hasCadlagPaths, hE.hasCadlagPaths] with ω hz he t
    exact hz.leftLimitProcess_sub he t
  have hDdiff : Indistinguishable D (IZ - IE) P := by
    filter_upwards [hZeq, hX.stochasticExponential_eq_one_add_integral hF hX0]
      with ω hz he t
    change ∀ u, Z u ω = 1 + IZ u ω at hz
    change ∀ u, E u ω = 1 + IE u ω at he
    change Z t ω - E t ω = IZ t ω - IE t ω
    rw [hz t, he t]
    ring
  have hIDdiff : Indistinguishable
      (hX.stochasticIntegral hF haDL hrDL) (IZ - IE) P :=
    (hX.stochasticIntegral_congr_integrand hF
      haDL hrDL haZmEL hrZmEL hleft).trans
        (hX.stochasticIntegral_sub hF haZL hrZL haEL hrEL)
  have hDeq : Indistinguishable D (hX.stochasticIntegral hF haDL hrDL) P :=
    hDdiff.trans hIDdiff.symm
  have hDzero :=
    hX.indistinguishable_zero_of_eq_stochasticIntegral_leftLimit hD hF hX0 hDeq
  filter_upwards [hDzero, hZ0] with ω hd _ t
  exact sub_eq_zero.mp (hd t)

end ProbabilityTheory

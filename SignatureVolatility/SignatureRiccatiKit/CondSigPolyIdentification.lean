module

public import SignatureVolatility.SignatureRiccatiKit.CondSigPoly
public import SignatureVolatility.SignatureRiccatiKit.ItoWordTiltClosedForm
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ProlongedBrownianSetup.StratItoCoeffBounds
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# C2c. Identification of `paperSig2` with `condSigPoly` under the complex tilt
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma countOnes_le_length {d : ℕ} (hd : 0 < d) :
    ∀ J : Word (d + 1), countOnes hd J ≤ J.length
  | [] => le_rfl
  | j :: J => by
    have := countOnes_le_length hd J
    simp only [countOnes, List.length_cons]
    split_ifs <;> omega

private lemma ofReal_list_sum (L : List ℝ) : ((L.sum : ℂ) = (L.map fun x => (x : ℂ)).sum) := by
  induction L with
  | nil => simp
  | cons x L ih => simp [Complex.ofReal_add, ih]

private lemma list_sum_mul (L : List ℂ) (c : ℂ) : L.sum * c = (L.map (fun x => x * c)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [add_mul, ih]

private lemma integrable_exp_mul_abs_gaussianReal (c : ℝ) {μ : ℝ} {v : ℝ≥0} :
    Integrable (fun x : ℝ => Real.exp (c * |x|)) (gaussianReal μ v) := by
  refine ((integrable_exp_mul_gaussianReal (μ := μ) (v := v) c).add
      (integrable_exp_mul_gaussianReal (μ := μ) (v := v) (-c))).mono'
    (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Pi.add_apply]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

private lemma integrable_ofReal_pow_gaussianReal (m : ℕ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x : ℂ) ^ m) (gaussianReal 0 v) := by
  have hbd : Integrable (fun x : ℝ => |x| ^ m) (gaussianReal 0 v) := by
    have hLp : MemLp (id : ℝ → ℝ) (m : ℝ≥0∞) (gaussianReal 0 v) :=
      memLp_id_gaussianReal' (μ := 0) (v := v) (m : ℝ≥0∞) (ENNReal.natCast_ne_top m)
    have hint := hLp.integrable_norm_rpow'
    simpa [Real.norm_eq_abs, ENNReal.toReal_natCast] using hint
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ m) (gaussianReal 0 v) :=
    (Complex.continuous_ofReal.pow m).aestronglyMeasurable
  refine Integrable.mono' hbd hmeas (ae_of_all _ fun x => ?_)
  simp [Complex.norm_real, Real.norm_eq_abs, norm_pow]

private lemma integrable_monicHermite_gaussianReal (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ => monicHermite k t (x : ℂ))
      (gaussianReal 0 (Real.toNNReal t)) := by
  simp_rw [monicHermite_eq_sum]
  refine integrable_finsetSum _ fun m _ => ?_
  have hx := integrable_ofReal_pow_gaussianReal (k - m) t.toNNReal
  convert hx.const_mul ((k.choose m : ℂ) * (I * (Real.sqrt t : ℂ)) ^ m *
      ∫ y : ℝ, (y : ℂ) ^ m ∂gaussianReal 0 1) using 1
  funext (x : ℝ)
  ring

/-- `‖exp(i ξ x + ξ² t / 2)‖ = exp(ξ² t / 2)`. -/
private lemma norm_exp_real_tilt (ξ t x : ℝ) :
    ‖Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))‖ =
      Real.exp (ξ ^ 2 * t / 2) := by
  rw [Complex.norm_exp]
  have h0 : (Complex.I * (ξ : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have h1 : (((ξ ^ 2 * t / 2 : ℝ) : ℂ)).re = ξ ^ 2 * t / 2 := Complex.ofReal_re _
  rw [Complex.add_re, h0, h1, zero_add]

private lemma iteratedDeriv_exp_mul_const (c : ℂ) (k : ℕ) (r : ℂ) :
    iteratedDeriv k (fun ρ : ℂ => Complex.exp (ρ * c)) r = c ^ k * Complex.exp (r * c) := by
  have hfun : ∀ n : ℕ, iteratedDeriv n (fun ρ : ℂ => Complex.exp (ρ * c)) =
      fun ρ => c ^ n * Complex.exp (ρ * c) := by
    intro n
    induction n with
    | zero => ext ρ; simp
    | succ n ih =>
      ext ρ
      rw [iteratedDeriv_succ, ih]
      have h1 : HasDerivAt (fun σ : ℂ => σ * c) c ρ := by
        simpa using (hasDerivAt_id ρ).mul_const c
      have h2 : HasDerivAt (fun σ : ℂ => c ^ n * Complex.exp (σ * c))
          (c ^ n * (Complex.exp (ρ * c) * c)) ρ :=
        h1.cexp.const_mul (c ^ n)
      have h3 : c ^ n * (Complex.exp (ρ * c) * c) = c ^ (n + 1) * Complex.exp (ρ * c) := by
        ring
      rw [h2.deriv, h3]
  exact congrArg (fun f => f r) (hfun k)

/-- Generating function of the tilted monic-Hermite integrand, in closed form. -/
private lemma integral_cexp_tilt_prod (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) (ρ : ℂ) :
    ∫ p : ℝ × ℝ,
        Complex.exp (ρ * ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)) +
          Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
      ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)) =
      Complex.exp (ρ * (Complex.I * (ξ : ℂ) * (t : ℂ))) := by
  set Z : ℝ × ℝ → ℂ :=
    fun p => (p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)
  set μ := (gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)
  have hfun : (fun p : ℝ × ℝ =>
        Complex.exp (ρ * Z p + Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))) =
      fun p =>
        (Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))) *
          Complex.exp ((ρ * Complex.I * (Real.sqrt t : ℂ)) * (p.2 : ℂ)) := by
    funext p
    have hz : ρ * Z p + Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ) =
        ((ρ + Complex.I * (ξ : ℂ)) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)) +
          (ρ * Complex.I * (Real.sqrt t : ℂ)) * (p.2 : ℂ) := by
      simp [Z]; ring
    rw [hz, Complex.exp_add]
  rw [hfun]
  set fX : ℝ → ℂ := fun x =>
    Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
  set gY : ℝ → ℂ := fun y =>
    Complex.exp ((ρ * Complex.I * (Real.sqrt t : ℂ)) * (y : ℂ))
  have hfX : Integrable fX (gaussianReal 0 (Real.toNNReal t)) := by
    have hsplit : fX = fun x : ℝ =>
        Complex.exp ((ξ ^ 2 * t / 2 : ℝ) : ℂ) *
          Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ)) := by
      funext (x : ℝ); dsimp [fX]; rw [Complex.exp_add, mul_comm]
    rw [hsplit]
    have hnorm : Integrable (fun x : ℝ => Real.exp ((ρ + Complex.I * (ξ : ℂ)).re * x))
        (gaussianReal 0 (Real.toNNReal t)) :=
      integrable_exp_mul_gaussianReal _
    have hcexp : Integrable
        (fun x : ℝ => Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ)))
        (gaussianReal 0 (Real.toNNReal t)) := by
      refine hnorm.mono' (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      have hx : ‖Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ))‖ =
          Real.exp ((ρ + Complex.I * (ξ : ℂ)).re * x) := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      simp [hx, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact hcexp.const_mul _
  have hgY : Integrable gY (gaussianReal 0 1) := by
    have hnorm : Integrable (fun y : ℝ => Real.exp ((ρ * Complex.I * (Real.sqrt t : ℂ)).re * y))
        (gaussianReal 0 1) :=
      integrable_exp_mul_gaussianReal _
    refine hnorm.mono' (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    have hy : ‖gY y‖ = Real.exp ((ρ * Complex.I * (Real.sqrt t : ℂ)).re * y) := by
      dsimp [gY]
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [hy, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hprod : Integrable (fun p : ℝ × ℝ => fX p.1 * gY p.2)
      ((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)) :=
    hfX.mul_prod hgY
  have hchange : (fun p : ℝ × ℝ =>
        Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)) *
          Complex.exp ((ρ * Complex.I * (Real.sqrt t : ℂ)) * (p.2 : ℂ))) =
      fun p => fX p.1 * gY p.2 := rfl
  rw [hchange, integral_prod _ hprod]
  have hinter : ∀ x : ℝ, ∫ y : ℝ, fX x * gY y ∂gaussianReal 0 1 =
      fX x * ∫ y : ℝ, gY y ∂gaussianReal 0 1 :=
    fun x => integral_const_mul (fX x) gY
  simp_rw [hinter, integral_mul_const]
  have hY : ∫ y : ℝ, Complex.exp ((ρ * Complex.I * (Real.sqrt t : ℂ)) * (y : ℂ))
      ∂gaussianReal 0 1 =
      complexMGF id (gaussianReal 0 1) (ρ * Complex.I * (Real.sqrt t : ℂ)) := by
    simp [complexMGF]
  have hX : ∫ x : ℝ, Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
      ∂(gaussianReal 0 (Real.toNNReal t)) =
      Complex.exp ((ξ ^ 2 * t / 2 : ℝ) : ℂ) *
        complexMGF id (gaussianReal 0 (Real.toNNReal t)) (ρ + Complex.I * (ξ : ℂ)) := by
    have hsplit : (fun x : ℝ =>
        Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))) =
        fun x : ℝ => Complex.exp ((ξ ^ 2 * t / 2 : ℝ) : ℂ) *
          Complex.exp ((ρ + Complex.I * (ξ : ℂ)) * (x : ℂ)) := by
      funext (x : ℝ); rw [Complex.exp_add, mul_comm]
    rw [hsplit, integral_const_mul]
    simp [complexMGF]
  rw [hX, hY, complexMGF_id_gaussianReal, complexMGF_id_gaussianReal]
  have hv : ((Real.toNNReal t : ℝ) : ℂ) = (t : ℂ) := by
    rw [Real.coe_toNNReal t ht]
  have hsqrt : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hexp :
      (ξ : ℂ) ^ 2 * (t : ℂ) / 2 +
        ((max t 0 : ℝ) : ℂ) * (ρ + Complex.I * (ξ : ℂ)) ^ 2 / 2 +
        (ρ * Complex.I * (Real.sqrt t : ℂ)) ^ 2 / 2 =
      ρ * (Complex.I * (ξ : ℂ) * (t : ℂ)) := by
    rw [max_eq_left ht]
    push_cast
    ring_nf
    rw [hI2, hsqrt]
    ring
  -- Collapse the product of exponentials, then equate the exponents.
  -- Last printed goal was `cexp A = cexp B` with `hexp : A = B` syntactically matching.
  simp [mul_zero, add_zero, zero_add, zero_mul, Complex.ofReal_zero, ← Complex.exp_add]
  exact congrArg Complex.exp hexp

/-- Tilted counterpart of `iteratedDeriv_integral_cexp_gaussianReal_prod`. -/
private lemma iteratedDeriv_integral_cexp_tilt (j : ℕ) (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv j (fun r : ℂ =>
      ∫ p : ℝ × ℝ,
        Complex.exp (r * ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)) +
          Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
          ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1))) 0 =
      ∫ p : ℝ × ℝ,
        ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)) ^ j *
          Complex.exp (Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
          ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)) := by
  set μ := (gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)
  set Z : ℝ × ℝ → ℂ :=
    fun p => (p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)
  set E : ℝ × ℝ → ℂ :=
    fun p => Complex.exp (Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
  have hnormZ : ∀ p, ‖Z p‖ ≤ |p.1| + Real.sqrt t * |p.2| := fun p => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    simp [Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
  have hnormE : ∀ p, ‖E p‖ = Real.exp (ξ ^ 2 * t / 2) := fun p => norm_exp_real_tilt ξ t p.1
  have hInt_exp : ∀ R : ℝ, 0 ≤ R → Integrable (fun p : ℝ × ℝ => Real.exp (R * ‖Z p‖)) μ :=
    fun R hR => by
      have h1 : Integrable (fun x : ℝ => Real.exp (R * |x|))
          (gaussianReal 0 (Real.toNNReal t)) :=
        integrable_exp_mul_abs_gaussianReal R
      have h2 : Integrable (fun y : ℝ => Real.exp (R * Real.sqrt t * |y|))
          (gaussianReal 0 1) :=
        integrable_exp_mul_abs_gaussianReal (R * Real.sqrt t)
      refine (h1.mul_prod h2).mono' (by fun_prop : Continuous _).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      calc R * ‖Z p‖
          ≤ R * (|p.1| + Real.sqrt t * |p.2|) :=
            mul_le_mul_of_nonneg_left (hnormZ p) hR
        _ = R * |p.1| + (R * Real.sqrt t) * |p.2| := by ring
  have hpow_le : ∀ (n : ℕ) (p : ℝ × ℝ),
      ‖Z p‖ ^ n ≤ (n.factorial : ℝ) * Real.exp (‖Z p‖) := fun n p => by
    have hx := Real.pow_div_factorial_le_exp (x := ‖Z p‖) (norm_nonneg (Z p)) n
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
    rw [div_le_iff₀ hfac] at hx
    linarith
  have hInt : ∀ (k : ℕ) (ρ : ℂ),
      Integrable (fun p : ℝ × ℝ => Z p ^ k * Complex.exp (ρ * Z p) * E p) μ := fun k ρ => by
    have hI : Integrable (fun p : ℝ × ℝ =>
        (k.factorial : ℝ) * Real.exp ((‖ρ‖ + 1) * ‖Z p‖) * Real.exp (ξ ^ 2 * t / 2)) μ := by
      convert (((hInt_exp (‖ρ‖ + 1) (by positivity)).const_mul (k.factorial : ℝ)).const_mul
          (Real.exp (ξ ^ 2 * t / 2))) using 1
      funext p; ring
    refine hI.mono' (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    calc ‖Z p ^ k * Complex.exp (ρ * Z p) * E p‖
        = ‖Z p‖ ^ k * ‖Complex.exp (ρ * Z p)‖ * ‖E p‖ := by
          rw [norm_mul, norm_mul, norm_pow]
      _ = ‖Z p‖ ^ k * Real.exp (ρ * Z p).re * Real.exp (ξ ^ 2 * t / 2) := by
          rw [Complex.norm_exp, hnormE]
      _ ≤ ‖Z p‖ ^ k * Real.exp (‖ρ * Z p‖) * Real.exp (ξ ^ 2 * t / 2) := by
          gcongr; exact Complex.re_le_norm _
      _ = ‖Z p‖ ^ k * Real.exp (‖ρ‖ * ‖Z p‖) * Real.exp (ξ ^ 2 * t / 2) := by
          rw [norm_mul]
      _ ≤ (k.factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp (‖ρ‖ * ‖Z p‖) *
            Real.exp (ξ ^ 2 * t / 2) := by
          gcongr; exact hpow_le k p
      _ = (k.factorial : ℝ) * Real.exp ((‖ρ‖ + 1) * ‖Z p‖) * Real.exp (ξ ^ 2 * t / 2) := by
          rw [mul_assoc (k.factorial : ℝ), ← Real.exp_add]; ring_nf
  have hderiv : ∀ (k : ℕ) (r : ℂ),
      HasDerivAt (fun ρ : ℂ => ∫ p : ℝ × ℝ, Z p ^ k * Complex.exp (ρ * Z p) * E p ∂μ)
        (∫ p : ℝ × ℝ, Z p ^ (k + 1) * Complex.exp (r * Z p) * E p ∂μ) r := fun k r => by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (ρ : ℂ) (p : ℝ × ℝ) => Z p ^ k * Complex.exp (ρ * Z p) * E p)
      (F' := fun (ρ : ℂ) (p : ℝ × ℝ) => Z p ^ (k + 1) * Complex.exp (ρ * Z p) * E p)
      (bound := fun p => (k + 1).factorial * Real.exp ((‖r‖ + 2) * ‖Z p‖) *
        Real.exp (ξ ^ 2 * t / 2))
      (s := Metric.ball r 1) (x₀ := r) (Metric.ball_mem_nhds r one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun ρ => (by fun_prop : Continuous _).aestronglyMeasurable
    · exact hInt k r
    · exact (hInt (k + 1) r).aestronglyMeasurable
    · refine ae_of_all _ fun p ρ hρ => ?_
      have hρbd : ‖ρ‖ ≤ ‖r‖ + 1 := by
        have hdist : ‖ρ - r‖ < 1 := by
          simpa [dist_eq_norm] using (Metric.mem_ball.mp hρ)
        calc ‖ρ‖ = ‖(ρ - r) + r‖ := by simp
          _ ≤ ‖ρ - r‖ + ‖r‖ := norm_add_le _ _
          _ ≤ 1 + ‖r‖ := by linarith [le_of_lt hdist]
          _ = ‖r‖ + 1 := by ring
      calc ‖Z p ^ (k + 1) * Complex.exp (ρ * Z p) * E p‖
          = ‖Z p‖ ^ (k + 1) * Real.exp (ρ * Z p).re * ‖E p‖ := by
            rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
        _ = ‖Z p‖ ^ (k + 1) * Real.exp (ρ * Z p).re * Real.exp (ξ ^ 2 * t / 2) := by
            rw [hnormE]
        _ ≤ ‖Z p‖ ^ (k + 1) * Real.exp (‖ρ * Z p‖) * Real.exp (ξ ^ 2 * t / 2) := by
            gcongr; exact Complex.re_le_norm _
        _ = ‖Z p‖ ^ (k + 1) * Real.exp (‖ρ‖ * ‖Z p‖) * Real.exp (ξ ^ 2 * t / 2) := by
            rw [norm_mul]
        _ ≤ ((k + 1).factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp (‖ρ‖ * ‖Z p‖) *
              Real.exp (ξ ^ 2 * t / 2) := by
            gcongr
            exact hpow_le (k + 1) p
        _ ≤ ((k + 1).factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp ((‖r‖ + 1) * ‖Z p‖) *
              Real.exp (ξ ^ 2 * t / 2) := by
            gcongr
        _ = (k + 1).factorial * Real.exp ((‖r‖ + 2) * ‖Z p‖) *
              Real.exp (ξ ^ 2 * t / 2) := by
            rw [mul_assoc ((k + 1).factorial : ℝ), ← Real.exp_add]; ring_nf
    · convert ((hInt_exp (‖r‖ + 2) (by positivity)).const_mul
          ((k + 1).factorial : ℝ)).const_mul (Real.exp (ξ ^ 2 * t / 2)) using 1
      funext p; ring
    · refine ae_of_all _ fun p ρ _ => ?_
      have h1 : HasDerivAt (fun ρ : ℂ => ρ * Z p) (Z p) ρ := by
        simpa using (hasDerivAt_id ρ).mul_const (Z p)
      have h2 : HasDerivAt (fun ρ : ℂ => Complex.exp (ρ * Z p))
          (Complex.exp (ρ * Z p) * Z p) ρ := h1.cexp
      have hmul : HasDerivAt (fun ρ : ℂ => Z p ^ k * Complex.exp (ρ * Z p) * E p)
          (Z p ^ k * (Complex.exp (ρ * Z p) * Z p) * E p) ρ :=
        (h2.const_mul (Z p ^ k)).mul_const (E p)
      convert hmul using 1
      ring
  have hgen : ∀ (k j : ℕ) (r : ℂ),
      iteratedDeriv j (fun ρ : ℂ => ∫ p : ℝ × ℝ, Z p ^ k * Complex.exp (ρ * Z p) * E p ∂μ) r =
        ∫ p : ℝ × ℝ, Z p ^ (k + j) * Complex.exp (r * Z p) * E p ∂μ := by
    intro k j
    induction j generalizing k with
    | zero =>
      intro r
      simp [iteratedDeriv_zero]
    | succ j ih =>
      intro r
      rw [iteratedDeriv_succ']
      have hder : deriv (fun ρ : ℂ => ∫ p : ℝ × ℝ, Z p ^ k * Complex.exp (ρ * Z p) * E p ∂μ) =
          fun ρ => ∫ p : ℝ × ℝ, Z p ^ (k + 1) * Complex.exp (ρ * Z p) * E p ∂μ :=
        funext fun ρ => (hderiv k ρ).deriv
      rw [hder, ih (k + 1) r]
      simp [add_assoc, add_comm, add_left_comm]
  have h0 := hgen 0 j 0
  simp only [zero_add, pow_zero, one_mul, zero_mul, Complex.exp_zero] at h0
  -- Restate the generating function in additive-exponent form.
  have hfun : (fun r : ℂ => ∫ p : ℝ × ℝ, Complex.exp (r * Z p) * E p ∂μ) =
      fun r => ∫ p : ℝ × ℝ,
        Complex.exp (r * Z p + Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)) ∂μ := by
    funext r
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [E]
    rw [← Complex.exp_add]
    ac_rfl
  rw [hfun] at h0
  simpa [μ, Z, E] using h0

private lemma integral_monicHermite_mul_complexTilt (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    ∫ x : ℝ, monicHermite k t (x : ℂ) *
        Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
      ∂(gaussianReal 0 (Real.toNNReal t)) =
      (Complex.I * (ξ : ℂ) * (t : ℂ)) ^ k := by
  set μ := (gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)
  set Z : ℝ × ℝ → ℂ :=
    fun p => (p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)
  set E : ℝ → ℂ :=
    fun x => Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
  have hInt : Integrable (fun p : ℝ × ℝ => Z p ^ k * E p.1) μ := by
    -- reuse the domination from the derivative lemma at ρ = 0
    have h1 : Integrable (fun x : ℝ => Real.exp ((1 : ℝ) * |x|))
        (gaussianReal 0 (Real.toNNReal t)) :=
      integrable_exp_mul_abs_gaussianReal 1
    have h2 : Integrable (fun y : ℝ => Real.exp (Real.sqrt t * |y|))
        (gaussianReal 0 1) :=
      integrable_exp_mul_abs_gaussianReal (Real.sqrt t)
    have hExp : Integrable (fun p : ℝ × ℝ => Real.exp (‖Z p‖)) μ := by
      refine (h1.mul_prod h2).mono' (by fun_prop : Continuous _).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hnormZ : ‖Z p‖ ≤ |p.1| + Real.sqrt t * |p.2| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        simp [Z, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      simpa [one_mul] using hnormZ
    have hpow_le : ∀ p, ‖Z p‖ ^ k ≤ (k.factorial : ℝ) * Real.exp (‖Z p‖) := fun p => by
      have hx := Real.pow_div_factorial_le_exp (x := ‖Z p‖) (norm_nonneg (Z p)) k
      have hfac : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
      rw [div_le_iff₀ hfac] at hx
      linarith
    have hI : Integrable (fun p : ℝ × ℝ =>
        (k.factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp (ξ ^ 2 * t / 2)) μ := by
      convert ((hExp.const_mul (k.factorial : ℝ)).const_mul (Real.exp (ξ ^ 2 * t / 2))) using 1
      funext p; ring
    refine hI.mono' (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    calc ‖Z p ^ k * E p.1‖
        = ‖Z p‖ ^ k * ‖E p.1‖ := by rw [norm_mul, norm_pow]
      _ = ‖Z p‖ ^ k * Real.exp (ξ ^ 2 * t / 2) := by rw [norm_exp_real_tilt]
      _ ≤ (k.factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp (ξ ^ 2 * t / 2) := by
          gcongr; exact hpow_le p
  have hFub : ∫ x : ℝ, monicHermite k t (x : ℂ) * E x ∂(gaussianReal 0 (Real.toNNReal t)) =
      ∫ p : ℝ × ℝ, Z p ^ k * E p.1 ∂μ := by
    have hinter (x : ℝ) :
        Integrable (fun y : ℝ => Z (x, y) ^ k) (gaussianReal 0 1) := by
      simpa [Z] using integrable_monicHermite_integrand k t (x : ℂ)
    have hinner (x : ℝ) :
        ∫ y : ℝ, Z (x, y) ^ k * E x ∂gaussianReal 0 1 =
          monicHermite k t (x : ℂ) * E x := by
      rw [integral_mul_const, monicHermite]
    rw [integral_prod _ hInt]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simpa [mul_comm] using (hinner x).symm
  have hid := iteratedDeriv_integral_cexp_tilt k ξ ht
  have hclosed := funext fun r : ℂ => integral_cexp_tilt_prod ξ ht r
  have hder : iteratedDeriv k (fun r : ℂ => Complex.exp (r * (Complex.I * (ξ : ℂ) * (t : ℂ)))) 0 =
      (Complex.I * (ξ : ℂ) * (t : ℂ)) ^ k * Complex.exp (0 * (Complex.I * (ξ : ℂ) * (t : ℂ))) :=
    iteratedDeriv_exp_mul_const (Complex.I * (ξ : ℂ) * (t : ℂ)) k 0
  simp only [zero_mul, Complex.exp_zero, mul_one] at hder
  calc ∫ x : ℝ, monicHermite k t (x : ℂ) * E x ∂(gaussianReal 0 (Real.toNNReal t))
      = ∫ p : ℝ × ℝ, Z p ^ k * E p.1 ∂μ := hFub
    _ = iteratedDeriv k (fun r : ℂ =>
          ∫ p : ℝ × ℝ,
            Complex.exp (r * ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)) +
              Complex.I * (ξ : ℂ) * (p.1 : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)) ∂μ) 0 := by
        simpa [μ, Z, E] using hid.symm
    _ = iteratedDeriv k (fun r : ℂ => Complex.exp (r * (Complex.I * (ξ : ℂ) * (t : ℂ)))) 0 := by
        rw [hclosed]
    _ = (Complex.I * (ξ : ℂ) * (t : ℂ)) ^ k := hder

lemma integral_paperSig2_eq_condSigPoly {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (I : Word (d + 1)) (ξ : ℝ) :
    ∫ ω, ((paperSig2 B 0 t ω).coeff I : ℂ) * complexTilt B hd ξ t ω ∂P =
      ∫ ω, condSigPoly hd t I (MultiBrownian.W B t ω ⟨0, hd⟩) *
        complexTilt B hd ξ t ω ∂P := by
  set E_bd : ℝ := Real.exp (ξ ^ 2 * t / 2)
  have hLHS_list : ∀ L : List (ℝ × Word (d + 1)),
      Integrable (fun ω => (L.map fun p => (p.1 : ℂ) *
          ((itoWordIntegral B 0 t ω p.2 : ℂ) * complexTilt B hd ξ t ω)).sum) P ∧
      ∫ ω, (L.map fun p => (p.1 : ℂ) *
          ((itoWordIntegral B 0 t ω p.2 : ℂ) * complexTilt B hd ξ t ω)).sum ∂P =
        (L.map fun p =>
          if onlyZeroOrOne hd p.2 then
            (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ (countOnes hd p.2) *
              ((t ^ p.2.length / (p.2.length.factorial : ℝ) : ℝ) : ℂ)
          else 0).sum := by
    intro L
    induction L with
    | nil => simp [integrable_zero]
    | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      have hintX : Integrable (fun ω => (itoWordIntegral B 0 t ω p.2 : ℂ)) P :=
        Integrable.ofReal ((memLp_itoWordIntegral B ht p.2 le_rfl).integrable (by norm_num))
      have hp : Integrable (fun ω => (p.1 : ℂ) *
          ((itoWordIntegral B 0 t ω p.2 : ℂ) * complexTilt B hd ξ t ω)) P :=
        (hintX.mul_bdd (measurable_complexTilt B hd ξ t).aestronglyMeasurable
          (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B hd ξ t ω))).const_mul _
      refine ⟨hp.add ih.1, ?_⟩
      rw [integral_add hp ih.1, integral_const_mul,
        integral_itoWordIntegral_mul_complexTilt B hd ξ p.2 ht, ih.2]
      split_ifs <;> ring
  have hLHS : ∫ ω, ((paperSig2 B 0 t ω).coeff I : ℂ) * complexTilt B hd ξ t ω ∂P =
      ((contractions I.reverse).map fun p =>
        if onlyZeroOrOne hd p.2 then
          (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ (countOnes hd p.2) *
            ((t ^ p.2.length / (p.2.length.factorial : ℝ) : ℝ) : ℂ)
        else 0).sum := by
    have hpt : (fun ω => ((paperSig2 B 0 t ω).coeff I : ℂ) * complexTilt B hd ξ t ω) =
        fun ω => ((contractions I.reverse).map fun p =>
          (p.1 : ℂ) * ((itoWordIntegral B 0 t ω p.2 : ℂ) * complexTilt B hd ξ t ω)).sum := by
      funext ω
      rw [paperSig2_coeff, stratWordIntegral_eq_list]
      induction (contractions I.reverse) with
      | nil => simp
      | cons p Lp ih =>
        simp [Complex.ofReal_add, Complex.ofReal_mul, add_mul, mul_assoc, ih]
    rw [hpt]
    exact (hLHS_list (contractions I.reverse)).2
  have hlaw : HasLaw (fun ω => MultiBrownian.W B t ω ⟨0, hd⟩)
      (gaussianReal 0 (Real.toNNReal t)) P := by
    simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using hasLaw_wnnIncr B ⟨0, hd⟩ le_rfl ht
  have hRHS_list : ∀ L : List (ℝ × Word (d + 1)),
      Integrable (fun x : ℝ => (L.map fun p =>
          if onlyZeroOrOne hd p.2 then
            (p.1 : ℂ) * ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) *
              hermitePoly (countOnes hd p.2) t x
          else 0).sum *
          Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)))
        (gaussianReal 0 (Real.toNNReal t)) ∧
      ∫ x : ℝ, (L.map fun p =>
          if onlyZeroOrOne hd p.2 then
            (p.1 : ℂ) * ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) *
              hermitePoly (countOnes hd p.2) t x
          else 0).sum *
          Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))
        ∂(gaussianReal 0 (Real.toNNReal t)) =
      (L.map fun p =>
        if onlyZeroOrOne hd p.2 then
          (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ (countOnes hd p.2) *
            ((t ^ p.2.length / (p.2.length.factorial : ℝ) : ℝ) : ℂ)
        else 0).sum := by
    intro L
    induction L with
    | nil => simp [integrable_zero]
    | cons p L ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      have hp_int : Integrable (fun x : ℝ =>
          (if onlyZeroOrOne hd p.2 then
            (p.1 : ℂ) * ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) *
              hermitePoly (countOnes hd p.2) t x
          else 0) *
          Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)))
          (gaussianReal 0 (Real.toNNReal t)) := by
        split_ifs
        · have hH : Integrable (fun x : ℝ => hermitePoly (countOnes hd p.2) t (x : ℂ))
              (gaussianReal 0 (Real.toNNReal t)) :=
            integrable_monicHermite_gaussianReal (countOnes hd p.2) ht
          have hHE := hH.mul_bdd
            (by fun_prop : Continuous _).aestronglyMeasurable
            (ae_of_all _ fun x => le_of_eq (norm_exp_real_tilt ξ t x))
          have hc := hHE.const_mul ((p.1 : ℂ) *
              ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ))
          convert hc using 1
          funext x
          simp [hermitePoly, mul_assoc, mul_left_comm, mul_comm]
        · simpa using integrable_zero _ _ _
      refine ⟨hp_int.add ih.1, ?_⟩
      rw [integral_add hp_int ih.1, ih.2]
      congr 1
      split_ifs with h01
      · have heq : (fun a : ℝ =>
            (p.1 : ℂ) * ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) *
              hermitePoly (countOnes hd p.2) t a *
              Complex.exp (Complex.I * (ξ : ℂ) * (a : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))) =
          (fun a : ℝ => ((p.1 : ℂ) *
              ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ)) *
            (hermitePoly (countOnes hd p.2) t a *
              Complex.exp (Complex.I * (ξ : ℂ) * (a : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)))) := by
          funext a; ring
        rw [heq, integral_const_mul, integral_monicHermite_mul_complexTilt _ ht ξ]
        have hle := countOnes_le_length hd p.2
        have hpow : (t : ℂ) ^ (p.2.length - countOnes hd p.2) * (t : ℂ) ^ countOnes hd p.2 =
            (t : ℂ) ^ p.2.length := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        have hdiv : ((t ^ p.2.length / (p.2.length.factorial : ℝ) : ℝ) : ℂ) =
            (t : ℂ) ^ p.2.length / (p.2.length.factorial : ℂ) := by
          rw [Complex.ofReal_div, Complex.ofReal_pow]
          norm_cast
        have hdiv0 : ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) =
            (t : ℂ) ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℂ) := by
          rw [Complex.ofReal_div, Complex.ofReal_pow]
          norm_cast
        rw [hdiv0]
        calc (p.1 : ℂ) * ((t : ℂ) ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℂ)) *
              ((Complex.I * (ξ : ℂ) * (t : ℂ)) ^ countOnes hd p.2)
            = (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ countOnes hd p.2 *
                (((t : ℂ) ^ (p.2.length - countOnes hd p.2) * (t : ℂ) ^ countOnes hd p.2) /
                  (p.2.length.factorial : ℂ)) := by rw [mul_pow]; ring
          _ = (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ countOnes hd p.2 *
                ((t : ℂ) ^ p.2.length / (p.2.length.factorial : ℂ)) := by
              rw [hpow]
          _ = (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ countOnes hd p.2 *
                ((t ^ p.2.length / (p.2.length.factorial : ℝ) : ℝ) : ℂ) := by
              rw [← hdiv]
      · simp
  have hRHS : ∫ ω, condSigPoly hd t I (MultiBrownian.W B t ω ⟨0, hd⟩) *
        complexTilt B hd ξ t ω ∂P =
      ((contractions I.reverse).map fun p =>
        if onlyZeroOrOne hd p.2 then
          (p.1 : ℂ) * (Complex.I * (ξ : ℂ)) ^ (countOnes hd p.2) *
            ((t ^ p.2.length / (p.2.length.factorial : ℝ) : ℝ) : ℂ)
        else 0).sum := by
    have hcomp := hlaw.integral_comp
      (f := fun x : ℝ => condSigPoly hd t I (x : ℂ) *
        Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)))
      (((differentiable_condSigPoly hd t I).continuous.comp Complex.continuous_ofReal).mul
        (by fun_prop : Continuous _)).aestronglyMeasurable
    simp only [Function.comp_def, complexTilt] at hcomp ⊢
    rw [hcomp]
    simpa [condSigPoly] using (hRHS_list (contractions I.reverse)).2
  rw [hLHS, hRHS]

end SignatureVolatility
